#light "off"

open System
open System.IO
open System.Collections.Generic

type shift = ShiftZero | ShiftOne | ShiftTwo
type zstring = { s:string; length:int; shift:shift }
let emptyString = { s=""; length=0; shift=ShiftZero }

type zobject = { num:int; attrib:uint32; parent:int; sibling:int; child:int; addr:int; name:zstring }
let defaultObject = {num=0; attrib=0u; parent=0; sibling=0; child=0; addr=0; name=emptyString }

type zproperty = { num:int; len:int; addr:int }
let defaultProperty = { num=0; len=0; addr=0 }

type operand = Large of uint16 | Small of byte | Variable of byte | Omitted
type encoding = Op0 | Op1 | Op2 | Var
type instruction = { opcode:int; optype:encoding; length:int; args:operand array; ret:operand; string:string; offset:int; compare:bool }
let emptyInstruction = {opcode=0; optype=Op0; length=0; args=[||]; ret=Omitted; string=""; offset=0; compare=false }

let debugPrint x = printfn "%A" x; x

let inline (|>>) a b = b a |> ignore; a

type Story(filename) = class
	let mem = File.ReadAllBytes(filename)
	let _read8 off = mem.[off]
	let _read16 off = (mem.[off] |> uint16 <<< 8) ||| (mem.[off+1] |> uint16)
	let _write16 v offset =
		mem.SetValue(uint8 (v >>> 8), int offset);
		mem.SetValue(uint8 (v &&& 0xffus), (int offset)+1)
	let _write8 v offset =
		mem.SetValue(uint8 (v &&& 0xffus), int offset)

	// zstring decoding w/ abbrev support.
	let unpackTriplet x = [(x >>> 10) &&& 0x1fus |> byte; (x >>> 5) &&& 0x1fus |> byte; (x >>> 0) &&& 0x1fus |> byte]

	let rec readString_r off (str:zstring) l =
		let x = off + str.length |> _read16 in
		if x &&& 0x8000us <> 0us then ({ str with length=str.length+2}, l @ (unpackTriplet x)) else
		l @ (unpackTriplet x) |> readString_r off { str with length=str.length+2 }

	let rec pumpString str = function
		| 0uy :: tail -> pumpString { str with s=str.s+" " } tail
		| a :: x :: tail when a > 0uy && a < 4uy ->
			let table = _read16 0x18 |> int in
			let index = 32 * ((int a) - 1) + (int x) in
			let offset = ((table + index * 2) |> _read16 |> int) * 2 in
			let _, l = readString_r offset emptyString [] in
			let abbrev = pumpString emptyString l in
			pumpString {str with s=str.s+abbrev.s} tail
		| 4uy :: tail -> pumpString { str with shift=ShiftOne } tail
		| 5uy :: tail -> pumpString { str with shift=ShiftTwo } tail
		| 6uy :: hi :: lo :: tail when str.shift=ShiftTwo ->
			let c = hi <<< 5 ||| lo |> int in
			pumpString { str with s=str.s+Char.ConvertFromUtf32(c).ToString() } tail
		| a :: tail when a > 5uy && a < 32uy -> let c = (match str.shift with
			| ShiftZero -> "______abcdefghijklmnopqrstuvwxyz"
			| ShiftOne -> "______ABCDEFGHIJKLMNOPQRSTUVWXYZ"
			| ShiftTwo -> "______^\n0123456789.,!?_#\'\"/\\-:()") |> Seq.nth (int a) in
			pumpString { str with s=str.s+c.ToString(); shift=ShiftZero } tail
		| [] -> str
		| _ -> failwith "Bad zstring"

	let _readString off = let str, l = readString_r off emptyString [] in pumpString str l

	let dynamic_start = 0
	let dynamic_end = _read16 0xe |> int
	let static_start = dynamic_end
	let static_end = static_start + (min mem.Length 0xffff)
	let high_start = _read16 0x4 |> int
	let high_end = mem.Length
	let globals = _read16 0xc |> int

	let mutable (stack:uint16 array) = [| |]
	let routine_stack = Stack<int * int * int * operand * int>()
	let _push x = stack <- Array.append stack [| x |]
	let _pop () = let x = stack.[stack.Length-1] in stack <- stack.[0..stack.Length-2]; x

	let _addr x = dynamic_start + (x |> int)
	let _paddr x = dynamic_start + (x * 2us |> int)
	let _readGlobal x = globals + (x - 0x10uy |> uint16 |> _paddr) |> _read16
	let _writeGlobal v x = globals + (x - 0x10uy |> uint16 |> _paddr) |> _write16 v

	let _readLocal x = let addr, stack_start, numlocals, return_storage, return_addr = routine_stack.Peek() in
		let i = stack_start + (x |> int) - 1 in stack.[i] 
	let _writeLocal v x = let addr, stack_start, numlocals, return_storage, return_addr = routine_stack.Peek() in
		let i = stack_start + (x |> int) - 1 in stack.SetValue(v,i)

	let _readVariable = function
		| x when x >= 0x10uy -> _readGlobal x
		| x when x = 0uy -> _pop ()
		| x -> _readLocal x

	let _writeVariable v = function
		| x when x >= 0x10uy -> _writeGlobal v x
		| x when x = 0uy -> _push v
		| x -> _writeLocal v x

	let _readObj index =
		if index = 0 then failwith "Cannot read object 0" else
			let addr = (_read16 0xa |> int) + 31 * 2 + (index - 1) * 9 in
			let prop_addr = addr + 7 |> _read16 |> int in
			{ defaultObject with
			num=index;
			attrib=(addr+0 |> _read16 |> uint32) <<< 16 ||| (addr+2 |> _read16 |> uint32);
			parent = addr+4 |> _read8 |> int;
			sibling = addr+5 |> _read8 |> int;
			child = addr+6 |> _read8 |> int;
			addr = prop_addr;
			name = prop_addr + 1 |> _readString
			}

	let _writeObj (o : zobject) =
		// don't bother re-writing string, it can't change.
		let addr = (_read16 0xa |> int) + 31 * 2 + (o.num - 1) * 9 in
		addr + 0 |> _write16 ((o.attrib >>> 16) &&& 0xffffu |> uint16);
		addr + 2 |> _write16 (o.attrib &&& 0xffffu |> uint16);
		addr + 4 |> _write8 (o.parent |> uint16);
		addr + 5 |> _write8 (o.sibling |> uint16);
		addr + 6 |> _write8 (o.child |> uint16);
		addr + 7 |> _write16 (o.addr |> uint16)
		
	let _getProp x = let size = _read8 x |> int in
		if size = 0 then defaultProperty else
		{ defaultProperty with num=size&&&31; len=((size&&&0xe0)>>>5) + 1; addr=x }

	let _readProp (p : zproperty) = match p.len with
		| 1 -> p.addr + 1 |> _read8 |> uint16
		| 2 -> p.addr + 1 |> _read16
		| _ -> failwith "Undefined behavior, property length must be 1 or 2 in v3."

	let _writeProp x (p : zproperty) = match p.len with
		| 1 -> p.addr + 1 |> _write8 x
		| 2 -> p.addr + 1 |> _write16 x
		| _ -> failwith "Undefined behavior, property length must be 1 or 2 in v3."

	member this.read8 = _read8
	member this.read16 = _read16
	member this.write8 = _write8
	member this.write16 = _write16
	member this.readString = _readString
	member this.readVariable = _readVariable
	member this.writeVariable = _writeVariable
	member this.readObj = _readObj
	member this.writeObj = _writeObj
	member this.readProp = _readProp
	member this.writeProp = _writeProp
	member this.addr = _addr
	member this.paddr = _paddr

	member this.vin = function
		| Variable(x) -> _readVariable x
		| Large(x) -> x
		| Small(x) -> x |> uint16
		| Omitted -> failwith "Omitted args have no value"

	// some instructions pass in the variable number directly, these shouldn't go through readVariable
	member this.vin_direct = function
		| Large(x) -> x |> byte
		| Small(x) -> x
		| _ -> failwith "Bad direct argument"

	member this.vin_addr = this.vin >> _addr
	member this.vin_paddr = this.vin >> _paddr
	member this.vin_i16 = this.vin >> int16

	member this.vout var value = _writeVariable value (match var with Variable(x) -> x | _ -> failwith ("bad return"))

	member this.call addr retaddr retdata (args:uint16 array) =
		if addr - dynamic_start = 0 then (this.vout retdata 0us; retaddr) else
		let args_start = stack.Length in
		let numlocals = _read8 addr |> int in
		routine_stack.Push(addr, args_start, numlocals, retdata, retaddr);
		for i in 0 .. (numlocals-1) do
			_push (if i < args.Length then args.[i] else _read16 (addr + 1 + i * 2))
		done;
		addr + 1 + numlocals * 2

	member this.ret retval =
		let addr, args_start, numlocals, retdata, retaddr = routine_stack.Pop() in
		while stack.Length <> args_start do _pop () |> ignore done;
		this.vout retdata retval;
		retaddr

	member this.removeObj (obj : zobject) =
		if obj.parent = 0 then obj else
		let parent = obj.parent |> _readObj in
		if parent.child = obj.num then { parent with child = obj.sibling } |> _writeObj	else
		(let rec getSibling i = let o = i |> _readObj in if i = obj.num then o else getSibling o.sibling in
		let child = parent.child |> getSibling in
		{ child with sibling=obj.sibling } |> _writeObj);
		{ obj with parent=0; sibling=0 } |>> _writeObj

	member this.insertObj (obj : zobject) (dest : zobject) =
		{ (obj |> this.removeObj) with sibling=dest.child; parent=dest.num } |> _writeObj;
		{ dest with child=obj.num } |> _writeObj

	member this.getProp (index : int) (obj : zobject) =
		// Pass -1 to get the first property
		let rec iterProperties addr =
			let p = _getProp addr in
			match p.num, p.len with
			| 0, 0 -> (* default *) { ((0xa |> _read16 |> _addr) + (index - 1) - 1 |> _getProp) with num=index;len=2 }
			| i, _ when i = index -> p
			| _, l -> addr + 1 + l |> iterProperties in
		let addr = obj.addr + 1 + obj.name.length in
		iterProperties addr

	member this.parseInput max_parse (input : string) =
		()
end

type Machine(filename) = class
	let s = Story(filename)
	let mutable ip = s.read16 0x6 |> int
	let mutable finished = false

	let mutable outbuf = ""
	let mutable _in = fun _ -> Console.ReadLine()
	let mutable _out = fun (x:string) -> outbuf <- outbuf + x
	let mutable _flush = fun _ -> printf "%s" outbuf; outbuf <- ""

	let jump (i:instruction) x =
		if x = i.compare then ip <- (match i.offset with
		| 0 -> s.ret 0us
		| 1 -> s.ret 1us
		| x -> ip + i.length + i.offset - 2)
		else ()

	let names0op = [| "rtrue"; "rfalse"; "print"; "print_ret"; "no"; "save"; "restore"; "restart"; "ret_popped"; "pop"; "quit"; "new_line"; "show_status"; "verify"; "extended"; "piracy" |]
	let names1op = [| "jz"; "get_sibling"; "get_child"; "get_parent"; "get_prop_len"; "inc"; "dec"; "print_addr"; "call_1s"; "remove_obj"; "print_obj"; "ret"; "jump"; "print_paddr"; "load"; "not"; "call_1n" |]
	let names2op = [| "none"; "je"; "jl"; "jg"; "dec_chk"; "inc_chk"; "jin"; "test"; "or"; "and"; "test_attr"; "set_attr"; "clear_attr"; "store"; "insert_obj"; "loadw"; "loadb"; "get_prop"; "get_prop_addr"; "get_next_prop"; "add"; "sub"; "mul"; "div"; "mod"; "call_2s"; "call_2n"; "set_colour"; "throw" |]
	let namesvar = [| "call"; "storew"; "storeb"; "put_prop"; "sread"; "print_char"; "print_num"; "random"; "push"; "pull"; "split_window"; "set_window"; "call_vs2"; "erase_window"; "erase_line"; "set_cursor"; "get_cursor"; "set_text_style"; "buffer_mode"; "output_stream"; "input_stream"; "sound_effect"; "read_char"; "scan_table"; "not_v4"; "call_vn"; "call_vn2"; "tokenise"; "encode_text"; "copy_table"; "print_table"; "check_arg_count" |]

	let attr_bit x = 1u <<< (31 - (x |> s.vin |>int))
	let nul2op = fun (op:instruction) x y ret -> _flush (); failwith <| sprintf "Unimplemented 2op instruction %s" names2op.[op.opcode]
	let instructions2op = [|
	(* none *) nul2op;
	(* je *) (fun i x y ret -> (x |> s.vin) = (y |> s.vin) |> jump i);
	(* jl *) (fun i x y _ -> (x |> s.vin_i16) < (y |> s.vin_i16) |> jump i);
	(* jg *) nul2op;
	(* dec_chk *) (fun i x y ret -> let var = x |> s.vin_direct in let old = var |> s.readVariable |> int16 in
		var |> s.writeVariable (old - 1s |> uint16); old - 1s < (y |> s.vin_i16) |> jump i);
	(* inc_chk *) (fun i x y ret -> let var = x |> s.vin_direct in let old = var |> s.readVariable |> int16 in
		var |> s.writeVariable (old + 1s |> uint16); old + 1s > (y |> s.vin_i16) |> jump i);
	(* jin *) (fun i x y _ -> let o = x |> s.vin_addr |> s.readObj in o.parent = (y |> s.vin |> int) |> jump i);
	(* test *) nul2op;
	(* or *) nul2op;
	(* and *) (fun _ x y ret -> (x |> s.vin) &&& (y |> s.vin) |> s.vout ret);
	(* test_attr *) (fun i x y ret -> let o = x |> s.vin_addr |> s.readObj in (o.attrib &&& (attr_bit y)) <> 0u |> jump i);
	(* set_attr *) (fun _ x y _ -> let o = x |> s.vin_addr |> s.readObj in { o with attrib=o.attrib ||| (attr_bit y) } |> s.writeObj);
	(* clear_attr *) nul2op;
	(* store *) (fun _ x y _ -> (x |> s.vin_direct) |> s.writeVariable (y |> s.vin));
	(* insert_obj *) (fun _ x y _ -> (x |> s.vin |> int |> s.readObj, y |> s.vin |> int |> s.readObj) ||> s.insertObj);
	(* loadw *) (fun _ x y ret -> (x |> s.vin) + 2us * (y |> s.vin) |> s.addr |> s.read16 |> s.vout ret);
	(* loadb *) (fun _ x y ret -> (x |> s.vin) + (y |> s.vin) |> s.addr |> s.read8 |> uint16 |> s.vout ret);
	(* get_prop *) (fun _ x y ret -> x |> s.vin_addr |> s.readObj |> s.getProp (y |> s.vin |> int) |> s.readProp |> s.vout ret);
	(* get_prop_addr *) nul2op;
	(* get_next_prop *) nul2op;
	(* add *) (fun _ x y ret -> (x |> s.vin_i16) + (y |> s.vin_i16) |> uint16 |> s.vout ret);
	(* sub *) (fun _ x y ret -> (x |> s.vin_i16) - (y |> s.vin_i16) |> uint16 |> s.vout ret);
	(* mul *) (fun _ x y ret -> (x |> s.vin_i16) * (y |> s.vin_i16) |> uint16 |> s.vout ret);
	(* div *) (fun _ x y ret -> (x |> s.vin_i16) / (y |> s.vin_i16) |> uint16 |> s.vout ret);
	(* mod *) nul2op;
	(* call_2s *) nul2op;
	(* call_2n *) nul2op;
	(* set_colour *) nul2op;
	(* throw *) nul2op;
	|]

	let nul1op = fun (op:instruction) x ret -> _flush (); failwith <| sprintf "Unimplemented 1op instruction %s" names1op.[op.opcode]
	let instructions1op = [|
	(* jz *) (fun i x ret -> (x |> s.vin) = 0us |> jump i);
	(* get_sibling *) (fun i x ret -> let o = x |> s.vin_addr |> s.readObj in (o.sibling |> uint16 |>> s.vout ret) <> 0us |> jump i);
	(* get_child *) (fun i x ret -> let o = x |> s.vin_addr |> s.readObj in (o.child |> uint16 |>> s.vout ret) <> 0us |> jump i);
	(* get_parent *) (fun _ x ret -> let o = x |> s.vin_addr |> s.readObj in o.parent |> uint16 |> s.vout ret);
	(* get_prop_len *) nul1op;
	(* inc *) (fun i x ret -> let var = x |> s.vin_direct in (((var |> s.readVariable |> int16) + 1s) |> uint16, var) ||> s.writeVariable);
	(* dec *) nul1op;
	(* print_addr *) nul1op;
	(* call_1s *) nul1op;
	(* remove_obj *) nul1op;
	(* print_obj *) (fun _ x _ -> let o = x |> s.vin_addr |> s.readObj in o.name.s |> _out);
	(* ret *) (fun i x ret -> ip <- x |> s.vin |> s.ret);
	(* jump *) (fun i x ret -> ip <- ip + i.length + (x |> s.vin_i16 |> int) - 2);
	(* print_paddr *) nul1op;
	(* load *) nul1op;
	(* not *) nul1op;
	(* call_1n *) nul1op;
	|]

	let nul0op = fun (op:instruction) ret -> _flush (); failwith <| sprintf "Unimplmented 0op instruction %s" names0op.[op.opcode]
	let instructions0op = [|
	(* rtrue *) (fun _ _ -> ip <- s.ret 1us);
	(* rfalse *) (fun _ _ -> ip <- s.ret 0us);
	(* print *) (fun i _ -> i.string |> _out);
	(* print_ret *) nul0op;
	(* no *) nul0op;
	(* save *) nul0op;
	(* restore *) nul0op;
	(* restart *) nul0op;
	(* ret_popped *) (fun i _ -> ip <- s.readVariable 0uy |> s.ret);
	(* pop *) nul0op;
	(* quit *) nul0op;
	(* new_line *) (fun _ _ -> "\n" |> _out);
	(* show_status *) nul0op;
	(* verify *) nul0op;
	(* extended *) nul0op;
	(* piracy *) nul0op;
	|]

	let trim_string len (str:string) = str.Substring(0, (str.Length, len) ||> min)
	let nulvar = fun (op:instruction) ret -> _flush (); failwith <| sprintf "Unimplemented var instruction %s" namesvar.[op.opcode]
	let instructionsvar =[|
	(* call*) (fun i ret -> ip <- s.call(i.args.[0] |> s.vin |> s.paddr) (ip + i.length) ret
		(seq { for x in i.args.[1..] do yield x |> s.vin done } |> Seq.toArray));
	(* storew*) (fun i ret -> (i.args.[0] |> s.vin) + 2us * (i.args.[1] |> s.vin) |> s.paddr |> s.write16 (i.args.[2] |> s.vin));
	(* storeb*) nulvar;
	(* put_prop*) (fun i _ -> i.args.[0] |> s.vin_addr |> s.readObj |> s.getProp (i.args.[1] |> s.vin_addr) |> s.writeProp (i.args.[2] |> s.vin));
	(* sread*) (fun i _ -> _flush (); let str = _in () in str.ToLower() |> trim_string (i.args.[0] |> s.vin |> int) |> s.parseInput (i.args.[1] |> s.vin));
	(* print_char*) (fun i _ -> i.args.[0] |> s.vin |> char |> sprintf "%c" |> _out);
	(* print_num*) (fun i _ -> i.args.[0] |> s.vin |> sprintf "%d" |> _out);
	(* random*) nulvar;
	(* push*) (fun i _ -> s.writeVariable (i.args.[0] |> s.vin) 0uy);
	(* pull*) (fun i _ -> i.args.[0] |> s.vin_direct |> byte |> s.writeVariable (s.readVariable 0uy));
	(* split_window*) nulvar;
	(* set_window*) nulvar;
	(* call_vs2*) nulvar;
	(* erase_window*) nulvar;
	(* erase_line*) nulvar;
	(* set_cursor*) nulvar;
	(* get_cursor*) nulvar;
	(* set_text_style*) nulvar;
	(* buffer_mode*) nulvar;
	(* output_stream*) nulvar;
	(* input_stream*) nulvar;
	(* sound_effect*) nulvar;
	(* read_char*) nulvar;
	(* scan_table*) nulvar;
	(* not_v4*) nulvar;
	(* call_vn*) nulvar;
	(* call_vn2*) nulvar;
	(* tokenise*) nulvar;
	(* encode_text*) nulvar;
	(* copy_table*) nulvar;
	(* print_table*) nulvar;
	(* check_arg_count*) nulvar;
	|]

	let decode_short op =
		let optype, length, args = match op &&& 0x30uy >>> 4 with
		| 3uy -> Op0, 1, [||]
		| 2uy -> Op1, 2, [| Variable(ip + 1 |> s.read8) |]
		| 1uy -> Op1, 2, [| Small(ip + 1 |> s.read8) |]
		| _ -> Op1, 3, [| Large(ip + 1 |> s.read16) |] in
		{ emptyInstruction with opcode=(op&&&0x0fuy)|>int; optype=optype; length=length; args=args }

	let decode_long op =
		let x = ip + 1 |> s.read8 in
		let y = ip + 2 |> s.read8 in
		{ emptyInstruction with	opcode=(op&&&0x1fuy)|>int; optype=Op2; length=3; args=
		[|
			(if op &&& 0x40uy <> 0uy then Variable(x) else Small(x));
			(if op &&& 0x20uy <> 0uy then Variable(y) else Small(y))
		|] }

	let decode_var op =
		let optypes = ip + 1 |> s.read8 in
		let size = ref 2 in
		let args = seq {
			for x in 0..3 do
				let shift = (3 - x) * 2 in
				let mask = 3 <<< shift |> byte in
				yield match (optypes &&& mask) >>> shift with
				| 0x3uy -> Omitted
				| 0x2uy -> size := !size + 1; Variable(ip + !size - 1 |> s.read8)
				| 0x1uy -> size := !size + 1; Small(ip + !size - 1 |> s.read8)
				| _-> size := !size + 2; Large(ip + !size - 2 |> s.read16)
			done
		} |> Seq.filter (fun x -> match x with | Omitted -> false | _ -> true) |> Seq.toArray in
		{ emptyInstruction with opcode=(op&&&0x1fuy)|>int;
			optype=if op &&& 0x20uy <> 0uy then Var else Op2;
			length=(!size); args=args }

	let stores opcode = function
		| Op2 -> (opcode >= 0x08 && opcode <= 0x09) || (opcode >= 0x0f && opcode <= 0x19)
		| Op1 -> (opcode >= 0x01 && opcode <= 0x04) || opcode = 0x08 || (opcode >= 0x0e && opcode <= 0x0f)
		| Var -> opcode = 0x0
		| _ -> false

	let branches opcode = function
		| Op2 -> (opcode >= 1 && opcode <= 7) || (opcode = 10)
		| Op1 -> (opcode >= 0 && opcode <= 2)
		| Op0 -> opcode = 5 || opcode = 6 || opcode = 0xd || opcode = 0xf
		| _ -> false

	let prints opcode = function
		| Op0 -> (opcode = 0x02) || (opcode = 0x03)
		| _ -> false

	let add_return i = if stores i.opcode i.optype then
		{ i with length=i.length+1; ret=Variable(ip + i.length |> s.read8) } else i

	let add_branch i = if branches i.opcode i.optype then
		let branch1 = ip + i.length |> s.read8 |> int in
		let offset = (0x80 &&& branch1) <<< 8 in
		let offset, len = if branch1 &&& 0x40 <> 0 then
			offset ||| (branch1 &&& 0x3f), 1 else
			offset ||| (branch1 &&& 0x1f <<< 8) ||| (ip + i.length + 1 |> s.read8 |> int), 2 in
		let offset, compare = offset &&& 0x7fff, offset &&& 0x8000 <> 0 in
		let offset = if offset > 0x0fff then -(0x1fff - offset + 1) else offset in
		{ i with offset=offset; length=i.length + len; compare=compare } else i

	let add_print i = if prints i.opcode i.optype then
		let str = ip + i.length |> s.readString in
		{ i with length=i.length+str.length; string=str.s } else i

	let decode ip =
		let op = s.read8 ip in
		(match (op &&& 0xc0uy) >>> 6 with
		| 0x03uy -> decode_var op
		| 0x02uy -> decode_short op
		| _ -> decode_long op)
		|> add_return
		|> add_branch
		|> add_print

	let string_from_operand = function
		| Large(x) -> sprintf "#%04x" x
		| Small(x) -> sprintf "#%02x" x
		| Variable(x) when x = 0uy -> "(SP)+"
		| Variable(x) when x >= 0x10uy -> sprintf "G%02x" (x - 0x10uy)
		| Variable(x) -> sprintf "L%02x" (x - 1uy)
		| Omitted -> ""

	let rec print str ret = function
		| h :: g :: t -> print (str + (string_from_operand h) + ",") ret (g :: t)
		| h :: t -> print (str + (string_from_operand h)) ret t
		| [] -> str + (match ret with
			| Variable(x) when x = 0uy -> " -> -(SP)"
			| Variable(x) when x >= 0x10uy -> sprintf " -> G%02x" (x - 0x10uy)
			| Variable(x) -> sprintf " -> L%02x" (x - 1uy)
			| _ -> "")

	let disassemble i = let names = match i.optype with
		| Op0 -> names0op
		| Op1 -> names1op
		| Op2 -> names2op
		| Var -> namesvar in
		printfn "[%08X] %s" ip (print (names.[i.opcode].ToUpper() + "\t") i.ret (i.args |> Array.toList)); i

	let execute i =
		let oldip = ip in
		(match i.optype with
		| Op0 -> instructions0op.[i.opcode] i i.ret
		| Op1 -> instructions1op.[i.opcode] i i.args.[0] i.ret
		| Op2 -> instructions2op.[i.opcode] i i.args.[0] i.args.[1] i.ret
		| Var -> instructionsvar.[i.opcode] i i.ret);
		if ip = oldip then ip + i.length else ip

	member this.Run () = while finished <> true do
		ip <- ip
		|> decode
		|> disassemble
		|> execute
		done
end

do
	Machine("zork.z3").Run ()
