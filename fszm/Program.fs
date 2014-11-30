#light "off"

open System
open System.IO
open System.Collections.Generic

type shift = ShiftZero | ShiftOne | ShiftTwo
type zstring = { s:string; length:int; shift:shift }
let emptyString = { s=""; length=0; shift=ShiftZero }

type operand = Large of uint16 | Small of byte | Variable of byte | Omitted
type encoding = Op0 | Op1 | Op2 | Var
type instruction = { opcode:int; optype:encoding; length:int; args:operand array; ret:operand; string:string; offset:int }
let emptyInstruction = {opcode=0; optype=Op0; length=0; args=[||]; ret=Omitted; string=""; offset=0 }

type Story(filename) = class
	let mem = File.ReadAllBytes(filename)
	let _read8 off = mem.[off]
	let _read16 off = (mem.[off] |> uint16 <<< 8) ||| (mem.[off+1] |> uint16)
	let _write16 v offset  =
		mem.SetValue(uint8 (v >>> 8), int offset);
		mem.SetValue(uint8 (v &&& 0xffus), (int offset)+1)
	let _write8 v offset =
		mem.SetValue(uint8 (v &&& 0xff), int offset)

	// zstring decoding w/ abbrev support.
	let unpackTriplet x = [(x >>> 10) &&& 0x1fus |> byte; (x >>> 5) &&& 0x1fus |> byte; (x >>> 0) &&& 0x1fus |> byte]

	let rec readString_r off (str:zstring) l =
		let x = off + str.length |> _read16 in
		if x &&& 0x8000us <> 0us then (str, l @ (unpackTriplet x)) else
		l @ (unpackTriplet x) |> readString_r off { str with length=str.length+2 }

	let rec pumpString str = function
		| 0uy :: tail -> pumpString { str with s=str.s+" " } tail
		| a :: x :: tail when a > 0uy && a < 4uy ->
			let table = _read16 0x18 |> int in
			let index = 32 * ((int a) - 1) + (int x) in
			let offset = ((table + index * 2) |> _read16 |> int) * 2 in
			let _, l = readString_r offset emptyString [] in
			pumpString str (l @ tail)
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

	let stack = Stack<uint16>()
	let routine_stack = Stack<int * int * int * byte * int>()

	let _addr x = dynamic_start + (x |> int)
	let _paddr x = dynamic_start + (x * 2us |> int)
	let _readGlobal x = globals + (x - 0x10uy |> uint16 |> _paddr) |> _read16
	let _writeGlobal v x = globals + (x - 0x10uy |> uint16 |> _paddr) |> _write16 v

	let _readLocal x = let addr, stack_start, numlocals, return_storage, return_addr = routine_stack.Peek() in
		let s, i = stack.ToArray(), stack_start + (x |> int) - 1 in s.[i]
	let _writeLocal v x = let addr, stack_start, numlocals, return_storage, return_addr = routine_stack.Peek() in
		let s, i = stack.ToArray(), stack_start + (x |> int) - 1 in s.SetValue(v, x |> int)

	let _readVariable = function
		| x when x >= 0x10uy -> _readGlobal x
		| x when x = 0uy -> stack.Pop()
		| x -> _readLocal x

	let _writeVariable v = function
		| x when x >= 0x10uy -> _writeGlobal v x
		| x when x = 0uy -> stack.Push(v)
		| x -> _writeLocal v x

	member this.read8 = _read8
	member this.read16 = _read16
	member this.readString = _readString
	member this.readVariable = _readVariable
	member this.writeVariable = _writeVariable

	member this.vin = function
		| Variable(x) -> _readVariable x
		| Large(x) -> x
		| Small(x) -> x |> uint16
		| Omitted -> failwith "omitted args have no value"

	member this.vout var value = _writeVariable value (match var with Variable(x) -> x | _ -> failwith ("bad return"))
end

type Machine(filename) = class
	let s = Story(filename)
	let mutable ip = s.read16 0x6 |> int
	let mutable finished = false

	let mutable _in = fun _ -> Console.ReadLine()
	let mutable _out = fun (x:string) -> printf "%s" x

	let names0op = [| "rtrue"; "rfalse"; "print"; "print_ret"; "no"; "save"; "restore"; "restart"; "ret_popped"; "pop"; "quit"; "new_line"; "show_status"; "verify"; "extended"; "piracy" |]
	let names1op = [| "jz"; "get_sibling"; "get_child"; "get_parent"; "get_prop_len"; "inc"; "dec"; "print_addr"; "call_1s"; "remove_obj"; "print_obj"; "ret"; "jump"; "print_paddr"; "load"; "not"; "call_1n" |]
	let names2op = [| "none"; "je"; "jl"; "jg"; "dec_chk"; "inc_chk"; "jin"; "test"; "or"; "and"; "test_attr"; "set_attr"; "clear_attr"; "store"; "insert_obj"; "loadw"; "loadb"; "get_prop"; "get_prop_addr"; "get_next_prop"; "add"; "sub"; "mul"; "div"; "mod"; "call_2s"; "call_2n"; "set_colour"; "throw" |]
	let namesvar = [| "call"; "storew"; "storeb"; "put_prop"; "sread"; "print_char"; "print_num"; "random"; "push"; "pull"; "split_window"; "set_window"; "call_vs2"; "erase_window"; "erase_line"; "set_cursor"; "get_cursor"; "set_text_style"; "buffer_mode"; "output_stream"; "input_stream"; "sound_effect"; "read_char"; "scan_table"; "not_v4"; "call_vn"; "call_vn2"; "tokenise"; "encode_text"; "copy_table"; "print_table"; "check_arg_count" |]

	let nul2op = fun (op:instruction) x y ret -> failwith <| sprintf "Unimplemented 2op instruction %s" names2op.[op.opcode]
	let instructions2op = [|
	(* none *) nul2op;
	(* je *) nul2op;
	(* jl *) nul2op;
	(* jg *) nul2op;
	(* dec_chk *) nul2op;
	(* inc_chk *) nul2op;
	(* jin *) nul2op;
	(* test *) nul2op;
	(* or *) nul2op;
	(* and *) (fun _ x y ret -> (x |> s.vin) &&& (y |> s.vin) |> s.vout ret);
	(* test_attr *) nul2op;
	(* set_attr *) nul2op;
	(* clear_attr *) nul2op;
	(* store *) nul2op;
	(* insert_obj *) nul2op;
	(* loadw *) nul2op;
	(* loadb *) nul2op;
	(* get_prop *) nul2op;
	(* get_prop_addr *) nul2op;
	(* get_next_prop *) nul2op;
	(* add *) (fun _ x y ret -> (x |> s.vin |> int16) + (y |> s.vin |> int16) |> uint16 |> s.vout ret);
	(* sub *) (fun _ x y ret -> (x |> s.vin |> int16) - (y |> s.vin |> int16) |> uint16 |> s.vout ret);
	(* mul *) (fun _ x y ret -> (x |> s.vin |> int16) * (y |> s.vin |> int16) |> uint16 |> s.vout ret);
	(* div *) (fun _ x y ret -> (x |> s.vin |> int16) / (y |> s.vin |> int16) |> uint16 |> s.vout ret);
	(* mod *) nul2op;
	(* call_2s *) nul2op;
	(* call_2n *) nul2op;
	(* set_colour *) nul2op;
	(* throw *) nul2op;
	|]

	let nul1op = fun (op:instruction) x ret -> failwith <| sprintf "Unimplemented 1op instruction %s" names1op.[op.opcode]
	let instructions1op = [|
	(* jz *) nul1op;
	(* get_sibling *) nul1op;
	(* get_child *) nul1op;
	(* get_parent *) nul1op;
	(* get_prop_len *) nul1op;
	(* inc *) nul1op;
	(* dec *) nul1op;
	(* print_addr *) nul1op;
	(* call_1s *) nul1op;
	(* remove_obj *) nul1op;
	(* print_obj *) nul1op;
	(* ret *) nul1op;
	(* jump *) nul1op;
	(* print_paddr *) nul1op;
	(* load *) nul1op;
	(* not *) nul1op;
	(* call_1n *) nul1op;
	|]

	let nul0op = fun (op:instruction) ret -> failwith <| sprintf "Unimplmented 0op instruction %s" names0op.[op.opcode]
	let instructions0op = [|
	(* rtrue *) nul0op;
	(* rfalse *) nul0op;
	(* print *) nul0op;
	(* print_ret *) nul0op;
	(* no *) nul0op;
	(* save *) nul0op;
	(* restore *) nul0op;
	(* restart *) nul0op;
	(* ret_popped *) nul0op;
	(* pop *) nul0op;
	(* quit *) nul0op;
	(* new_line *) nul0op;
	(* show_status *) nul0op;
	(* verify *) nul0op;
	(* extended *) nul0op;
	(* piracy *) nul0op;
	|]

	let nulvar = fun (op:instruction) args ret -> failwith <| sprintf "Unimplemented var instruction %s" namesvar.[op.opcode]
	let instructionsvar =[|
	(* call*) nulvar;
	(* storew*) nulvar;
	(* storeb*) nulvar;
	(* put_prop*) nulvar;
	(* sread*) nulvar;
	(* print_char*) nulvar;
	(* print_num*) nulvar;
	(* random*) nulvar;
	(* push*) nulvar;
	(* pull*) nulvar;
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
		{ emptyInstruction with	opcode=(op&&&0x1fuy)|>int; optype=Op2; length=3;	args=
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
		| Op2 -> (opcode >= 0x08 && opcode <= 0x09) || (opcode >= 0x09 && opcode <= 0x19)
		| Op1 -> (opcode >= 0x01 && opcode <= 0x04) || opcode = 0x08 || (opcode >= 0x0e && opcode <= 0x0f)
		| Var -> opcode = 0x0
		| _ -> false

	let branches opcode = function
		| _ -> false

	let prints opcode = function
		| Op0 -> (opcode = 0x02) || (opcode = 0x03)
		| _ -> false

	let add_return i = if stores i.opcode i.optype then
		{ i with length=i.length+1; ret=Variable(ip + i.length |> s.read8) } else i

	let add_branch i = if branches i.opcode i.optype then
		i else i

	let add_print i = if prints i.opcode i.optype then
		let str = ip + i.length |> s.readString in
		{ i with length=i.length+str.length; string=str.s } else i

	let decode =
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

	let disassemble i =	let names = match i.optype with
		| Op0 -> names0op
		| Op1 -> names1op
		| Op2 -> names2op
		| Var -> namesvar in
		printfn "%s" (print (names.[i.opcode].ToUpper() + "\t") i.ret (i.args |> Array.toList)); i

	let execute i =
		let oldip = ref ip in
		match i.optype with
		| Op0 -> instructions0op.[i.opcode] i i.ret
		| Op1 -> instructions1op.[i.opcode] i i.args.[0] i.ret
		| Op2 -> instructions2op.[i.opcode] i i.args.[0] i.args.[1] i.ret
		| Var -> instructionsvar.[i.opcode] i i.args i.ret;
		ip <- if ip = !oldip then ip + i.length else ip

	member this.Run = while finished <> true do
		decode
		|> disassemble
		|> execute
		done
end

type ZStory(filename) = class
	let bytes = File.ReadAllBytes(filename)
	let stack = Stack<uint16>()
	let routine_stack = Stack<int * int * int * byte * int>()

	let readWord offset = ((uint16 bytes.[offset]) <<< 8) ||| (uint16 bytes.[offset+1])
	let readByte offset = bytes.[offset]
	let writeWord offset word =
		bytes.SetValue(uint8 (word >>> 8), int offset);
		bytes.SetValue(uint8 (word &&& 0xffus), (int offset)+1)
	let writeByte offset byte =
		bytes.SetValue(uint8 (byte &&& 0xff), int offset)

	let version = readByte 0
	let dynamic_start = 0
	let dynamic_end = readWord 0xe |> int
	let static_start = dynamic_end
	let static_end = static_start + (min bytes.Length 0xffff)
	let high_start = readWord 0x4 |> int
	let high_end = bytes.Length
	let globals = readWord 0xc |> int
	let mutable ip = dynamic_start + ((readWord 0x6) |> int)

	member this.Bytes = bytes
	member this.Version = version
	member this.IP with get() = ip and set value = ip <- value
	member this.ReadWord = readWord
	member this.ReadByte = readByte
	member this.WriteWord = writeWord
	member this.WriteByte = writeByte
	member this.Address addr = dynamic_start + (addr |> int)
	member this.PackedAddress addr = dynamic_start + (addr * 2us |> int)
	member this.ReadGlobal x = readWord (globals + (this.PackedAddress (x - 0x10uy |> uint16)))
	member this.WriteGlobal x v = writeWord (globals + (this.PackedAddress (x - 0x10uy |> uint16))) v

	member this.ReadLocal x = let addr, stack_start, numlocals, return_storage, return_addr = routine_stack.Peek() in
		let s, i = stack.ToArray(), stack_start + (x |> int) - 1 in s.[i]
	member this.WriteLocal x v = let addr, stack_start, numlocals, return_storage, return_addr = routine_stack.Peek() in
		let s, i = stack.ToArray(), stack_start + (x |> int) - 1 in s.SetValue(v, x |> int)

	member this.Call call_addr (args : uint16 list) ret_addr ret_data =
		if call_addr = 0 then (this.WriteVariable 0us ret_data; ret_addr) else
		let args_start = stack.Count in
		let numlocals = readByte call_addr |> int in
		routine_stack.Push(call_addr, args_start, numlocals, ret_data, ret_addr);
		for i in 0 .. numlocals do
			stack.Push(
				if i < args.Length then args.[i] else readWord (call_addr + 1 + i * 2)
			)
		done;
		call_addr + 1 + numlocals * 2

	member this.ReadVariable = function
	| x when x >= 0x10uy -> this.ReadGlobal x
	| x when x = 0uy -> stack.Pop()
	| x -> this.ReadLocal x

	member this.WriteVariable v = function
	| x when x >= 0x10uy -> this.WriteGlobal x v
	| x when x = 0uy -> stack.Push(v)
	| x -> this.WriteLocal x v

	member this.Pop = stack.Pop()
	member this.Push x = stack.Push(x)
end

do
	Machine("zork.z3").Run;
	Console.ReadKey(true) |> ignore
