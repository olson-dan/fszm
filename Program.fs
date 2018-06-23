open System
open System.IO
open System.Collections.Generic

type shift = ShiftZero | ShiftOne | ShiftTwo
type zstring = { s:string; length:int; offset:int}
let emptyString = { s=""; length=0; offset=0 }

type zobject = { num:uint16; attrib:uint32; parent:uint16; sibling:uint16; child:uint16; addr:int; name:zstring }
type zproperty = { num:int; len:int; addr:int }

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

    let rec readString_r (str:zstring) l =
        let x = str.offset + str.length |> _read16
        if x &&& 0x8000us <> 0us then ({ str with length=str.length+2}, l @ (unpackTriplet x)) else
        l @ (unpackTriplet x) |> readString_r { str with length=str.length+2 }

    let rec pumpString str shift = function
    | 0uy :: tail -> pumpString { str with s=str.s+" " } shift tail
    | a :: x :: tail when a > 0uy && a < 4uy ->
        let table = _read16 0x18 |> int
        let index = 32 * ((int a) - 1) + (int x)
        let offset = ((table + index * 2) |> _read16 |> int) * 2
        let _, l = readString_r { emptyString with offset=offset } []
        let abbrev = pumpString { emptyString with offset=offset } ShiftZero l
        pumpString {str with s=str.s+abbrev.s} shift tail
    | 4uy :: tail -> pumpString str ShiftOne tail
    | 5uy :: tail -> pumpString str ShiftTwo tail
    | 6uy :: hi :: lo :: tail when shift=ShiftTwo ->
        let c = hi <<< 5 ||| lo |> int
        pumpString { str with s=str.s+Char.ConvertFromUtf32(c).ToString() } ShiftZero tail
    | a :: tail when a > 5uy && a < 32uy ->
        let alphabet =
            match shift with
            | ShiftZero -> "______abcdefghijklmnopqrstuvwxyz"
            | ShiftOne -> "______ABCDEFGHIJKLMNOPQRSTUVWXYZ"
            | ShiftTwo -> "______^\n0123456789.,!?_#\'\"/\\-:()"
        let c = alphabet |> Seq.item (int a)
        pumpString { str with s=str.s+c.ToString() } ShiftZero tail
    | [] -> str
    | _ -> failwith "Bad zstring"

    let _readString off =
        let str, l = readString_r { emptyString with offset=off } []
        pumpString str ShiftZero l

    let dynamic_start = 0
    //let dynamic_end = _read16 0xe |> int
    //let static_start = dynamic_end
    //let static_end = static_start + (min mem.Length 0xffff)
    //let high_start = _read16 0x4 |> int
    //let high_end = mem.Length
    let globals = _read16 0xc |> int

    let mutable (stack:uint16 array) = [| |]
    let routine_stack = Stack<int * int * int * operand * int>()
    let _push x = stack <- Array.append stack [| x |]
    let _pop () =
        let x = stack.[stack.Length-1]
        stack <- stack.[0..stack.Length-2]
        x

    let _addr x = dynamic_start + (x |> int)
    let _paddr x = dynamic_start + (x * 2us |> int)
    let _readGlobal x = globals + (x - 0x10uy |> uint16 |> _paddr) |> _read16
    let _writeGlobal v x = globals + (x - 0x10uy |> uint16 |> _paddr) |> _write16 v

    let _readLocal x =
        let _addr, stack_start, _numlocals, _return_storage, _return_addr = routine_stack.Peek() in
        let i = stack_start + (x |> int) - 1
        stack.[i]
    let _writeLocal v x =
        let _addr, stack_start, _numlocals, _return_storage, _return_addr = routine_stack.Peek() in
        let i = stack_start + (x |> int) - 1
        stack.SetValue(v,i)

    let _readVariable = function
        | x when x >= 0x10uy -> _readGlobal x
        | x when x = 0uy -> _pop ()
        | x -> _readLocal x

    let _readVariableIndirect = function
        | x when x >= 0x10uy -> _readGlobal x
        | x when x = 0uy -> stack.[stack.Length-1]
        | x -> _readLocal x

    let _writeVariable v = function
        | x when x >= 0x10uy -> _writeGlobal v x
        | x when x = 0uy -> _push v
        | x -> _writeLocal v x

    let _writeVariableIndirect v = function
        | x when x >= 0x10uy -> _writeGlobal v x
        | x when x = 0uy ->
            _pop () |> ignore
            _push v
        | x -> _writeLocal v x

    let _readObj index =
        if index = 0us then failwith "Cannot read object 0" else
            let addr = (_read16 0xa |> int) + 31 * 2 + ((index |> int) - 1) * 9
            let prop_addr = addr + 7 |> _read16 |> int
            {
                num=index |> uint16;
                attrib=(addr+0 |> _read16 |> uint32) <<< 16 ||| (addr+2 |> _read16 |> uint32);
                parent = addr+4 |> _read8 |> uint16;
                sibling = addr+5 |> _read8 |> uint16;
                child = addr+6 |> _read8 |> uint16;
                addr = prop_addr;
                name = prop_addr + 1 |> _readString
            }

    let _writeObj (o : zobject) =
        // don't bother re-writing string, it can't change.
        let addr = (_read16 0xa |> int) + 31 * 2 + ((o.num |> int) - 1) * 9
        addr + 0 |> _write16 ((o.attrib >>> 16) &&& 0xffffu |> uint16)
        addr + 2 |> _write16 (o.attrib &&& 0xffffu |> uint16)
        addr + 4 |> _write8 o.parent
        addr + 5 |> _write8 o.sibling
        addr + 6 |> _write8 o.child
        addr + 7 |> _write16 (o.addr |> uint16)

    let _getProp x =
        let size = _read8 x |> int
        { num=size&&&31; len=((size&&&0xe0)>>>5) + 1; addr=x }

    let _readProp (p : zproperty) =
        match p.len with
        | 1 -> p.addr + 1 |> _read8 |> uint16
        | 2 -> p.addr + 1 |> _read16
        | _ -> failwith "Undefined behavior, property length must be 1 or 2 in v3."

    let _writeProp x (p : zproperty) =
        match p.len with
        | 1 -> p.addr + 1 |> _write8 x
        | 2 -> p.addr + 1 |> _write16 x
        | _ -> failwith "Undefined behavior, property length must be 1 or 2 in v3."

    member _this.read8 = _read8
    member _this.read16 = _read16
    member _this.write8 = _write8
    member _this.write16 = _write16
    member _this.readString = _readString
    member _this.readVariable = _readVariable
    member _this.readVariableIndirect = _readVariableIndirect
    member _this.writeVariable = _writeVariable
    member _this.writeVariableIndirect = _writeVariableIndirect
    member _this.readObj = _readObj
    member _this.writeObj = _writeObj
    member _this.readProp = _readProp
    member _this.readPropAtAddr = _getProp
    member _this.writeProp = _writeProp
    member _this.addr = _addr
    member _this.paddr = _paddr

    member _this.vin = function
        | Variable(x) -> _readVariable x
        | Large(x) -> x
        | Small(x) -> x |> uint16
        | Omitted -> failwith "Omitted args have no value"

    member this.vin_direct = this.vin >> byte
    member this.vin_paddr = this.vin >> _paddr
    member this.vin_i16 = this.vin >> int16

    member _this.vout var value =
        _writeVariable value (match var with Variable(x) -> x | _ -> failwith ("bad return"))

    member _this.vout_indirect var value =
        _writeVariableIndirect value (match var with Variable(x) -> x | _ -> failwith("bad return"))

    member this.call addr retaddr retdata (args:uint16 array) =
        if addr - dynamic_start = 0 then (this.vout retdata 0us; retaddr) else
        let args_start = stack.Length
        let numlocals = _read8 addr |> int
        routine_stack.Push(addr, args_start, numlocals, retdata, retaddr);
        for i in 0 .. (numlocals-1) do
            _push (if i < args.Length then args.[i] else _read16 (addr + 1 + i * 2))
        done;
        addr + 1 + numlocals * 2

    member this.ret retval =
        let _addr, args_start, _numlocals, retdata, retaddr = routine_stack.Pop()
        while stack.Length <> args_start do _pop () |> ignore done;
        this.vout retdata retval;
        retaddr

    member this.ret_indirect retval =
        let _addr, args_start, _numlocals, retdata, retaddr = routine_stack.Pop()
        while stack.Length <> args_start do _pop () |> ignore done;
        this.vout_indirect retdata retval;
        retaddr

    member _this.removeObj (obj : zobject) =
        if obj.parent <> 0us then
            let parent = obj.parent |> _readObj
            if parent.child = obj.num then
                { parent with child=obj.sibling } |> _writeObj
            else
                let rec getSibling i =
                    let o = i |> _readObj
                    if o.sibling = obj.num then o else getSibling o.sibling
                let child = parent.child |> getSibling
                { child with sibling=obj.sibling } |> _writeObj
        { obj with parent=0us; sibling=0us } |>> _writeObj

    member this.insertObj (obj : zobject) (dest : uint16) =
        let obj = obj |> this.removeObj
        let dest = dest |> _readObj
        { obj with sibling=dest.child; parent=dest.num } |> _writeObj
        { dest with child=obj.num } |> _writeObj

    member _this.getProp (index : int) (obj : zobject) =
        // Pass -1 to get the first property
        let rec iterProperties addr =
            let p = _getProp addr
            match p.num with
            | 0 -> (0xa |> _read16 |> _addr) + (index - 1) * 2 |> _getProp
            | i when i = index -> p
            | _ -> addr + 1 + p.len |> iterProperties
        let addr = obj.addr + 1 + obj.name.length
        iterProperties addr

    member _this.getNextProp (index : int) (obj : zobject) =
        // TODO: gracefully handle the missing property case (with an error message)
        let rec iterProperties found addr =
            let p = _getProp addr
            match p.num, found with
            | 0, false -> 0
            | i, true -> i
            | i, false -> addr + 1 + p.len |> iterProperties (i = index)
        let addr = obj.addr + 1 + obj.name.length
        iterProperties (index = 0) addr |> uint16

    member _this.parseInput _max_parse (_input : string) =
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
    let mutable _rand = System.Random()

    let read i = s.vin i.args.[0]
    let read_addr = read >> s.addr
    let read2 i = (s.vin i.args.[0], s.vin i.args.[1])
    let read2_i16 i = (s.vin_i16 i.args.[0], s.vin_i16 i.args.[1])
    let read_obj = read_addr >> uint16 >> s.readObj
    let read_high_addr i = (i.args.[0] |> s.vin) + 2us * (i.args.[1] |> s.vin) |> s.addr
    let read_prop i = (i.args.[1] |> s.vin |> int, i |> read_obj) ||> s.getProp
    let read_next_prop i = (i.args.[1] |> s.vin |> int, i |> read_obj) ||> s.getNextProp

    let write i x = x |> s.vout i.ret
    let write_i16 i x = x |> uint16 |> s.vout i.ret
    let write_obj o = s.writeObj o

    let jump (i:instruction) x =
        if x = i.compare then
            ip <-
                match i.offset with
                | 0 -> s.ret 0us
                | 1 -> s.ret 1us
                | _ -> ip + i.length + i.offset - 2
        else ()

    let names0op = [| "rtrue"; "rfalse"; "print"; "print_ret"; "no"; "save"; "restore"; "restart"; "ret_popped"; "pop"; "quit"; "new_line"; "show_status"; "verify"; "extended"; "piracy" |]
    let names1op = [| "jz"; "get_sibling"; "get_child"; "get_parent"; "get_prop_len"; "inc"; "dec"; "print_addr"; "call_1s"; "remove_obj"; "print_obj"; "ret"; "jump"; "print_paddr"; "load"; "not"; "call_1n" |]
    let names2op = [| "none"; "je"; "jl"; "jg"; "dec_chk"; "inc_chk"; "jin"; "test"; "or"; "and"; "test_attr"; "set_attr"; "clear_attr"; "store"; "insert_obj"; "loadw"; "loadb"; "get_prop"; "get_prop_addr"; "get_next_prop"; "add"; "sub"; "mul"; "div"; "mod"; "call_2s"; "call_2n"; "set_colour"; "throw" |]
    let namesvar = [| "call"; "storew"; "storeb"; "put_prop"; "sread"; "print_char"; "print_num"; "random"; "push"; "pull"; "split_window"; "set_window"; "call_vs2"; "erase_window"; "erase_line"; "set_cursor"; "get_cursor"; "set_text_style"; "buffer_mode"; "output_stream"; "input_stream"; "sound_effect"; "read_char"; "scan_table"; "not_v4"; "call_vn"; "call_vn2"; "tokenise"; "encode_text"; "copy_table"; "print_table"; "check_arg_count" |]

    let attr_bit x = 1u <<< (31 - (x |> s.vin |>int))
    let nul2op = fun (op:instruction) _ -> _flush (); failwith <| sprintf "Unimplemented 2op instruction %s" names2op.[op.opcode]
    let instructions2op = [|
        nul2op; (* none *)
        (fun i _ -> (* je *)
            let x = i |> read
            seq { for a in i.args.[1..] -> x = (a |> s.vin) }
            |> Seq.contains true
            |> jump i);
        (fun i y -> (* jl *) i |> read2_i16 ||> (<) |> jump i);
        (fun i y -> (* jg *) i |> read2_i16 ||> (>) |> jump i);
        (fun i y -> (* dec_chk *)
            let var = i |> read |> byte
            let old = var |> s.readVariable |> int16
            var |> s.writeVariable (old - 1s |> uint16)
            old - 1s < (y |> s.vin_i16) |> jump i);
        (fun i y -> (* inc_chk *)
            let var = i |> read |> byte
            let old = var |> s.readVariable |> int16
            var |> s.writeVariable (old + 1s |> uint16)
            old + 1s > (y |> s.vin_i16) |> jump i);
        (fun i y -> (* jin *)
            (i |> read_obj).parent = (y |> s.vin) |> jump i);
        (fun i y -> (* test *)
            let (x, y) = i |> read2
            (x &&& y) = y |> jump i);
        (fun i y -> (* or *)  i |> read2 ||> (|||) |> write i);
        (fun i y -> (* and *) i |> read2 ||> (&&&) |> write i);
        (fun i y -> (* test_attr *)
            ((i |> read_obj).attrib &&& (attr_bit y)) <> 0u |> jump i);
        (fun i y -> (* set_attr *)
            let o = i |> read_obj
            { o with attrib=o.attrib ||| (attr_bit y) } |> write_obj);
        (fun i y -> (* clear_attr *)
            let o = i |> read_obj
            { o with attrib=o.attrib &&& ~~~(attr_bit y) } |> write_obj);
        (fun i y -> (* store *)
            i |> read |> byte |> s.writeVariableIndirect (y |> s.vin));
        (fun i y -> (* insert_obj *)
            (i |> read_obj, y |> s.vin) ||> s.insertObj);
        (fun i _ -> (* loadw *) i |> read_high_addr |> s.read16 |> write i);
        (fun i _ -> (* loadb *)
            i |> read2 ||> (+) |> s.addr |> s.read8 |> uint16 |> write i);
        (fun i _ -> (* get_prop *) i |> read_prop |> s.readProp |> write i);
        (fun i _ -> (* get_prop_addr *) (i |> read_prop).addr |> uint16 |> write i);
        (fun i _ -> (* get_next_prop *) i |> read_next_prop |> write i);
        (fun i _ -> (* add *) i |> read2_i16 ||> (+) |> write_i16 i);
        (fun i _ -> (* sub *) i |> read2_i16 ||> (-) |> write_i16 i);
        (fun i _ -> (* mul *) i |> read2_i16 ||> (*) |> write_i16 i);
        (fun i _ -> (* div *) i |> read2_i16 ||> (/) |> write_i16 i);
        (fun i _ -> (* mod *) i |> read2_i16 ||> (%) |> write_i16 i);
        nul2op; (* call_2s *)
        nul2op; (* call_2n *)
        nul2op; (* set_colour *)
        nul2op; (* throw *)
    |]

    let nul1op = fun (op:instruction) -> _flush (); failwith <| sprintf "Unimplemented 1op instruction %s" names1op.[op.opcode]
    let instructions1op = [|
        (fun i -> (* jz *) (i |> read) = 0us |> jump i);
        (fun i -> (* get_sibling *)
            ((i |> read_obj).sibling |>> write i) <> 0us |> jump i);
        (fun i -> (* get_child *)
            ((i |> read_obj).child |>> write i) <> 0us |> jump i);
        (fun i -> (* get_parent *) (i |> read_obj).parent |> write i);
        (fun i ->  (* get_prop_len *)
            let addr = i |> read_addr
            if addr = 0 then
                0us |> write i
            else
                let prop = addr |> int |> s.readPropAtAddr
                prop.len |> uint16 |> write i);
        (fun i -> (* inc *)
            let var = i |> read |> byte
            (((var |> s.readVariable |> int16) + 1s) |> uint16, var) ||> s.writeVariable);
        (fun i -> (* dec *)
            let var = i |> read |> byte
            (((var |> s.readVariable |> int16) - 1s) |> uint16, var) ||> s.writeVariable);
        (fun i -> (* print_addr *) (i |> read_addr |> s.readString).s |> _out);
        nul1op; (* call_1s *)
        (fun i -> (* remove_obj *) i |> read_obj |> s.removeObj |> ignore);
        (fun i -> (* print_obj *) (i |> read_obj).name.s |> _out);
        (fun i -> (* ret *) ip <- i |> read |> s.ret);
        (fun i -> (* jump *)
            ip <- ip + i.length + (i |> read |> int16 |> int) - 2);
        (fun i -> (* print_paddr *)
            (i.args.[0] |> s.vin_paddr |> s.readString).s |> _out);
        (fun i -> (* load *)
            i |> read |> byte |> s.readVariableIndirect |> write i);
        (fun i -> (* not *) i |> read |> (~~~) |> write i);
        nul1op; (* call_1n *)
    |]

    let nul0op = fun (op:instruction) -> _flush (); failwith <| sprintf "Unimplmented 0op instruction %s" names0op.[op.opcode]
    let instructions0op = [|
        (fun _ -> (* rtrue *)  ip <- s.ret 1us);
        (fun _ -> (* rfalse *) ip <- s.ret 0us);
        (fun i -> (* print *) i.string |> _out);
        (fun i -> (* print_ret *)
            i.string + "\n" |> _out
            ip <- s.ret 1us);
        nul0op; (* no *)
        nul0op; (* save *)
        nul0op; (* restore *)
        nul0op; (* restart *)
        (fun _ -> (* ret_popped *) ip <- s.readVariable 0uy |> s.ret);
        (fun _ -> (* pop *) s.readVariable 0uy |> ignore);
        (fun _ -> (* quit *) _flush (); finished <- true);
        (fun _ -> (* new_line *) "\n" |> _out);
        nul0op; (* show_status *)
        (fun i -> (* verify *) true |> jump i);
        nul0op; (* extended *)
        nul0op; (* piracy *)
    |]

    let trim_string len (str:string) = str.Substring(0, (str.Length, len) ||> min)
    let nulvar = fun (op:instruction) -> _flush (); failwith <| sprintf "Unimplemented var instruction %s" namesvar.[op.opcode]
    let instructionsvar =[|
        (fun i -> (* call*)
            let args = seq { for x in i.args.[1..] -> x |> s.vin } |> Seq.toArray
            ip <- s.call(i |> read |> s.paddr) (ip + i.length) i.ret args);
        (fun i -> (* storew*)
            i |> read_high_addr |> s.write16 (i.args.[2] |> s.vin));
        (fun i -> (* storeb*)
            i |> read_high_addr |> s.write8 (i.args.[2] |> s.vin));
        (fun i -> (* put_prop*)
            i |> read_prop |> s.writeProp (i.args.[2] |> s.vin));
        (fun i -> (* sread*)
            _flush ()
            let str = _in ()
            let x, y = i |> read2
            str.ToLower() |> trim_string (x |> int) |> s.parseInput y);
        (fun i -> (* print_char*) i |> read |> char |> sprintf "%c" |> _out);
        (fun i -> (* print_num*) i |> read |> int16 |> sprintf "%d" |> _out);
        (fun i -> (* random*)
            let range = i |> read |> int16
            if range <= 0s then
                _rand <- System.Random(range |> int)
                0us |> write i
            else
                _rand.Next(0, range |> int) + 1 |> uint16 |> write i
            );
        (fun i -> (* push*) s.writeVariable (i.args.[0] |> s.vin) 0uy);
        (fun i -> (* pull*)
            i |> read |> byte |> s.writeVariableIndirect (s.readVariable 0uy));
        nulvar; (* split_window*)
        nulvar; (* set_window*)
        nulvar; (* call_vs2*)
        nulvar; (* erase_window*)
        nulvar; (* erase_line*)
        nulvar; (* set_cursor*)
        nulvar; (* get_cursor*)
        nulvar; (* set_text_style*)
        nulvar; (* buffer_mode*)
        nulvar; (* output_stream*)
        nulvar; (* input_stream*)
        nulvar; (* sound_effect*)
        nulvar; (* read_char*)
        nulvar; (* scan_table*)
        nulvar; (* not_v4*)
        nulvar; (* call_vn*)
        nulvar; (* call_vn2*)
        nulvar; (* tokenise*)
        nulvar; (* encode_text*)
        nulvar; (* copy_table*)
        nulvar; (* print_table*)
        nulvar; (* check_arg_count*)
    |]

    let decode_short op =
        let optype, length, args =
            match op &&& 0x30uy >>> 4 with
            | 3uy -> Op0, 1, [||]
            | 2uy -> Op1, 2, [| Variable(ip + 1 |> s.read8) |]
            | 1uy -> Op1, 2, [| Small(ip + 1 |> s.read8) |]
            | _ -> Op1, 3, [| Large(ip + 1 |> s.read16) |]
        { emptyInstruction with opcode=(op&&&0x0fuy)|>int; optype=optype; length=length; args=args }

    let decode_long op =
        let x = ip + 1 |> s.read8
        let y = ip + 2 |> s.read8
        { emptyInstruction with opcode=(op&&&0x1fuy)|>int; optype=Op2; length=3; args= [| (if op &&& 0x40uy <> 0uy then Variable(x) else Small(x)); (if op &&& 0x20uy <> 0uy then Variable(y) else Small(y)) |] }

    let decode_var op =
        let optypes = ip + 1 |> s.read8
        let size = ref 2
        let generateArgs x =
            let shift = (3 - x) * 2
            let mask = 3 <<< shift |> byte
            match (optypes &&& mask) >>> shift with
            | 0x3uy -> Omitted
            | 0x2uy -> size := !size + 1; Variable(ip + !size - 1 |> s.read8)
            | 0x1uy -> size := !size + 1; Small(ip + !size - 1 |> s.read8)
            | _-> size := !size + 2; Large(ip + !size - 2 |> s.read16)
        let args =
            seq { for x in 0..3 -> generateArgs x } |>
            Seq.filter (fun x -> match x with | Omitted -> false | _ -> true) |>
            Seq.toArray
        { emptyInstruction with
            opcode=(op&&&0x1fuy)|>int;
            optype=if op &&& 0x20uy <> 0uy then Var else Op2;
            length=(!size);
            args=args }

    let stores opcode = function
        | Op2 -> (opcode >= 0x08 && opcode <= 0x09) || (opcode >= 0x0f && opcode <= 0x19)
        | Op1 -> (opcode >= 0x01 && opcode <= 0x04) || opcode = 0x08 || (opcode >= 0x0e && opcode <= 0x0f)
        | Var -> opcode = 0x0 || opcode = 0x7
        | _ -> false

    let branches opcode = function
        | Op2 -> (opcode >= 1 && opcode <= 7) || (opcode = 10)
        | Op1 -> (opcode >= 0 && opcode <= 2)
        | Op0 -> opcode = 5 || opcode = 6 || opcode = 0xd || opcode = 0xf
        | _ -> false

    let prints opcode = function
        | Op0 -> (opcode = 0x02) || (opcode = 0x03)
        | _ -> false

    let add_return i =
        if stores i.opcode i.optype then
            { i with length=i.length+1; ret=Variable(ip + i.length |> s.read8) }
        else i

    let add_branch i =
        if branches i.opcode i.optype then
            let branch1 = ip + i.length |> s.read8 |> int
            let offset = (0x80 &&& branch1) <<< 8
            let offset, len =
                if branch1 &&& 0x40 <> 0 then
                    offset ||| (branch1 &&& 0x3f), 1
                else
                    let branch2 = ip + i.length + 1 |> s.read8 |> int
                    (offset ||| (branch1 &&& 0x1f <<< 8) ||| branch2), 2
            let offset, compare = offset &&& 0x7fff, offset &&& 0x8000 <> 0
            let offset = if offset > 0x0fff then -(0x1fff - offset + 1) else offset
            { i with offset=offset; length=i.length + len; compare=compare }
        else i

    let add_print i =
        if prints i.opcode i.optype then
            let str = ip + i.length |> s.readString
            { i with length=i.length+str.length; string=str.s }
        else i

    let decode ip =
        let op = s.read8 ip
        match (op &&& 0xc0uy) >>> 6 with
        | 0x03uy -> decode_var op
        | 0x02uy -> decode_short op
        | _ -> decode_long op
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

    let print_ret = function
        | Variable(x) when x = 0uy -> " -> -(SP)"
        | Variable(x) when x >= 0x10uy -> sprintf " -> G%02x" (x - 0x10uy)
        | Variable(x) -> sprintf " -> L%02x" (x - 1uy)
        | _ -> ""

    let rec print str ret = function
        | h :: g :: t -> print (str + (string_from_operand h) + ",") ret (g :: t)
        | h :: t -> print (str + (string_from_operand h)) ret t
        | [] -> str + (print_ret ret)

    let disassemble i =
        let names =
            match i.optype with
            | Op0 -> names0op
            | Op1 -> names1op
            | Op2 -> names2op
            | Var -> namesvar
        printfn "[%08X] %s" ip (print (names.[i.opcode].ToUpper() + "\t") i.ret (i.args |> Array.toList)); i

    let execute i =
        let oldip = ip
        match i.optype with
        | Op0 -> instructions0op.[i.opcode] i
        | Op1 -> instructions1op.[i.opcode] i
        | Op2 -> instructions2op.[i.opcode] i i.args.[1]
        | Var -> instructionsvar.[i.opcode] i
        if ip = oldip then ip + i.length else ip

    member _this.Run () =
        while finished <> true do
            ip <- ip
            |> decode
            #if DEBUG
            |> disassemble
            #endif
            |> execute
end

do
    Machine("zork.z3").Run ()
