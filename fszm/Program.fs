#light "off"

open System
open System.IO
open System.Collections.Generic

type shift = ShiftZero | ShiftOne | ShiftTwo
type String = { s:string; length:int; shift:shift }

type Story(filename) = class
	let mem = File.ReadAllBytes(filename)
	let _read8 off = mem.[off]
	let _read16 off = (mem.[off] |> uint16 <<< 8) ||| (mem.[off+1] |> uint16)

	let unpackTriplet x = [((x >>> 10) &&& 0x1fus |> byte);	((x >>> 5) &&& 0x1fus |> byte);	((x >>> 0) &&& 0x1fus |> byte) ]

	let rec readString_r off str l =
		let x = off + str.length |> _read16 in
		if x &&& 0x8000us <> 0us then (str, l @ (unpackTriplet x)) else
		l @ (unpackTriplet x) |> readString_r off { str with length=str.length+2 }

	let rec pumpString str = function
		| 0uy :: tail -> pumpString { str with s=str.s+" " } tail
		| a :: x :: tail when a > 0uy && a < 4uy ->
			let table = _read16 0x18 |> int in
			let index = 32 * ((int a) - 1) + (int x) in
			let offset = ((table + index * 2) |> _read16 |> int) * 2 in
			let _, l = readString_r offset {s="";length=0;shift=ShiftZero} [] in
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
			pumpString { str with s=str.s+c.ToString();shift=ShiftZero } tail
		| [] -> str
		| _ -> failwith "Bad zstring"

	let _readString off = let str, l = readString_r off {s=""; length=0; shift=ShiftZero } [] in pumpString str l

	do
		printfn "%A" (_readString 0x4fb2).s

	member this.read8 = _read8
	member this.read16 = _read16
	member this.readString = _readString
	member this.version = _read8 0
end

type Machine(filename) = class
	let s = Story(filename)
	let mutable ip = s.read16 0x6 |> int
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

module ZMachine = begin
	type operand = OperandLarge of uint16 | OperandSmall of byte | OperandVariable of byte | OperandOmitted
	type instruction =
	| Instruction0Op of byte
	| Instruction1Op of byte * operand * byte option
	| Instruction2Op of byte * operand * operand * byte option
	| InstructionVar of byte * operand list * byte option

	let to_operand (bytes : byte[]) i = function
	| 0x00uy -> OperandLarge (((uint16 bytes.[i]) <<< 8) ||| (uint16 bytes.[i+1]))
	| 0x01uy -> OperandSmall (bytes.[i])
	| 0x02uy -> OperandVariable (bytes.[i])
	| 0x03uy -> OperandOmitted
	| _ -> failwith "impossible operand type"

	let opsize = function
	| OperandLarge(x) -> 2
	| OperandSmall(x) -> 1
	| OperandVariable(x) -> 1
	| OperandOmitted -> 0

	let stores = function
	| Instruction2Op(opcode,arg0,arg1,ret) -> (opcode >= 0x08uy && opcode <= 0x09uy) ||	(opcode >= 0x09uy && opcode <= 0x19uy)
	| Instruction1Op(opcode,arg0,ret) -> (opcode >= 0x01uy && opcode <= 0x04uy) || opcode = 0x08uy || (opcode >= 0x0euy && opcode <= 0x0fuy)
	| InstructionVar(opcode,args,ret) -> opcode = 0x0uy
	| _ -> false

	let add_return instruction op =
		match instruction with
		| Instruction1Op(opcode,arg0,ret) -> Instruction1Op(opcode,arg0,Some(op))
		| Instruction2Op(opcode,arg0,arg1,ret) -> Instruction2Op(opcode,arg0,arg1,Some(op))
		| InstructionVar(opcode,args,ret) -> InstructionVar(opcode,args,Some(op))
		| _ -> instruction

	let decode_var (bytes : byte []) i op =
		let opcode = (op &&& 0x1fuy) in
		let optypes = seq { for x in 0..3 -> (bytes.[i] &&& (0xc0uy >>> (x*2))) >>> ((3-x)*2) } |> Seq.toList in
		if (op &&& 0x20uy) = 0uy then
			let arg0 = to_operand bytes (i+1) optypes.[0] in
			let arg1 = to_operand bytes (i+1+(opsize arg0)) optypes.[1] in
			1 + (opsize arg0) + (opsize arg1), Instruction2Op(opcode, arg0, arg1, None)
		else
			let rec getOperands bytes i l = function
			| h :: t when h <> 0x3uy ->
				let operand = to_operand bytes i h in
				getOperands bytes (i + opsize operand) (operand :: l) t
			| _ -> List.rev l in
			let args = getOperands bytes (i + 1) [] optypes in
			let sizes = seq { for x in args -> opsize x } in
			(Seq.sum sizes) + 1, InstructionVar(opcode, args, None)

	let decode_short bytes i op =
		let optype = to_operand bytes i ((op &&& 0x30uy) >>> 4) in
		let opcode = (op &&& 0x0fuy) in
		match optype with
		| OperandOmitted -> 0, Instruction0Op(opcode)
		| _ -> opsize optype, Instruction1Op(opcode, optype, None)

	let decode_long bytes i op =
		let opcode = (op &&& 0x1fuy) in
		3, Instruction2Op(opcode,
			to_operand bytes (i+0) (if (op &&& 0x40uy) <> 0uy then 0x02uy else 0x01uy),
			to_operand bytes (i+1) (if (op &&& 0x20uy) <> 0uy then 0x02uy else 0x01uy), None)

	let decode (bytes : byte[]) i =
		let op = bytes.[i] in
		let form = (op &&& 0xc0uy) >>> 6 in
		let size, instruction = match form with
		| 0x03uy -> decode_var bytes (i+1) op
		| 0x02uy -> decode_short bytes (i+1) op
		| _ -> decode_long bytes (i+1) op in
		//printfn "%A" (i, seq { for x in bytes.[i..i+size] -> sprintf "%x" x } |> Seq.toList);
		if stores instruction then
			size + 1, add_return instruction bytes.[i+size+1]
		else
			size, instruction

	let string_from_operand = function
	| OperandLarge(x) -> sprintf "#%04x" x
	| OperandSmall(x) -> sprintf "#%02x" x
	| OperandVariable(x) when x = 0uy -> "(SP)+"
	| OperandVariable(x) when x >= 0x10uy -> sprintf "G%02x" (x - 0x10uy)
	| OperandVariable(x) -> sprintf "L%02x" (x - 1uy)
	| OperandOmitted -> ""

	let rec print str ret = function
	| h :: g :: t -> print (str + (string_from_operand h) + ",") ret (g :: t)
	| h :: t -> print (str + (string_from_operand h)) ret t
	| [] -> str + (match ret with
		| Some(x) when x = 0uy -> " -> -(SP)"
		| Some(x) when x >= 0x10uy -> sprintf " -> G%02x" (x - 0x10uy)
		| Some(x) -> sprintf " -> L%02x" (x - 1uy)
		| None -> "")

	let names_0op = [| "rtrue"; "rfalse"; "print"; "print_ret"; "no"; "save"; "restore"; "restart"; "ret_popped"; "pop"; "quit"; "new_line"; "show_status"; "verify"; "extended"; "piracy" |]
	let names_1op = [| "jz"; "get_sibling"; "get_child"; "get_parent"; "get_prop_len"; "inc"; "dec"; "print_addr"; "call_1s"; "remove_obj"; "print_obj"; "ret"; "jump"; "print_paddr"; "load"; "not"; "call_1n" |]
	let names_2op = [| "none"; "je"; "jl"; "jg"; "dec_chk"; "inc_chk"; "jin"; "test"; "or"; "and"; "test_attr"; "set_attr"; "clear_attr"; "store"; "insert_obj"; "loadw"; "loadb"; "get_prop"; "get_prop_addr"; "get_next_prop"; "add"; "sub"; "mul"; "div"; "mod"; "call_2s"; "call_2n"; "set_colour"; "throw" |]
	let names_var = [| "call"; "storew"; "storeb"; "put_prop"; "sread"; "print_char"; "print_num"; "random"; "push"; "pull"; "split_window"; "set_window"; "call_vs2"; "erase_window"; "erase_line"; "set_cursor"; "get_cursor"; "set_text_style"; "buffer_mode"; "output_stream"; "input_stream"; "sound_effect"; "read_char"; "scan_table"; "not_v4"; "call_vn"; "call_vn2"; "tokenise"; "encode_text"; "copy_table"; "print_table"; "check_arg_count" |]

	let disassemble = function
	| Instruction0Op(opcode) -> print (names_0op.[int opcode].ToUpper() + "\t") None []
	| Instruction1Op(opcode, arg0, ret) -> print (names_1op.[int opcode].ToUpper() + "\t") ret [arg0]
	| Instruction2Op(opcode, arg0, arg1, ret) -> print (names_2op.[int opcode].ToUpper() + "\t") ret [arg0; arg1]
	| InstructionVar(opcode, args, ret) -> print (names_var.[int opcode].ToUpper() + "\t") ret args

	let value_of_arg (s : ZStory) = function
	| OperandVariable(x) -> s.ReadVariable x
	| OperandLarge(x) -> x
	| OperandSmall(x) -> x |> uint16
	| OperandOmitted -> failwith "omitted args have no value"

	// fun x y -> x + y |> out d
	let z_add (s : ZStory) x y d =
		let result = (x |> int16) + (y |> int16) in
		s.WriteVariable (result |> uint16) d

	let interpret (s : ZStory) size = function
	| InstructionVar(0x00uy, args, ret) ->
		s.Call (args.[0] |> value_of_arg s |> s.PackedAddress) (args |> List.tail |> List.map (value_of_arg s)) (s.IP + size) ret.Value
	| Instruction2Op(0x14uy, arg0, arg1, ret) -> z_add s (value_of_arg s arg0) (value_of_arg s arg1) ret.Value; s.IP + size
	//| Instruction2Op(0x19uy, arg0, arg1, ret) -> s.IP + size
	| Instruction0Op(opcode) -> failwith <| sprintf "unhandled 0op instruction 0x%x" opcode
	| Instruction1Op(opcode, arg0, ret) -> failwith <| sprintf "unhandled 1op instruction 0x%x" opcode
	| Instruction2Op(opcode, arg0, arg1, ret) -> failwith <| sprintf "unhandled 2op instruction 0x%x" opcode
	| InstructionVar(opcode, args, ret) -> failwith <| sprintf "unhandled var instruction 0x%x" opcode
end

do
	let test = Story "zork.z3" in
	(*
	let story = ZStory "zork.z3" in
	while story.IP <> 0 do
		let size, inst = ZMachine.decode story.Bytes story.IP in
		printfn "0x%016x %s" story.IP (ZMachine.disassemble inst);
		story.IP <- ZMachine.interpret story size inst
	done;*)
	//let data = [|0x5duy; 0x2auy; 0x24uy; 0x0buy; 0x5euy; 0x93uy; 0x64uy; 0x09uy; 0x52uy; 0x97uy; 0x96uy; 0x45uy|] in
	//let results = data |> Seq.toList |> decode_zstring in
	//let results = data |> ZString.ToString in
	//printfn "%A" results;
	Console.ReadKey(true) |> ignore
