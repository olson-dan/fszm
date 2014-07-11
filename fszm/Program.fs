#light "off"

open System
open System.IO
open System.Collections.Generic

module ZString = begin
	let decode (bytes : byte []) =
		seq {
			for i in 0..((bytes.Length / 2)-1) do
				let h, l = bytes.[i*2+0], bytes.[i*2+1] in
				let x = ((uint16 h) <<< 8) ||| (uint16 l) in
				yield byte ((x >>> 10) &&& 0x1fus);
				yield byte ((x >>> 5) &&& 0x1fus);
				yield byte ((x >>> 0) &&& 0x1fus)
			done
		}

	type shift = ShiftZero | ShiftOne | ShiftTwo
	let ToString zs =
		let rec to_char shift str = function
			| 0uy :: tail -> to_char shift (str + " ") tail
			| a :: tail when a > 0uy && a < 4uy -> to_char shift str tail // abbrevs, do later.
			| 4uy :: tail -> to_char ShiftOne str tail
			| 5uy :: tail -> to_char ShiftTwo str tail
			| 6uy :: a :: b :: tail when shift = ShiftTwo -> let x = (a <<< 5) ||| b in
				to_char shift (str + Char.ConvertFromUtf32(int(x)).ToString()) tail
			| a :: tail when a > 6uy && a < 32uy -> let x =
				(match shift with
				| ShiftZero -> "______abcdefghijklmnopqrstuvwxyz"
				| ShiftOne -> "______ABCDEFGHIJKLMNOPQRSTUVWXYZ"
				| ShiftTwo -> "______^\n0123456789.,!?_#\'\"/\\-:()") |> Seq.nth (int a) in
				to_char ShiftZero (str + x.ToString()) tail
			| [] -> str
			| _ -> failwith "Error decoding zstring" in
		zs |> decode |> Seq.toList |> to_char ShiftZero ""
end

type ZStory(filename) = class
	let bytes = File.ReadAllBytes(filename)
	let stack = Stack<uint16>()

	let readWord offset = ((uint16 bytes.[offset]) <<< 8) ||| (uint16 bytes.[offset+1])
	let readByte offset = bytes.[offset]
	let writeWord offset word =
		bytes.SetValue(uint8 (word >>> 8), int offset);
		bytes.SetValue(uint8 (word &&& 0xff), (int offset)+1)
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

	let readVar var =
		match var with
		| v when v >= 0x10uy -> globals + 2 * ((int v) - 0x10) |> readWord
		| 0uy -> stack.Pop()
		| _ -> 0us

	member this.Bytes = bytes
	member this.Version = version
	member this.IP with get() = ip and set value = ip <- value
	member this.ReadWord = readWord
	member this.ReadByte = readByte
	member this.WriteWord = writeWord
	member this.WriteByte = writeByte
	member this.Address addr = dynamic_start + (addr |> int)
	member this.PackedAddress addr = dynamic_start + (addr * 2us |> int)
end

module ZInstruction = begin
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

	let stores instruction =
		match instruction with
		| Instruction2Op(opcode,arg0,arg1,ret) ->
			(opcode >= 0x08uy && opcode <= 0x09uy) ||
			(opcode >= 0x09uy && opcode <= 0x19uy)
		| Instruction1Op(opcode,arg0,ret) ->
			(opcode >= 0x01uy && opcode <= 0x04uy) ||
			opcode = 0x08uy ||
			(opcode >= 0x0euy && opcode <= 0x0fuy)
		| InstructionVar(opcode,args,ret) ->
			opcode = 0x0uy
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
			let rec getOperands bytes i optypes l =
				match optypes with
				| h :: t when h <> 0x3uy ->
					let operand = to_operand bytes i h in
					getOperands bytes (i + opsize operand) t (operand :: l)
				| _ -> List.rev l in
			let args = getOperands bytes (i + 1) optypes [] in
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
		2, Instruction2Op(opcode,
			to_operand bytes (i+0) (if (op &&& 0x40uy) <> 0uy then 0x01uy else 0x02uy),
			to_operand bytes (i+1) (if (op &&& 0x20uy) <> 0uy then 0x01uy else 0x02uy), None)

	let decode_operand (bytes : byte[]) i =
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

	let disassemble inst =
		match inst with
		| Instruction0Op(opcode) -> print (names_0op.[int opcode].ToUpper() + "\t") None []
		| Instruction1Op(opcode, arg0, ret) -> print (names_1op.[int opcode].ToUpper() + "\t") ret [arg0]
		| Instruction2Op(opcode, arg0, arg1, ret) -> print (names_2op.[int opcode].ToUpper() + "\t") ret [arg0; arg1]
		| InstructionVar(opcode, args, ret) -> print (names_var.[int opcode].ToUpper() + "\t") ret args
end

let toUintSeq (bytes : byte []) =
	let br = new BinaryReader(new MemoryStream (bytes)) in
	seq { for _ in 0..(bytes.Length / 4) -> br.ReadUInt32() }

do
	let story = ZStory "zork.z3" in
	let rec step ip count =
		if count = 0 then () else
		let size, inst = ZInstruction.decode_operand story.Bytes ip in
		printfn "%s" (ZInstruction.disassemble inst);
		step (ip + size + 1) (count - 1) in
	step story.IP 10;
	//let data = [|0x5duy; 0x2auy; 0x24uy; 0x0buy; 0x5euy; 0x93uy; 0x64uy; 0x09uy; 0x52uy; 0x97uy; 0x96uy; 0x45uy|] in
	//let results = data |> Seq.toList |> decode_zstring in
	//let results = data |> ZString.ToString in
	//printfn "%A" results;
	Console.ReadKey(true) |> ignore
