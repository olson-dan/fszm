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

	let add_return instruction op =
		match instruction with
		| InstructionVar(opcode,args,ret) -> InstructionVar(opcode,args,Some(op))
		| Instruction1Op(opcode,arg0,ret) -> Instruction1Op(opcode,arg0,Some(op))
		| Instruction2Op(opcode,arg0,arg1,ret) -> Instruction2Op(opcode,arg0,arg1,Some(op))
		| _ -> instruction

	let rec print str ret = function
		| h :: t -> print (str + (match h with
		    | OperandLarge(x) -> sprintf "#%04x," x
			| OperandSmall(x) -> sprintf "#%02x," x
			| OperandVariable(x) when x = 0uy -> "(SP)+,"
			| OperandVariable(x) when x >= 0x10uy -> sprintf "G%02x," (x - 0x10uy)
			| OperandVariable(x) -> sprintf "L%02x" (x - 1uy)
			| OperandOmitted -> "")) ret t
		| [] -> str + (match ret with
			| Some(x) when x = 0uy -> " -> -(SP)"
			| Some(x) when x >= 0x10uy -> sprintf " -> G%02x" (x - 0x10uy)
			| Some(x) -> sprintf " -> L%02x" (x - 1uy)
		    | None -> "")

	let disassemble inst =
		match inst with
		| InstructionVar(00uy,args,ret) -> print "CALL " ret args
		| InstructionVar(01uy,args,ret) -> print "STOREW " ret args
		| InstructionVar(02uy,args,ret) -> print "STOREB " ret args
		| Instruction0Op(opcode) -> failwith <| sprintf "unimplemented 0op %A" opcode
		| Instruction1Op(opcode, arg0,ret) -> failwith <| sprintf "unimplemented 1op %A" opcode
		| Instruction2Op(opcode, arg0, arg1, ret) -> failwith <| sprintf "unimplmented 2op %A" opcode
		| InstructionVar(opcode, args, ret) -> failwith <| sprintf "unimplemented var %A" opcode

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
		//printfn "%A" (i, seq { for x in bytes.[i..i+8] -> sprintf "%x" x } |> Seq.toList);
		let op = bytes.[i] in
		let form = (op &&& 0xc0uy) >>> 6 in
		let size, instruction = match form with
		| 0x03uy -> decode_var bytes (i+1) op
		| 0x02uy -> decode_short bytes (i+1) op
		| _ -> decode_long bytes (i+1) op in
		size + 1, add_return instruction 0uy
end

let toUintSeq (bytes : byte []) =
	let br = new BinaryReader(new MemoryStream (bytes)) in
	seq { for _ in 0..(bytes.Length / 4) -> br.ReadUInt32() }

do
	let story = ZStory "zork.z3" in
	let size, inst = ZInstruction.decode_operand story.Bytes story.IP in
	printfn "%A" (size, inst);
	printfn "%s" (ZInstruction.disassemble inst);
	//let data = [|0x5duy; 0x2auy; 0x24uy; 0x0buy; 0x5euy; 0x93uy; 0x64uy; 0x09uy; 0x52uy; 0x97uy; 0x96uy; 0x45uy|] in
	//let results = data |> Seq.toList |> decode_zstring in
	//let results = data |> ZString.ToString in
	//printfn "%A" results;
	Console.ReadKey(true) |> ignore
