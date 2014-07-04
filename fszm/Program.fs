#light "off"

open System
open System.IO

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
	let readWord offset = ((uint16 bytes.[offset]) <<< 16) ||| (uint16 bytes.[offset+1])
	let readByte offset = bytes.[offset]
	let version = readWord 0
	let dynamic_start = 0us
	let dynamic_end = readWord 0xe
	let static_start = dynamic_end
	let static_end = static_start + (uint16 (min bytes.Length 0xffff))
	let high_start = readWord 0x4
	let high_end = bytes.Length
	let mutable ip = dynamic_start + (readWord 0x6)
	member this.Version = version
	member this.IP with public get() = ip and public set value = ip <- value
	member this.ReadWord = readWord
	member this.ReadByte = readByte
end

type zoperand = ZOperandLarge | ZOperandSmall | ZOperandVariable | ZOperandOmitted
type zinstruction = ZInstruction of uint16
type zargument = ZArgument of uint16 | ZVariable of uint16
type zinstruction_kind =
	| ZInstruction0Op of zinstruction
	| ZInstruction1Op of zinstruction * zargument
	| ZInstruction2Op of zinstruction * zargument * zargument
	| ZInstructionVar of zinstruction * zargument list

let to_var arg =
	match arg with
	| ZArgument(x) -> ZVariable(x)
	| ZVariable(x) -> failwith "argument is already a variable"

let exec inst state =
	match inst with
	| ZInstruction0Op(opcode) -> (match opcode with
		| ZInstruction(0us) -> "rtrue"
		| ZInstruction(1us) -> "rfalse"
		| ZInstruction(2us) -> "print"
		| ZInstruction(3us) -> "print_ret"
		| ZInstruction(5us) -> "save"
		| ZInstruction(6us) -> "restore"
		| ZInstruction(7us) -> "restart"
		| _ -> failwith <| sprintf "unimplemented 0op %A" opcode)
	| ZInstruction1Op(opcode, arg0) -> (match opcode with
		| _ -> failwith <| sprintf "unimplemented 1op %A" opcode)
	| ZInstruction2Op(opcode, arg0, arg1) -> (match opcode with
		| _ -> failwith <| sprintf "unimplmented 2op %A" opcode)
	| ZInstructionVar(opcode, args) -> (match opcode with
		| _ -> failwith <| sprintf "unimplemented var %A" opcode)

let decode_zoperand zs =
	zs

let toUintSeq (bytes : byte []) =
	let br = new BinaryReader(new MemoryStream (bytes)) in
	seq { for _ in 0..(bytes.Length / 4) -> br.ReadUInt32() }

do 
	let story = ZStory "zork.z3" in
	printfn "%A" story.Version;
	//let data = [|0x5duy; 0x2auy; 0x24uy; 0x0buy; 0x5euy; 0x93uy; 0x64uy; 0x09uy; 0x52uy; 0x97uy; 0x96uy; 0x45uy|] in
	//let results = data |> Seq.toList |> decode_zstring in
	//let results = data |> ZString.ToString in
	//printfn "%A" results;
	Console.ReadKey(true) |> ignore
