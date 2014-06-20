#light "off"

open System

type zstring_shift = ZShiftZero | ZShiftOne | ZShiftTwo
let decode_zstring zs =
	let triplet a b = let v = (a <<< 8) ||| b in
		[(v >>> 10) &&& 0x1f; (v >>> 5) &&& 0x1f; v &&& 0x1f] in
	let rec decode bytes = function
		| a :: b :: tail -> decode (bytes @ (triplet a b)) tail
		| a :: tail -> decode (bytes @ (triplet a 0)) tail
		| [] -> bytes in
	let rec to_char shift str = function
		| 0 :: tail -> to_char shift (str + " ") tail
		| a :: tail when a > 0 && a < 4 -> to_char shift str tail // abbrevs, do later.
		| 4 :: tail -> to_char ZShiftOne str tail
		| 5 :: tail -> to_char ZShiftTwo str tail
		| 6 :: a :: b :: tail when shift = ZShiftTwo -> let x = (a <<< 8 ) ||| b in
			to_char shift (str + Char.ConvertFromUtf32(x).ToString()) tail
		| a :: tail -> let x =
			(match shift with
			| ZShiftZero -> "______abcdefghijklmnopqrstuvwxyz"
			| ZShiftOne -> "______ABCDEFGHIJKLMNOPQRSTUVWXYZ"
			| ZShiftTwo -> "______^\n0123456789.,!?_#\'\"/\\-:()") |> Seq.nth a in
			to_char ZShiftZero (str + x.ToString()) tail
		| [] -> str in
	zs |> decode [] |> to_char ZShiftZero ""

do 
	let data = [0x5d; 0x2a; 0x24; 0x0b; 0x5e; 0x93; 0x64; 0x09; 0x52; 0x97; 0x96 ; 0x45 ] in
	printfn "%A" (decode_zstring data);
	Console.ReadKey(true) |> ignore
