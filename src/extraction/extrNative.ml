type comparison = Eq | Lt | Gt

type 'a carry = C0 of 'a | C1 of 'a
    
type uint = int 
    
  (* to be used only on 32 bits achitectures *)
let maxuint31 = Int32.of_string "0x7FFFFFFF"
let uint_32 i =  Int32.logand (Int32.of_int i) maxuint31
    
let select f32 f64 = if Sys.word_size = 64 then f64 else f32
 
    (* conversion to an int *)
let to_int i = i 

let of_int_32 i = i
let of_int_64 i = i land 0x7FFFFFFF

let of_int = select of_int_32 of_int_64
let of_uint i = i
 	
    (* convertion of an uint31 to a string *)
let to_string_32 i = Int32.to_string (uint_32 i)
let to_string_64 = string_of_int 

let to_string = select to_string_32 to_string_64
let of_string s = 
  let i32 = Int32.of_string s in
  if Int32.compare Int32.zero i32 <= 0
      && Int32.compare i32 maxuint31 <= 0 
  then Int32.to_int i32
  else raise (Failure "int_of_string")

      

    (* logical shift *)
let l_sl x y = 
  of_int (if 0 <= y && y < 31 then x lsl y else 0)
    
let l_sr x y = 
  if 0 <= y && y < 31 then x lsr y else 0
    
let l_and x y = x land y
let l_or x y = x lor y
let l_xor x y = x lxor y

    (* addition of int31 *)
let add x y = of_int (x + y)
 
    (* subtraction *)
let sub x y = of_int (x - y)
   
    (* multiplication *)
let mul x y = of_int (x * y)
    
    (* exact multiplication *)
let mulc_32 x y =
  let x = Int64.of_int32 (uint_32 x) in
  let y = Int64.of_int32 (uint_32 y) in
  let m = Int64.mul x y in
  let l = Int64.to_int m in
  let h = Int64.to_int (Int64.shift_right_logical m 31) in
  h,l

let mulc_64 x y =
  let m = x * y in
  let l = of_int_64 m in
  let h = of_int_64 (m lsr 31) in
  h, l
let mulc = select mulc_32 mulc_64

    (* division *)
let div_32 x y = 
  if y = 0 then 0 else
  Int32.to_int (Int32.div (uint_32 x) (uint_32 y)) 
let div_64 x y = if y = 0 then 0 else  x / y
let div = select div_32 div_64
    
    (* modulo *)
let rem_32 x y = 
  if y = 0 then 0 
  else Int32.to_int (Int32.rem (uint_32 x) (uint_32 y))
let rem_64 x y = if y = 0 then 0 else x mod y
let rem = select rem_32 rem_64
    
    (* division of two numbers by one *)
let div21_32 xh xl y =
  if y = 0 then (0,0) 
  else
    let x = 
      Int64.logor 
	(Int64.shift_left (Int64.of_int32 (uint_32 xh)) 31) 
	(Int64.of_int32 (uint_32 xl)) in
    let y = Int64.of_int32 (uint_32 y) in
    let q = Int64.div x y in
    let r = Int64.rem x y in
    Int64.to_int q, Int64.to_int r
let div21_64 xh xl y =
  if y = 0 then (0,0) 
  else
    let x = (xh lsl 31) lor xl in
    let q = x / y in
    let r = x mod y in
    q, r
let div21 = select div21_32 div21_64
    
    (* comparison *)
let lt_32 x y = (x lxor 0x40000000) < (y lxor 0x40000000)
(*  if 0 <= x then
    if 0 <= y then x < y
    else true
  else if 0 <= y then false
    else x < y *)
(* Int32.compare (uint_32 x) (uint_32 y) < 0 *)

let lt_64 x y = x < y
let lt = select lt_32 lt_64
    
let le_32 x y = 
 (x lxor 0x40000000) <= (y lxor 0x40000000)
(*
  if 0 <= x then
    if 0 <= y then x <= y
    else true
  else if 0 <= y then false
    else x <= y
*)
(*Int32.compare (uint_32 x) (uint_32 y) <= 0*)
let le_64 x y = x <= y
let le = select le_32 le_64

let eq x y = x == y
    
let cmp_32 x y = Int32.compare (uint_32 x) (uint_32 y)
let cmp_64 x y = compare x y
let compare = select cmp_32 cmp_64
 
let compare x y =
  match compare x y with
  | x when x < 0 -> Lt
  | 0 -> Eq
  | _ -> Gt

    (* head tail *)

let head0 x =
  let r = ref 0 in
  let x = ref x in
  if !x land 0x7FFF0000 = 0 then r := !r + 15
  else x := !x lsr 15;
  if !x land 0xFF00 = 0 then (x := !x lsl 8; r := !r + 8);
  if !x land 0xF000 = 0 then (x := !x lsl 4; r := !r + 4);
  if !x land 0xC000 = 0 then (x := !x lsl 2; r := !r + 2);
  if !x land 0x8000 = 0 then (x := !x lsl 1; r := !r + 1);
  if !x land 0x8000 = 0 then (               r := !r + 1);
  !r;;

let tail0 x =
  let r = ref 0 in
  let x = ref x in
  if !x land 0xFFFF = 0 then (x := !x lsr 16; r := !r + 16);
  if !x land 0xFF = 0   then (x := !x lsr 8;  r := !r + 8);
  if !x land 0xF = 0    then (x := !x lsr 4;  r := !r + 4);
  if !x land 0x3 = 0    then (x := !x lsr 2;  r := !r + 2);
  if !x land 0x1 = 0    then (                r := !r + 1);
  !r

let addc x y =
  let s = add x y in
  if lt s x then C1 s else C0 s

let addcarryc x y =
  let s = add (x+1) y in 
  if le s x then C1 s else C0 s

let subc x y =
  let s = sub x y in
  if lt x y then C1 s else C0 s

let subcarryc x y =
  let s = sub (x-1) y in
  if le x y then C1 s else C0 s

let diveucl x y = div x y, rem x y

let diveucl_21 = div21

let addmuldiv p i j =
  let p' = to_int p in
  of_uint (l_or 
	     (l_sl i p) 
	     (l_sr j (of_int (31 - p'))))

let rec foldi_cont f min max cont a =
  if lt min max then f min (foldi_cont f (add min 1) max cont) a
  else if min = max then f min cont a 
  else cont a 

let rec foldi_down_cont f max min cont a =
  if lt min max then
    f max (foldi_down_cont f (sub max 1) min cont) a
  else if min = max then f min cont a
  else cont a

let print_uint x =
  Printf.fprintf stderr "%s" (to_string x);
  flush stderr;
  x
   
(* Les Tableaux maintenant *)

let max_array_length32 = 4194303 (* Sys.max_array_length on arch32 *)
 
type 'a parray = ('a kind) ref
and 'a kind =
  | Array of 'a array 
	(* | Matrix of 'a array array *)
  | Updated of int * 'a * 'a parray

let of_array t = ref (Array t)

let parray_make n def = 
  let n = to_int n in
  let n = 
    if 0 <= n && n < max_array_length32 then n + 1 
    else max_array_length32 in
  ref (Array (Array.make n def))

let rec get_updated p n =
  match !p with
  | Array t ->
      let l =  Array.length t in
      if 0 <= n && n < l then Array.unsafe_get t n
      else (Array.unsafe_get t (l-1))
  | Updated (k,e,p) -> if n = k then e else get_updated p n
      
let parray_get p n =
  let n = to_int n in
  match !p with
  | Array t ->
      let l = Array.length t in
      if 0 <= n && n < l then Array.unsafe_get t n
      else (Array.unsafe_get t (l-1))
  | Updated _ -> get_updated p n
      

let rec default_updated p =
  match !p with
  | Array t -> Array.unsafe_get t (Array.length t - 1)
  | Updated (_,_,p) -> default_updated p
	
let parray_default p =
  match !p with
  | Array t -> Array.unsafe_get t (Array.length t - 1)
  | Updated (_,_,p) -> default_updated p

let rec length p =
  match !p with
  | Array t -> of_int (Array.length t - 1) (* The default value *)
  | Updated (_, _, p) -> length p
	
let parray_length p = 
  match !p with
  | Array t -> of_int (Array.length t - 1)
  | Updated (_, _, p) -> length p
	
let parray_set p n e =
  let kind = !p in
  let n = to_int n in
  match kind with
  | Array t ->
      if 0 <= n && n < Array.length t - 1 then
	let res = ref kind in
	p := Updated (n, Array.unsafe_get t n, res);
	Array.unsafe_set t n e;
	res
      else p
  | Updated _ ->
      if 0 <= n && n < to_int (parray_length p) then
	ref (Updated(n, e, p))   
      else p

	
let rec copy_updated p =
  match !p with
  | Array t -> Array.copy t
  | Updated (n,e,p) -> 
      let t = copy_updated p in 
      Array.unsafe_set t n e; t 
	
let parray_copy p =
  let t = 
    match !p with
    | Array t -> Array.copy t
    | Updated _ -> copy_updated p in
  ref (Array t)
    
let rec rerootk t k = 
  match !t with
  | Array _ -> k ()
  | Updated (i, v, t') -> 
      let k' () =
	begin match !t' with
	| Array a as n ->
	    let v' = a.(i) in
	    a.(i) <- v;
	    t := n;
	    t' := Updated (i, v', t)
	| Updated _ -> assert false 
	end; k() in
      rerootk t' k'
	
let parray_reroot t = rerootk t (fun () -> t)
 
let parray_init n f def =
  let n = to_int n in
  let n = 
    if 0 <= n && n < max_array_length32 then n + 1 
    else max_array_length32 in
  let t = Array.make n def in
  for i = 0 to n - 2 do Array.unsafe_set t i (f i) done;
  ref (Array t)

let parray_map f p =
  match !p with
  | Array t -> ref (Array (Array.map f t))
  | _ ->
      let len = to_int (length p) in
      ref (Array 
	     (Array.init (len + 1) 
		(fun i -> f (parray_get p (of_int i)))))
	
