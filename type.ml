type typ = Bool | Int | Rat | Struct of (typ*string) list| TypeNomme of string | Pointer of typ | Undefined



let rec string_of_type t = 
  match t with
  | Bool ->  "Bool"
  | Int  ->  "Int"
  | Rat  ->  "Rat"
  | Pointer t -> "Pointer"^string_of_type t
  | TypeNomme n -> n
  | Struct _ -> "struct"
  | Undefined -> "Undefined"


  
let rec toStringType t = 
    match t with
      | Pointer(t1) -> "Pointer "^toStringType t1
      | Int -> "int "
      | Rat -> "rat "
      | Bool -> "bool "
      | Undefined -> "null "
      | TypeNomme tid -> tid
      | Struct(id) -> let (t,i) = List.split(id) in
        "struct { "^(toStringList t i)
                  
  and toStringList t i =
      match t,i with
       | [],[] -> "}"
       | t::tl,i::tl1 -> (toStringType t)^" "^i^" "^toStringList tl tl1^" "
       | _ -> failwith "Error"  
  
  
let est_compatible t1 t2 =
  match t1, t2 with
  | Bool, Bool -> true
  | Int, Int -> true
  | Rat, Rat -> true 
  | _ -> false 

let%test _ = est_compatible Bool Bool
let%test _ = est_compatible Int Int
let%test _ = est_compatible Rat Rat
let%test _ = not (est_compatible Int Bool)
let%test _ = not (est_compatible Bool Int)
let%test _ = not (est_compatible Int Rat)
let%test _ = not (est_compatible Rat Int)
let%test _ = not (est_compatible Bool Rat)
let%test _ = not (est_compatible Rat Bool)
let%test _ = not (est_compatible Undefined Int)
let%test _ = not (est_compatible Int Undefined)
let%test _ = not (est_compatible Rat Undefined)
let%test _ = not (est_compatible Bool Undefined)
let%test _ = not (est_compatible Undefined Int)
let%test _ = not (est_compatible Undefined Rat)
let%test _ = not (est_compatible Undefined Bool)

let est_compatible_list lt1 lt2 =
  try
    List.for_all2 est_compatible lt1 lt2
  with Invalid_argument _ -> false

let%test _ = est_compatible_list [] []
let%test _ = est_compatible_list [Int ; Rat] [Int ; Rat]
let%test _ = est_compatible_list [Bool ; Rat ; Bool] [Bool ; Rat ; Bool]
let%test _ = not (est_compatible_list [Int] [Int ; Rat])
let%test _ = not (est_compatible_list [Int] [Rat ; Int])
let%test _ = not (est_compatible_list [Int ; Rat] [Rat ; Int])
let%test _ = not (est_compatible_list [Bool ; Rat ; Bool] [Bool ; Rat ; Bool ; Int])

let rec getTaille t =
  match t with
  | Int -> 1
  | Bool -> 1
  | Rat -> 2
  | Pointer _ -> 1
  | Struct typeIdList -> let typeList,_ = List.split(typeIdList) in
                    let tailleList = List.map(getTaille) typeList in
                    List.fold_right(fun t1 t2 -> t1 + t2) tailleList 0
  | TypeNomme _ -> failwith "Size undefined"
  | Undefined -> 0
  
let%test _ = getTaille Int = 1
let%test _ = getTaille Bool = 1
let%test _ = getTaille Rat = 2
