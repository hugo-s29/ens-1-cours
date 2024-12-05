type ty = Tint | Tarr of ty * ty | Tuvar of string

let rec string_of_ty = function
  | Tint -> "int"
  | Tuvar s -> s
  | Tarr(ty1,ty2) -> 
      Printf.sprintf "arr(%s,%s)"
        (string_of_ty ty1) (string_of_ty ty2)

