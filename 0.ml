
(* Types *)

type prim
  = PBool of bool
  | PInt of int

type tyscm 
  = TyPrim of prim
  | TyVar of int
  | TyFun of (tyscm * tyscm)

(* Main *)

;;

print_string (TyVar 1)
