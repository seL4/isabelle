(*  Title:      HOL/MicroJava/J/Value.thy
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   1999 Technische Universitaet Muenchen
*)

header "Java Values"

theory Value = Type:

typedecl loc (* locations, i.e. abstract references on objects *)
arities loc :: "term"

datatype val
  = Unit        (* dummy result value of void methods *)
  | Null        (* null reference *)
  | Bool bool   (* Boolean value *)
  | Intg int    (* integer value, name Intg instead of Int because
                   of clash with HOL/Set.thy *)
  | Addr loc    (* addresses, i.e. locations of objects *)

consts
  the_Bool :: "val => bool"
  the_Intg :: "val => int"
  the_Addr :: "val => loc"

primrec
  "the_Bool (Bool b) = b"

primrec
  "the_Intg (Intg i) = i"

primrec
  "the_Addr (Addr a) = a"

consts
  defpval :: "prim_ty => val"  (* default value for primitive types *)
  default_val :: "ty => val"   (* default value for all types *)

primrec
  "defpval Void    = Unit"
  "defpval Boolean = Bool False"
  "defpval Integer = Intg (#0)"

primrec
  "default_val (PrimT pt) = defpval pt"
  "default_val (RefT  r ) = Null"

end
