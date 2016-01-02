(*  Title:      HOL/MicroJava/J/Value.thy
    Author:     David von Oheimb, Technische Universitaet Muenchen
*)

section \<open>Java Values\<close>

theory Value imports Type begin

typedecl loc' \<comment> "locations, i.e. abstract references on objects" 

datatype loc 
  = XcptRef xcpt \<comment> "special locations for pre-allocated system exceptions"
  | Loc loc'     \<comment> "usual locations (references on objects)"

datatype val
  = Unit        \<comment> "dummy result value of void methods"
  | Null        \<comment> "null reference"
  | Bool bool   \<comment> "Boolean value"
  | Intg int    \<comment> "integer value, name Intg instead of Int because
                   of clash with HOL/Set.thy" 
  | Addr loc    \<comment> "addresses, i.e. locations of objects "

primrec the_Bool :: "val => bool" where
  "the_Bool (Bool b) = b"

primrec the_Intg :: "val => int" where
  "the_Intg (Intg i) = i"

primrec the_Addr :: "val => loc" where
  "the_Addr (Addr a) = a"

primrec defpval :: "prim_ty => val"  \<comment> "default value for primitive types" where
  "defpval Void    = Unit"
| "defpval Boolean = Bool False"
| "defpval Integer = Intg 0"

primrec default_val :: "ty => val"   \<comment> "default value for all types" where
  "default_val (PrimT pt) = defpval pt"
| "default_val (RefT  r ) = Null"

end
