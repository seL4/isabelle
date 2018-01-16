(*  Title:      HOL/MicroJava/J/Value.thy
    Author:     David von Oheimb, Technische Universitaet Muenchen
*)

section \<open>Java Values\<close>

theory Value imports Type begin

typedecl loc' \<comment> \<open>locations, i.e. abstract references on objects\<close> 

datatype loc 
  = XcptRef xcpt \<comment> \<open>special locations for pre-allocated system exceptions\<close>
  | Loc loc'     \<comment> \<open>usual locations (references on objects)\<close>

datatype val
  = Unit        \<comment> \<open>dummy result value of void methods\<close>
  | Null        \<comment> \<open>null reference\<close>
  | Bool bool   \<comment> \<open>Boolean value\<close>
  | Intg int    \<comment> \<open>integer value, name Intg instead of Int because
                   of clash with HOL/Set.thy\<close> 
  | Addr loc    \<comment> \<open>addresses, i.e. locations of objects\<close>

primrec the_Bool :: "val => bool" where
  "the_Bool (Bool b) = b"

primrec the_Intg :: "val => int" where
  "the_Intg (Intg i) = i"

primrec the_Addr :: "val => loc" where
  "the_Addr (Addr a) = a"

primrec defpval :: "prim_ty => val"  \<comment> \<open>default value for primitive types\<close> where
  "defpval Void    = Unit"
| "defpval Boolean = Bool False"
| "defpval Integer = Intg 0"

primrec default_val :: "ty => val"   \<comment> \<open>default value for all types\<close> where
  "default_val (PrimT pt) = defpval pt"
| "default_val (RefT  r ) = Null"

end
