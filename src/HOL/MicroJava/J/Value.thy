(*  Title:      HOL/MicroJava/J/Value.thy
    Author:     David von Oheimb, Technische Universitaet Muenchen
*)

header {* \isaheader{Java Values} *}

theory Value imports Type begin

typedecl loc' -- "locations, i.e. abstract references on objects" 

datatype loc 
  = XcptRef xcpt -- "special locations for pre-allocated system exceptions"
  | Loc loc'     -- "usual locations (references on objects)"

datatype val
  = Unit        -- "dummy result value of void methods"
  | Null        -- "null reference"
  | Bool bool   -- "Boolean value"
  | Intg int    -- "integer value, name Intg instead of Int because
                   of clash with HOL/Set.thy" 
  | Addr loc    -- "addresses, i.e. locations of objects "

primrec the_Bool :: "val => bool" where
  "the_Bool (Bool b) = b"

primrec the_Intg :: "val => int" where
  "the_Intg (Intg i) = i"

primrec the_Addr :: "val => loc" where
  "the_Addr (Addr a) = a"

primrec defpval :: "prim_ty => val"  -- "default value for primitive types" where
  "defpval Void    = Unit"
| "defpval Boolean = Bool False"
| "defpval Integer = Intg 0"

primrec default_val :: "ty => val"   -- "default value for all types" where
  "default_val (PrimT pt) = defpval pt"
| "default_val (RefT  r ) = Null"

end
