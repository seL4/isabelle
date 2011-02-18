(*  Title:      HOL/Bali/Value.thy
    Author:     David von Oheimb
*)
header {* Java values *}



theory Value imports Type begin

typedecl loc            --{* locations, i.e. abstract references on objects *}

datatype val
        = Unit          --{* dummy result value of void methods *}
        | Bool bool     --{* Boolean value *}
        | Intg int      --{* integer value *}
        | Null          --{* null reference *}
        | Addr loc      --{* addresses, i.e. locations of objects *}


primrec the_Bool :: "val \<Rightarrow> bool"
  where "the_Bool (Bool b) = b"

primrec the_Intg :: "val \<Rightarrow> int"
  where "the_Intg (Intg i) = i"

primrec the_Addr :: "val \<Rightarrow> loc"
  where "the_Addr (Addr a) = a"

type_synonym dyn_ty = "loc \<Rightarrow> ty option"

primrec typeof :: "dyn_ty \<Rightarrow> val \<Rightarrow> ty option"
where
  "typeof dt  Unit = Some (PrimT Void)"
| "typeof dt (Bool b) = Some (PrimT Boolean)"
| "typeof dt (Intg i) = Some (PrimT Integer)"
| "typeof dt  Null = Some NT"
| "typeof dt (Addr a) = dt a"

primrec defpval :: "prim_ty \<Rightarrow> val"  --{* default value for primitive types *}
where
  "defpval Void = Unit"
| "defpval Boolean = Bool False"
| "defpval Integer = Intg 0"

primrec default_val :: "ty \<Rightarrow> val"  --{* default value for all types *}
where
  "default_val (PrimT pt) = defpval pt"
| "default_val (RefT  r ) = Null"

end
