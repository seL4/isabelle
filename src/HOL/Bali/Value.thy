(*  Title:      HOL/Bali/Value.thy
    ID:         $Id$
    Author:     David von Oheimb
    License:    GPL (GNU GENERAL PUBLIC LICENSE)
*)
header {* Java values *}



theory Value = Type:

typedecl loc            --{* locations, i.e. abstract references on objects *}
arities	 loc :: "type"

datatype val
	= Unit          --{* dummy result value of void methods *}
	| Bool bool     --{* Boolean value *}
	| Intg int      --{* integer value *}
	| Null          --{* null reference *}
	| Addr loc      --{* addresses, i.e. locations of objects *}


translations "val" <= (type) "Term.val"
             "loc" <= (type) "Term.loc"

consts   the_Bool   :: "val \<Rightarrow> bool"  
primrec "the_Bool (Bool b) = b"
consts   the_Intg   :: "val \<Rightarrow> int"
primrec "the_Intg (Intg i) = i"
consts   the_Addr   :: "val \<Rightarrow> loc"
primrec "the_Addr (Addr a) = a"

types	dyn_ty      = "loc \<Rightarrow> ty option"
consts
  typeof        :: "dyn_ty \<Rightarrow> val \<Rightarrow> ty option"
  defpval       :: "prim_ty \<Rightarrow> val"  --{* default value for primitive types *}
  default_val   :: "     ty \<Rightarrow> val"  --{* default value for all types *}

primrec "typeof dt  Unit    = Some (PrimT Void)"
	"typeof dt (Bool b) = Some (PrimT Boolean)"
	"typeof dt (Intg i) = Some (PrimT Integer)"
	"typeof dt  Null    = Some NT"
	"typeof dt (Addr a) = dt a"

primrec	"defpval Void    = Unit"
	"defpval Boolean = Bool False"
	"defpval Integer = Intg 0"
primrec	"default_val (PrimT pt) = defpval pt"
	"default_val (RefT  r ) = Null"

end
