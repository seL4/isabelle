(*  Title:      HOL/MicroJava/J/Term.thy
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   1999 Technische Universitaet Muenchen

Java values
*)

Value = Type +

types   loc		(* locations, i.e. abstract references on objects *)
arities loc :: term

datatype val_		(* name non 'val' because of clash with ML token *)
	= Unit		(* dummy result value of void methods *)
	| Null		(* null reference *)
	| Bool bool	(* Boolean value *)
	| Intg int	(* integer value *) (* Name Intg instead of Int because
					       of clash with HOL/Set.thy *)
	| Addr loc	(* addresses, i.e. locations of objects *)
types	val = val_
translations "val" <= (type) "val_"

consts
  the_Bool	:: "val \\<Rightarrow> bool"
  the_Intg	:: "val \\<Rightarrow> int"
  the_Addr	:: "val \\<Rightarrow> loc"

primrec
 "the_Bool (Bool b) = b"

primrec
 "the_Intg (Intg i) = i"

primrec
 "the_Addr (Addr a) = a"

consts
  defpval	:: "prim_ty \\<Rightarrow> val"	(* default value for primitive types *)
  default_val	:: "ty \\<Rightarrow> val"		(* default value for all types *)

primrec
	"defpval Void    = Unit"
	"defpval Boolean = Bool False"
	"defpval Integer = Intg (#0)"

primrec
	"default_val (PrimT pt) = defpval pt"
	"default_val (RefT  r ) = Null"

end
