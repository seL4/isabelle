(*  Author: Jia Meng, Cambridge University Computer Laboratory
    ID: $Id$
    Copyright 2004 University of Cambridge

Generation of unique Skolem functions (with types) as Term.term.
*)

signature RES_SKOLEM_FUNCTION =
sig

val gen_skolem: Term.term list -> Term.typ  -> Term.term

end;

structure ResSkolemFunction: RES_SKOLEM_FUNCTION  =

struct

val skolem_prefix = "sk_";

(* internal reference starting from 0. *)
val skolem_id = ref 0;


fun gen_skolem_name () = 
    let val new_id = !skolem_id
	val sk_fun = skolem_prefix ^ (string_of_int new_id)
    in
	(skolem_id := new_id + 1; sk_fun) (* increment id by 1. *)
    end;

fun sk_type_of_aux [Var(_,tp1)] tp = Type("fun",[tp1,tp])
  | sk_type_of_aux (Var(_,tp1)::vars) tp = 
    let val tp' = sk_type_of_aux vars tp
    in
	Type("fun",[tp1,tp'])
    end;


fun sk_type_of [] tp = tp
  | sk_type_of vars tp = sk_type_of_aux vars tp; 



fun gen_skolem univ_vars tp = 
    let val new_sk_name = gen_skolem_name ()
	val new_sk_type = sk_type_of univ_vars tp
	val skolem_term = Const(new_sk_name,new_sk_type)
	fun app [] sf = sf
	  | app (var::vars) sf= app vars (sf $ var)
    in
	app univ_vars skolem_term
    end;


end;