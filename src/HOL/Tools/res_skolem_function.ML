(*  Author: Jia Meng, Cambridge University Computer Laboratory
    ID: $Id$
    Copyright 2004 University of Cambridge

Generation of unique Skolem functions (with types) as term.
*)

signature RES_SKOLEM_FUNCTION =
sig
  val gen_skolem: term list -> typ -> term
end;

structure ResSkolemFunction: RES_SKOLEM_FUNCTION  =
struct

val skolem_prefix = "sk_";
val skolem_id = ref 0;

fun gen_skolem_name () =
  let val sk_fun = skolem_prefix ^ string_of_int (! skolem_id);
  in inc skolem_id; sk_fun end;

fun gen_skolem univ_vars tp =
  let
    val skolem_type = map Term.fastype_of univ_vars ---> tp
    val skolem_term = Const (gen_skolem_name (), skolem_type)
  in Term.list_comb (skolem_term, univ_vars) end;

end;
