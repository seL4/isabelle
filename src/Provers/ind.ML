(*  Title: 	Provers/ind
    ID:         $Id$
    Author: 	Tobias Nipkow
    Copyright   1991  University of Cambridge

Generic induction package -- for use with simplifier
*)

signature IND_DATA =
  sig
  val spec: thm (* All(?P) ==> ?P(?a) *)
  end;


signature IND =
  sig
  val all_frees_tac: string -> int -> tactic
  val ALL_IND_TAC: thm -> (int -> tactic) -> (int -> tactic)
  val IND_TAC: thm -> (int -> tactic) -> string -> (int -> tactic)
  end;


functor InductionFun(Ind_Data: IND_DATA):IND =
struct
local open Ind_Data in

val _$(_$Var(a_ixname,aT)) = concl_of spec;
val a_name = implode(tl(explode(Syntax.string_of_vname a_ixname)));

fun add_term_frees tsig =
let fun add(tm, vars) = case tm of
	Free(v,T) => if Type.typ_instance tsig (T,aT) then v ins vars
		     else vars
      | Abs (_,_,body) => add(body,vars)
      | rator$rand => add(rator, add(rand, vars))
      | _ => vars
in add end;


fun qnt_tac i = fn (tac,var) => tac THEN res_inst_tac [(a_name,var)] spec i;

(*Generalizes over all free variables, with the named var outermost.*)
fun all_frees_tac (var:string) i thm = 
    let val tsig = Sign.tsig_of (Thm.sign_of_thm thm);
        val frees = add_term_frees tsig (nth_elem(i-1,prems_of thm),[var]);
        val frees' = sort (rev_order o string_ord) (frees \ var) @ [var]
    in foldl (qnt_tac i) (all_tac,frees') thm end;

fun REPEAT_SIMP_TAC simp_tac n i =
let fun repeat thm = 
        (COND (has_fewer_prems n) all_tac
	 let val k = nprems_of thm
	 in simp_tac i THEN COND (has_fewer_prems k) repeat all_tac end)
	thm
in repeat end;

fun ALL_IND_TAC sch simp_tac i thm = 
	(resolve_tac [sch] i THEN
	 REPEAT_SIMP_TAC simp_tac (nprems_of thm) i) thm;

fun IND_TAC sch simp_tac var =
	all_frees_tac var THEN' ALL_IND_TAC sch simp_tac;


end
end;
