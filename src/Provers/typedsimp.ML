(*  Title: 	typedsimp
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Functor for constructing simplifiers.  Suitable for Constructive Type
Theory with its typed reflexivity axiom a:A ==> a=a:A.  For most logics try
simp.ML.
*)

signature TSIMP_DATA =
  sig
  val refl: thm		(*Reflexive law*)
  val sym: thm		(*Symmetric law*)
  val trans: thm	(*Transitive law*)
  val refl_red: thm	(* reduce(a,a) *)
  val trans_red: thm	(* [|a=b; reduce(b,c) |] ==> a=c *)
  val red_if_equal: thm (* a=b ==> reduce(a,b) *)
  (*Built-in rewrite rules*)
  val default_rls: thm list
  (*Type checking or similar -- solution of routine conditions*)
  val routine_tac: thm list -> int -> tactic
  end;

signature TSIMP =
  sig
  val asm_res_tac: thm list -> int -> tactic   
  val cond_norm_tac: ((int->tactic) * thm list * thm list) -> tactic
  val cond_step_tac: ((int->tactic) * thm list * thm list) -> int -> tactic
  val norm_tac: (thm list * thm list) -> tactic
  val process_rules: thm list -> thm list * thm list
  val rewrite_res_tac: int -> tactic   
  val split_eqn: thm
  val step_tac: (thm list * thm list) -> int -> tactic
  val subconv_res_tac: thm list -> int -> tactic   
  end;


functor TSimpFun (TSimp_data: TSIMP_DATA) : TSIMP = 
struct
local open TSimp_data
in

(*For simplifying both sides of an equation:
      [| a=c; b=c |] ==> b=a
  Can use resolve_tac [split_eqn] to prepare an equation for simplification. *)
val split_eqn = standard (sym RSN (2,trans) RS sym);


(*    [| a=b; b=c |] ==> reduce(a,c)  *)
val red_trans = standard (trans RS red_if_equal);

(*For REWRITE rule: Make a reduction rule for simplification, e.g.
  [| a: C(0); ... ; a=c: C(0) |] ==> rec(0,a,b) = c: C(0) *)
fun simp_rule rl = rl RS trans;

(*For REWRITE rule: Make rule for resimplifying if possible, e.g.
  [| a: C(0); ...; a=c: C(0) |] ==> reduce(rec(0,a,b), c)  *)
fun resimp_rule rl = rl RS red_trans;

(*For CONGRUENCE rule, like a=b ==> succ(a) = succ(b)
  Make rule for simplifying subterms, e.g.
  [| a=b: N; reduce(succ(b), c) |] ==> succ(a)=c: N   *)
fun subconv_rule rl = rl RS trans_red;

(*If the rule proves an equality then add both forms to simp_rls
  else add the rule to other_rls*)
fun add_rule (rl, (simp_rls, other_rls)) =
    (simp_rule rl :: resimp_rule rl :: simp_rls, other_rls)
    handle THM _ => (simp_rls, rl :: other_rls);

(*Given the list rls, return the pair (simp_rls, other_rls).*)
fun process_rules rls = foldr add_rule (rls, ([],[]));

(*Given list of rewrite rules, return list of both forms, reject others*)
fun process_rewrites rls = 
  case process_rules rls of
      (simp_rls,[])  =>  simp_rls
    | (_,others) => raise THM 
	("process_rewrites: Ill-formed rewrite", 0, others);

(*Process the default rewrite rules*)
val simp_rls = process_rewrites default_rls;

(*If subgoal is too flexible (e.g. ?a=?b or just ?P) then filt_resolve_tac
  will fail!  The filter will pass all the rules, and the bound permits
  no ambiguity.*)

(*Resolution with rewrite/sub rules.  Builds the tree for filt_resolve_tac.*)
val rewrite_res_tac = filt_resolve_tac simp_rls 2;

(*The congruence rules for simplifying subterms.  If subgoal is too flexible
    then only refl,refl_red will be used (if even them!). *)
fun subconv_res_tac congr_rls =
  filt_resolve_tac (map subconv_rule congr_rls) 2
  ORELSE'  filt_resolve_tac [refl,refl_red] 1;

(*Resolve with asms, whether rewrites or not*)
fun asm_res_tac asms =
    let val (xsimp_rls,xother_rls) = process_rules asms
    in 	routine_tac xother_rls  ORELSE'  
	filt_resolve_tac xsimp_rls 2
    end;

(*Single step for simple rewriting*)
fun step_tac (congr_rls,asms) =
    asm_res_tac asms   ORELSE'  rewrite_res_tac  ORELSE'  
    subconv_res_tac congr_rls;

(*Single step for conditional rewriting: prove_cond_tac handles new subgoals.*)
fun cond_step_tac (prove_cond_tac, congr_rls, asms) =
    asm_res_tac asms   ORELSE'  rewrite_res_tac  ORELSE'  
    (resolve_tac [trans, red_trans]  THEN'  prove_cond_tac)  ORELSE'  
    subconv_res_tac congr_rls;

(*Unconditional normalization tactic*)
fun norm_tac arg = REPEAT_FIRST (step_tac arg)  THEN
    TRYALL (resolve_tac [red_if_equal]);

(*Conditional normalization tactic*)
fun cond_norm_tac arg = REPEAT_FIRST (cond_step_tac arg)  THEN
    TRYALL (resolve_tac [red_if_equal]);

end;
end;


