(*  Title: 	CTT/ctt.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Tactics and lemmas for ctt.thy (Constructive Type Theory)
*)

open CTT;

(*Formation rules*)
val form_rls = [NF, ProdF, SumF, PlusF, EqF, FF, TF]
and formL_rls = [ProdFL, SumFL, PlusFL, EqFL];

 
(*Introduction rules
  OMITTED: EqI, because its premise is an eqelem, not an elem*)
val intr_rls = [NI0, NI_succ, ProdI, SumI, PlusI_inl, PlusI_inr, TI]
and intrL_rls = [NI_succL, ProdIL, SumIL, PlusI_inlL, PlusI_inrL];


(*Elimination rules
  OMITTED: EqE, because its conclusion is an eqelem,  not an elem
           TE, because it does not involve a constructor *)
val elim_rls = [NE, ProdE, SumE, PlusE, FE]
and elimL_rls = [NEL, ProdEL, SumEL, PlusEL, FEL];

(*OMITTED: eqC are TC because they make rewriting loop: p = un = un = ... *)
val comp_rls = [NC0, NC_succ, ProdC, SumC, PlusC_inl, PlusC_inr];

(*rules with conclusion a:A, an elem judgement*)
val element_rls = intr_rls @ elim_rls;

(*Definitions are (meta)equality axioms*)
val basic_defs = [fst_def,snd_def];

(*Compare with standard version: B is applied to UNSIMPLIFIED expression! *)
qed_goal "SumIL2" CTT.thy
    "[| c=a : A;  d=b : B(a) |] ==> <c,d> = <a,b> : Sum(A,B)"
 (fn prems=>
  [ (resolve_tac [sym_elem] 1),
    (resolve_tac [SumIL] 1),
    (ALLGOALS (resolve_tac [sym_elem])),
    (ALLGOALS (resolve_tac prems)) ]);

val intrL2_rls = [NI_succL, ProdIL, SumIL2, PlusI_inlL, PlusI_inrL];

(*Exploit p:Prod(A,B) to create the assumption z:B(a).  
  A more natural form of product elimination. *)
qed_goal "subst_prodE" CTT.thy
    "[| p: Prod(A,B);  a: A;  !!z. z: B(a) ==> c(z): C(z) \
\    |] ==> c(p`a): C(p`a)"
 (fn prems=>
  [ (REPEAT (resolve_tac (prems@[ProdE]) 1)) ]);

(** Tactics for type checking **)

fun is_rigid_elem (Const("Elem",_) $ a $ _) = not (is_Var (head_of a))
  | is_rigid_elem _ = false;

(*Try solving a:A by assumption provided a is rigid!*) 
val test_assume_tac = SUBGOAL(fn (prem,i) =>
    if is_rigid_elem (Logic.strip_assums_concl prem)
    then  assume_tac i  else  no_tac);

fun ASSUME tf i = test_assume_tac i  ORELSE  tf i;


(*For simplification: type formation and checking,
  but no equalities between terms*)
val routine_rls = form_rls @ formL_rls @ [refl_type] @ element_rls;

fun routine_tac rls prems = ASSUME (filt_resolve_tac (prems @ rls) 4);


(*Solve all subgoals "A type" using formation rules. *)
val form_tac = REPEAT_FIRST (filt_resolve_tac(form_rls) 1);


(*Type checking: solve a:A (a rigid, A flexible) by intro and elim rules. *)
fun typechk_tac thms =
  let val tac = filt_resolve_tac (thms @ form_rls @ element_rls) 3
  in  REPEAT_FIRST (ASSUME tac)  end;


(*Solve a:A (a flexible, A rigid) by introduction rules. 
  Cannot use stringtrees (filt_resolve_tac) since
  goals like ?a:SUM(A,B) have a trivial head-string *)
fun intr_tac thms =
  let val tac = filt_resolve_tac(thms@form_rls@intr_rls) 1
  in  REPEAT_FIRST (ASSUME tac)  end;


(*Equality proving: solve a=b:A (where a is rigid) by long rules. *)
fun equal_tac thms =
  let val rls = thms @ form_rls @ element_rls @ intrL_rls @
                elimL_rls @ [refl_elem]
  in  REPEAT_FIRST (ASSUME (filt_resolve_tac rls 3))  end;

(*** Simplification ***)

(*To simplify the type in a goal*)
qed_goal "replace_type" CTT.thy
    "[| B = A;  a : A |] ==> a : B"
 (fn prems=>
  [ (resolve_tac [equal_types] 1),
    (resolve_tac [sym_type] 2),
    (ALLGOALS (resolve_tac prems)) ]);

(*Simplify the parameter of a unary type operator.*)
qed_goal "subst_eqtyparg" CTT.thy
    "a=c : A ==> (!!z.z:A ==> B(z) type) ==> B(a)=B(c)"
 (fn prems=>
  [ (resolve_tac [subst_typeL] 1),
    (resolve_tac [refl_type] 2),
    (ALLGOALS (resolve_tac prems)),
    (assume_tac 1) ]);

(*Make a reduction rule for simplification.
  A goal a=c becomes b=c, by virtue of a=b *)
fun resolve_trans rl = rl RS trans_elem;

(*Simplification rules for Constructive Type Theory*)
val reduction_rls = map resolve_trans comp_rls;

(*Converts each goal "e : Eq(A,a,b)" into "a=b:A" for simplification.
  Uses other intro rules to avoid changing flexible goals.*)
val eqintr_tac = REPEAT_FIRST (ASSUME (filt_resolve_tac(EqI::intr_rls) 1));

(** Tactics that instantiate CTT-rules.
    Vars in the given terms will be incremented! 
    The (resolve_tac [EqE] i) lets them apply to equality judgements. **)

fun NE_tac (sp: string) i = 
  TRY (resolve_tac [EqE] i) THEN res_inst_tac [ ("p",sp) ] NE i;

fun SumE_tac (sp: string) i = 
  TRY (resolve_tac [EqE] i) THEN res_inst_tac [ ("p",sp) ] SumE i;

fun PlusE_tac (sp: string) i = 
  TRY (resolve_tac [EqE] i) THEN res_inst_tac [ ("p",sp) ] PlusE i;

(** Predicate logic reasoning, WITH THINNING!!  Procedures adapted from NJ. **)

(*Finds f:Prod(A,B) and a:A in the assumptions, concludes there is z:B(a) *)
fun add_mp_tac i = 
    resolve_tac [subst_prodE] i  THEN  assume_tac i  THEN  assume_tac i;

(*Finds P-->Q and P in the assumptions, replaces implication by Q *)
fun mp_tac i = eresolve_tac [subst_prodE] i  THEN  assume_tac i;

(*"safe" when regarded as predicate calculus rules*)
val safe_brls = sort lessb 
    [ (true,FE), (true,asm_rl), 
      (false,ProdI), (true,SumE), (true,PlusE) ];

val unsafe_brls =
    [ (false,PlusI_inl), (false,PlusI_inr), (false,SumI), 
      (true,subst_prodE) ];

(*0 subgoals vs 1 or more*)
val (safe0_brls, safep_brls) =
    partition (apl(0,op=) o subgoals_of_brl) safe_brls;

fun safestep_tac thms i =
    form_tac  ORELSE  
    resolve_tac thms i  ORELSE
    biresolve_tac safe0_brls i  ORELSE  mp_tac i  ORELSE
    DETERM (biresolve_tac safep_brls i);

fun safe_tac thms i = DEPTH_SOLVE_1 (safestep_tac thms i); 

fun step_tac thms = safestep_tac thms  ORELSE'  biresolve_tac unsafe_brls;

(*Fails unless it solves the goal!*)
fun pc_tac thms = DEPTH_SOLVE_1 o (step_tac thms);

(** The elimination rules for fst/snd **)

qed_goalw "SumE_fst" CTT.thy basic_defs
    "p : Sum(A,B) ==> fst(p) : A"
 (fn [major] =>
  [ (rtac (major RS SumE) 1),
    (assume_tac 1) ]);

(*The first premise must be p:Sum(A,B) !!*)
qed_goalw "SumE_snd" CTT.thy basic_defs
    "[| p: Sum(A,B);  A type;  !!x. x:A ==> B(x) type \
\    |] ==> snd(p) : B(fst(p))"
 (fn major::prems=>
  [ (rtac (major RS SumE) 1),
    (resolve_tac [SumC RS subst_eqtyparg RS replace_type] 1),
    (typechk_tac prems) ]);
