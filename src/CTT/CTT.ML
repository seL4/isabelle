(*  Title:      CTT/CTT.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Tactics and derived rules for Constructive Type Theory
*)

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
Goal "[| c=a : A;  d=b : B(a) |] ==> <c,d> = <a,b> : Sum(A,B)";
by (rtac sym_elem 1);
by (rtac SumIL 1);
by (ALLGOALS (rtac sym_elem ));
by (ALLGOALS assume_tac) ;
qed "SumIL2";

val intrL2_rls = [NI_succL, ProdIL, SumIL2, PlusI_inlL, PlusI_inrL];

(*Exploit p:Prod(A,B) to create the assumption z:B(a).  
  A more natural form of product elimination. *)
val prems = Goal "[| p: Prod(A,B);  a: A;  !!z. z: B(a) ==> c(z): C(z) \
\    |] ==> c(p`a): C(p`a)";
by (REPEAT (resolve_tac (ProdE::prems) 1)) ;
qed "subst_prodE";

(** Tactics for type checking **)

fun is_rigid_elem (Const("CTT.Elem",_) $ a $ _) = not(is_Var (head_of a))
  | is_rigid_elem (Const("CTT.Eqelem",_) $ a $ _ $ _) = not(is_Var (head_of a))
  | is_rigid_elem (Const("CTT.Type",_) $ a) = not(is_Var (head_of a))
  | is_rigid_elem _ = false;

(*Try solving a:A or a=b:A by assumption provided a is rigid!*) 
val test_assume_tac = SUBGOAL(fn (prem,i) =>
    if is_rigid_elem (Logic.strip_assums_concl prem)
    then  assume_tac i  else  no_tac);

fun ASSUME tf i = test_assume_tac i  ORELSE  tf i;


(*For simplification: type formation and checking,
  but no equalities between terms*)
val routine_rls = form_rls @ formL_rls @ [refl_type] @ element_rls;

fun routine_tac rls prems = ASSUME (filt_resolve_tac (prems @ rls) 4);


(*Solve all subgoals "A type" using formation rules. *)
val form_tac = REPEAT_FIRST (ASSUME (filt_resolve_tac(form_rls) 1));


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
Goal "[| B = A;  a : A |] ==> a : B";
by (rtac equal_types 1);
by (rtac sym_type 2);
by (ALLGOALS assume_tac) ;
qed "replace_type";

(*Simplify the parameter of a unary type operator.*)
val prems = Goal
     "[| a=c : A;  !!z. z:A ==> B(z) type |] ==> B(a)=B(c)";
by (rtac subst_typeL 1);
by (rtac refl_type 2);
by (ALLGOALS (resolve_tac prems));
by (assume_tac 1) ;
qed "subst_eqtyparg";

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
    The (rtac EqE i) lets them apply to equality judgements. **)

fun NE_tac (sp: string) i = 
  TRY (rtac EqE i) THEN res_inst_tac [ ("p",sp) ] NE i;

fun SumE_tac (sp: string) i = 
  TRY (rtac EqE i) THEN res_inst_tac [ ("p",sp) ] SumE i;

fun PlusE_tac (sp: string) i = 
  TRY (rtac EqE i) THEN res_inst_tac [ ("p",sp) ] PlusE i;

(** Predicate logic reasoning, WITH THINNING!!  Procedures adapted from NJ. **)

(*Finds f:Prod(A,B) and a:A in the assumptions, concludes there is z:B(a) *)
fun add_mp_tac i = 
    rtac subst_prodE i  THEN  assume_tac i  THEN  assume_tac i;

(*Finds P-->Q and P in the assumptions, replaces implication by Q *)
fun mp_tac i = etac subst_prodE i  THEN  assume_tac i;

(*"safe" when regarded as predicate calculus rules*)
val safe_brls = sort (make_ord lessb)
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

Goalw basic_defs "p : Sum(A,B) ==> fst(p) : A";
by (etac SumE 1);
by (assume_tac 1);
qed "SumE_fst";

(*The first premise must be p:Sum(A,B) !!*)
val major::prems= Goalw basic_defs
    "[| p: Sum(A,B);  A type;  !!x. x:A ==> B(x) type \
\    |] ==> snd(p) : B(fst(p))";
by (rtac (major RS SumE) 1);
by (resolve_tac [SumC RS subst_eqtyparg RS replace_type] 1);
by (typechk_tac prems) ;
qed "SumE_snd";
