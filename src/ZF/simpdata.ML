(*  Title:      ZF/simpdata
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Rewriting for ZF set theory -- based on FOL rewriting
*)

fun prove_fun s = 
    (writeln s;  prove_goal ZF.thy s
       (fn prems => [ (cut_facts_tac prems 1), (fast_tac ZF_cs 1) ]));

val mem_rews = map prove_fun
 [ "a:0 <-> False",
   "a : A Un B <-> a:A | a:B",
   "a : A Int B <-> a:A & a:B",
   "a : A-B <-> a:A & ~a:B",
   "a : cons(b,B) <-> a=b | a:B",
   "i : succ(j) <-> i=j | i:j",
   "<a,b>: Sigma(A,B) <-> a:A & b:B(a)",
   "a : Collect(A,P) <-> a:A & P(a)" ];

(** Tactics for type checking -- from CTT **)

fun is_rigid_elem (Const("Trueprop",_) $ (Const("op :",_) $ a $ _)) = 
      not (is_Var (head_of a))
  | is_rigid_elem _ = false;

(*Try solving a:A by assumption provided a is rigid!*) 
val test_assume_tac = SUBGOAL(fn (prem,i) =>
    if is_rigid_elem (Logic.strip_assums_concl prem)
    then  assume_tac i  else  no_tac);

(*Type checking solves a:?A (a rigid, ?A maybe flexible).  
  match_tac is too strict; would refuse to instantiate ?A*)
fun typechk_step_tac tyrls =
    FIRSTGOAL (test_assume_tac ORELSE' filt_resolve_tac tyrls 3);

fun typechk_tac tyrls = REPEAT (typechk_step_tac tyrls);

val ZF_typechecks = [if_type,lam_type,SigmaI,apply_type,split_type];

(*To instantiate variables in typing conditions; 
  to perform type checking faster than rewriting can
  NOT TERRIBLY USEFUL because it does not simplify conjunctions*)
fun type_auto_tac tyrls hyps = SELECT_GOAL
    (DEPTH_SOLVE (typechk_step_tac (tyrls@hyps)
           ORELSE ares_tac [TrueI,ballI,allI,conjI,impI] 1));

(** New version of mk_rew_rules **)

(*Should False yield False<->True, or should it solve goals some other way?*)

(*Analyse a rigid formula*)
val atomize_pairs =
  [("Ball",	[bspec]), 
   ("All",	[spec]),
   ("op -->",	[mp]),
   ("op &",	[conjunct1,conjunct2])];

(*Analyse a:b, where b is rigid*)
val atomize_mem_pairs = 
  [("Collect",	[CollectD1,CollectD2]),
   ("op -",	[DiffD1,DiffD2]),
   ("op Int",	[IntD1,IntD2])];

(*Analyse a theorem to atomic rewrite rules*)
fun atomize th = 
  let fun tryrules pairs t =
	  case head_of t of
	      Const(a,_) => 
		(case assoc(pairs,a) of
		     Some rls => flat (map atomize ([th] RL rls))
		   | None     => [th])
	    | _ => [th]
  in case concl_of th of (*The operator below is Trueprop*)
	_ $ (Const("op :",_) $ a $ b) => tryrules atomize_mem_pairs b
      | _ $ (Const("True",_)) => []	(*True is DELETED*)
      | _ $ (Const("False",_)) => []	(*should False do something??*)
      | _ $ A => tryrules atomize_pairs A
  end;

fun ZF_mk_rew_rules th = map mk_eq (atomize th);


fun auto_tac rls hyps = SELECT_GOAL (DEPTH_SOLVE_1 (ares_tac (rls@hyps) 1));

structure ZF_SimpData : SIMP_DATA =
  struct
  val refl_thms		= FOL_SimpData.refl_thms
  val trans_thms	= FOL_SimpData.trans_thms
  val red1		= FOL_SimpData.red1
  val red2		= FOL_SimpData.red2
  val mk_rew_rules	= ZF_mk_rew_rules 
  val norm_thms		= FOL_SimpData.norm_thms
  val subst_thms	= FOL_SimpData.subst_thms
  val dest_red		= FOL_SimpData.dest_red
  end;

structure ZF_Simp = SimpFun(ZF_SimpData);

open ZF_Simp;

(*Redeclared because the previous FOL_ss belongs to a different instance
  of type simpset*)
val FOL_ss = empty_ss addcongs FOL_congs addrews FOL_rews 
		      setauto auto_tac[TrueI,ballI];

(** Basic congruence and rewrite rules for ZF set theory **)

val ZF_congs = 
   [ball_cong,bex_cong,Replace_cong,RepFun_cong,Collect_cong,the_cong,
    if_cong,Sigma_cong,split_cong,Pi_cong,lam_cong] @ basic_ZF_congs;

val ZF_rews = [empty_subsetI, ball_rew, if_true, if_false, 
	       beta, eta, restrict,
	       fst_conv, snd_conv, split];

val ZF_ss = FOL_ss addcongs ZF_congs addrews (ZF_rews@mem_rews);

