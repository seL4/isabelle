(*  Title:      ZF/simpdata
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Rewriting for ZF set theory -- based on FOL rewriting
*)

fun prove_fun s = 
    (writeln s;  prove_goal ZF.thy s
       (fn prems => [ (cut_facts_tac prems 1), (fast_tac ZF_cs 1) ]));

(*INCLUDED IN ZF_ss*)
val mem_simps = map prove_fun
 [ "a : 0             <-> False",
   "a : A Un B        <-> a:A | a:B",
   "a : A Int B       <-> a:A & a:B",
   "a : A-B           <-> a:A & ~a:B",
   "<a,b>: Sigma(A,B) <-> a:A & b:B(a)",
   "a : Collect(A,P)  <-> a:A & P(a)" ];

(*INCLUDED: should be??*)
val bquant_simps = map prove_fun
 [ "(ALL x:0.P(x)) <-> True",
   "(EX  x:0.P(x)) <-> False",
   "(ALL x:succ(i).P(x)) <-> P(i) & (ALL x:i.P(x))",
   "(EX  x:succ(i).P(x)) <-> P(i) | (EX  x:i.P(x))" ];

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
           ORELSE ares_tac [TrueI,refl,iff_refl,ballI,allI,conjI,impI] 1));

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
  in case concl_of th of 
       Const("Trueprop",_) $ P => 
	  (case P of
	       Const("op :",_) $ a $ b => tryrules atomize_mem_pairs b
	     | Const("True",_)         => []
	     | Const("False",_)        => []
	     | A => tryrules atomize_pairs A)
     | _                       => [th]
  end;

val ZF_simps = [empty_subsetI, consI1, succI1, ball_simp, if_true, if_false, 
		beta, eta, restrict, fst_conv, snd_conv, split, Pair_iff];

(*Sigma_cong, Pi_cong NOT included by default since they cause
  flex-flex pairs and the "Check your prover" error -- because most
  Sigma's and Pi's are abbreviated as * or -> *)
val ZF_congs =
   [ball_cong, bex_cong, Replace_cong, RepFun_cong, Collect_cong, lam_cong];

val ZF_ss = FOL_ss 
      setmksimps (map mk_meta_eq o atomize o gen_all)
      addsimps (ZF_simps @ mem_simps @ bquant_simps)
      addcongs ZF_congs;
