(*  Title:      ZF/simpdata
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Rewriting for ZF set theory -- based on FOL rewriting
*)

(** Tactics for type checking -- from CTT **)

fun is_rigid_elem (Const("Trueprop",_) $ (Const("op :",_) $ a $ _)) = 
      not (is_Var (head_of a))
  | is_rigid_elem _ = false;

(*Try solving a:A by assumption provided a is rigid!*) 
val test_assume_tac = SUBGOAL(fn (prem,i) =>
    if is_rigid_elem (Logic.strip_assums_concl prem)
    then  assume_tac i  else  eq_assume_tac i);

(*Type checking solves a:?A (a rigid, ?A maybe flexible).  
  match_tac is too strict; would refuse to instantiate ?A*)
fun typechk_step_tac tyrls =
    FIRSTGOAL (test_assume_tac ORELSE' filt_resolve_tac tyrls 3);

fun typechk_tac tyrls = REPEAT (typechk_step_tac tyrls);

val ZF_typechecks =
    [if_type, lam_type, SigmaI, apply_type, split_type, consI1];

(*Instantiates variables in typing conditions.
  drawback: does not simplify conjunctions*)
fun type_auto_tac tyrls hyps = SELECT_GOAL
    (DEPTH_SOLVE (typechk_step_tac (tyrls@hyps)
           ORELSE ares_tac [TrueI,refl,iff_refl,ballI,allI,conjI,impI] 1));

(** New version of mk_rew_rules **)

(*Should False yield False<->True, or should it solve goals some other way?*)

(*Analyse a theorem to atomic rewrite rules*)
fun atomize (conn_pairs, mem_pairs) th = 
  let fun tryrules pairs t =
          case head_of t of
              Const(a,_) => 
                (case assoc(pairs,a) of
                     Some rls => flat (map (atomize (conn_pairs, mem_pairs))
                                       ([th] RL rls))
                   | None     => [th])
            | _ => [th]
  in case concl_of th of 
         Const("Trueprop",_) $ P => 
            (case P of
                 Const("op :",_) $ a $ b => tryrules mem_pairs b
               | Const("True",_)         => []
               | Const("False",_)        => []
               | A => tryrules conn_pairs A)
       | _                       => [th]
  end;

(*Analyse a rigid formula*)
val ZF_conn_pairs =
  [("Ball",     [bspec]), 
   ("All",      [spec]),
   ("op -->",   [mp]),
   ("op &",     [conjunct1,conjunct2])];

(*Analyse a:b, where b is rigid*)
val ZF_mem_pairs = 
  [("Collect",  [CollectD1,CollectD2]),
   ("op -",     [DiffD1,DiffD2]),
   ("op Int",   [IntD1,IntD2])];

val ZF_simps = 
    [empty_subsetI, consI1, succI1, ball_simp, if_true, if_false, 
     beta, eta, restrict, fst_conv, snd_conv, split, Pair_iff, singleton_iff,
     Sigma_empty1, Sigma_empty2, triv_RepFun, subset_refl];

(*Sigma_cong, Pi_cong NOT included by default since they cause
  flex-flex pairs and the "Check your prover" error -- because most
  Sigma's and Pi's are abbreviated as * or -> *)
val ZF_congs =
   [ball_cong, bex_cong, Replace_cong, RepFun_cong, Collect_cong, lam_cong];

val ZF_atomize = atomize (ZF_conn_pairs, ZF_mem_pairs);

val ZF_ss = FOL_ss 
      setmksimps (map mk_meta_eq o ZF_atomize o gen_all)
      addsimps (ZF_simps @ mem_simps @ bquant_simps @ 
                Collect_simps @ UnInt_simps)
      addcongs ZF_congs;
