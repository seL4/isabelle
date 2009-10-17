(*  Title:      ZF/simpdata
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Rewriting for ZF set theory: specialized extraction of rewrites from theorems
*)

(*** New version of mk_rew_rules ***)

(*Should False yield False<->True, or should it solve goals some other way?*)

(*Analyse a theorem to atomic rewrite rules*)
fun atomize (conn_pairs, mem_pairs) th =
  let fun tryrules pairs t =
          case head_of t of
              Const(a,_) =>
                (case AList.lookup (op =) pairs a of
                     SOME rls => maps (atomize (conn_pairs, mem_pairs)) ([th] RL rls)
                   | NONE => [th])
            | _ => [th]
  in case concl_of th of
         Const("Trueprop",_) $ P =>
            (case P of
                 Const(@{const_name mem},_) $ a $ b => tryrules mem_pairs b
               | Const("True",_)         => []
               | Const("False",_)        => []
               | A => tryrules conn_pairs A)
       | _                       => [th]
  end;

(*Analyse a rigid formula*)
val ZF_conn_pairs =
  [("Ball",     [@{thm bspec}]),
   ("All",      [spec]),
   ("op -->",   [mp]),
   ("op &",     [conjunct1,conjunct2])];

(*Analyse a:b, where b is rigid*)
val ZF_mem_pairs =
  [("Collect",  [@{thm CollectD1}, @{thm CollectD2}]),
   (@{const_name Diff},     [@{thm DiffD1}, @{thm DiffD2}]),
   (@{const_name Int},   [@{thm IntD1}, @{thm IntD2}])];

val ZF_atomize = atomize (ZF_conn_pairs, ZF_mem_pairs);

change_simpset (fn ss =>
  ss setmksimps (map mk_eq o ZF_atomize o gen_all)
  addcongs [@{thm if_weak_cong}]);

local

val unfold_bex_tac = unfold_tac [@{thm Bex_def}];
fun prove_bex_tac ss = unfold_bex_tac ss THEN Quantifier1.prove_one_point_ex_tac;
val rearrange_bex = Quantifier1.rearrange_bex prove_bex_tac;

val unfold_ball_tac = unfold_tac [@{thm Ball_def}];
fun prove_ball_tac ss = unfold_ball_tac ss THEN Quantifier1.prove_one_point_all_tac;
val rearrange_ball = Quantifier1.rearrange_ball prove_ball_tac;

in

val defBEX_regroup = Simplifier.simproc (Theory.deref @{theory_ref})
  "defined BEX" ["EX x:A. P(x) & Q(x)"] rearrange_bex;

val defBALL_regroup = Simplifier.simproc (Theory.deref @{theory_ref})
  "defined BALL" ["ALL x:A. P(x) --> Q(x)"] rearrange_ball;

end;

Addsimprocs [defBALL_regroup, defBEX_regroup];


val ZF_ss = @{simpset};

