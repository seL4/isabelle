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

val ZF_atomize = atomize (ZF_conn_pairs, ZF_mem_pairs);

simpset_ref() :=
  simpset() setmksimps (map mk_eq o ZF_atomize o gen_all)
  addcongs [if_weak_cong]
  setSolver (mk_solver "types" (fn prems => TCSET' (fn tcset => type_solver_tac tcset prems)));



local

val prove_bex_tac = rewtac Bex_def THEN Quantifier1.prove_one_point_ex_tac;
val rearrange_bex = Quantifier1.rearrange_bex prove_bex_tac;

val prove_ball_tac = rewtac Ball_def THEN Quantifier1.prove_one_point_all_tac;
val rearrange_ball = Quantifier1.rearrange_ball prove_ball_tac;

in

val defBEX_regroup = Simplifier.simproc (Theory.sign_of (the_context ()))
  "defined BEX" ["EX x:A. P(x) & Q(x)"] rearrange_bex;

val defBALL_regroup = Simplifier.simproc (Theory.sign_of (the_context ()))
  "defined BALL" ["ALL x:A. P(x) --> Q(x)"] rearrange_ball;

end;

Addsimprocs [defBALL_regroup, defBEX_regroup];


val ZF_ss = simpset();
