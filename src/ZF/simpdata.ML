(*  Title:      ZF/simpdata.ML
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Rewriting for ZF set theory: specialized extraction of rewrites from theorems.
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
  in case Thm.concl_of th of
         Const(@{const_name Trueprop},_) $ P =>
            (case P of
                 Const(@{const_name mem},_) $ a $ b => tryrules mem_pairs b
               | Const(@{const_name True},_)         => []
               | Const(@{const_name False},_)        => []
               | A => tryrules conn_pairs A)
       | _                       => [th]
  end;

(*Analyse a rigid formula*)
val ZF_conn_pairs =
  [(@{const_name Ball}, [@{thm bspec}]),
   (@{const_name All}, [@{thm spec}]),
   (@{const_name imp}, [@{thm mp}]),
   (@{const_name conj}, [@{thm conjunct1}, @{thm conjunct2}])];

(*Analyse a:b, where b is rigid*)
val ZF_mem_pairs =
  [(@{const_name Collect}, [@{thm CollectD1}, @{thm CollectD2}]),
   (@{const_name Diff}, [@{thm DiffD1}, @{thm DiffD2}]),
   (@{const_name Int}, [@{thm IntD1}, @{thm IntD2}])];

val ZF_atomize = atomize (ZF_conn_pairs, ZF_mem_pairs);

