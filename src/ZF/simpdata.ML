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
         \<^Const_>\<open>Trueprop for P\<close> =>
            (case P of
                 \<^Const_>\<open>mem for a b\<close> => tryrules mem_pairs b
               | \<^Const_>\<open>True\<close> => []
               | \<^Const_>\<open>False\<close> => []
               | A => tryrules conn_pairs A)
       | _                       => [th]
  end;

(*Analyse a rigid formula*)
val ZF_conn_pairs =
  [(\<^const_name>\<open>Ball\<close>, [@{thm bspec}]),
   (\<^const_name>\<open>All\<close>, [@{thm spec}]),
   (\<^const_name>\<open>imp\<close>, [@{thm mp}]),
   (\<^const_name>\<open>conj\<close>, [@{thm conjunct1}, @{thm conjunct2}])];

(*Analyse a:b, where b is rigid*)
val ZF_mem_pairs =
  [(\<^const_name>\<open>Collect\<close>, [@{thm CollectD1}, @{thm CollectD2}]),
   (\<^const_name>\<open>Diff\<close>, [@{thm DiffD1}, @{thm DiffD2}]),
   (\<^const_name>\<open>Int\<close>, [@{thm IntD1}, @{thm IntD2}])];

val ZF_atomize = atomize (ZF_conn_pairs, ZF_mem_pairs);

