(*  Title:      HOLCF/Dnat.thy
    ID:         $Id$
    Author:     Franz Regensburger
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Theory for the domain of natural numbers  dnat = one ++ dnat
*)

theory Dnat = HOLCF:

domain dnat = dzero | dsucc (dpred :: dnat)

constdefs
  iterator :: "dnat -> ('a -> 'a) -> 'a -> 'a"
  "iterator == fix $ (LAM h n f x.
    case n of dzero => x
      | dsucc $ m => f $ (h $ m $ f $ x))"

text {*
  \medskip Expand fixed point properties.
*}

ML_setup {*
bind_thm ("iterator_def2", fix_prover2 (the_context ()) (thm "iterator_def")
        "iterator = (LAM n f x. case n of dzero => x | dsucc$m => f$(iterator$m$f$x))");
*}

text {*
  \medskip Recursive properties.
*}

lemma iterator1: "iterator $ UU $ f $ x = UU"
  apply (subst iterator_def2)
  apply (simp add: dnat.rews)
  done

lemma iterator2: "iterator $ dzero $ f $ x = x"
  apply (subst iterator_def2)
  apply (simp add: dnat.rews)
  done

lemma iterator3: "n ~= UU ==> iterator $ (dsucc $ n) $ f $ x = f $ (iterator $ n $ f $ x)"
  apply (rule trans)
   apply (subst iterator_def2)
   apply (simp add: dnat.rews)
  apply (rule refl)
  done

lemmas iterator_rews = iterator1 iterator2 iterator3

lemma dnat_flat: "ALL x y::dnat. x<<y --> x=UU | x=y"
  apply (rule allI)
  apply (induct_tac x rule: dnat.ind)
    apply fast
   apply (rule allI)
   apply (rule_tac x = y in dnat.casedist)
     apply (fast intro!: UU_I)
    apply simp
   apply (simp add: dnat.dist_les)
  apply (rule allI)
  apply (rule_tac x = y in dnat.casedist)
    apply (fast intro!: UU_I)
   apply (simp add: dnat.dist_les)
  apply (simp (no_asm_simp) add: dnat.rews)
  apply (intro strip)
  apply (subgoal_tac "d << da")
   apply (erule allE)
   apply (drule mp)
    apply assumption
   apply (erule disjE)
    apply (tactic "contr_tac 1")
   apply simp
  apply (erule (2) dnat.inverts)
  done

end
