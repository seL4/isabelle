(*  Title:      HOLCF/Dnat.thy
    ID:         $Id$
    Author:     Franz Regensburger

Theory for the domain of natural numbers  dnat = one ++ dnat
*)

theory Dnat imports HOLCF begin

domain dnat = dzero | dsucc (dpred :: dnat)

definition
  iterator :: "dnat -> ('a -> 'a) -> 'a -> 'a"
  "iterator = fix $ (LAM h n f x.
    case n of dzero => x
      | dsucc $ m => f $ (h $ m $ f $ x))"

text {*
  \medskip Expand fixed point properties.
*}

ML_setup {*
bind_thm ("iterator_def2", fix_prover2 (the_context ()) (thm "iterator_def" RS eq_reflection)
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
     apply simp
    apply simp
   apply (simp add: dnat.dist_les)
  apply (rule allI)
  apply (rule_tac x = y in dnat.casedist)
    apply (fast intro!: UU_I)
   apply (thin_tac "ALL y. d << y --> d = UU | d = y")
   apply (simp add: dnat.dist_les)
  apply (simp (no_asm_simp) add: dnat.rews dnat.injects dnat.inverts)
  apply (drule_tac x="da" in spec)
  apply simp
  done

end
