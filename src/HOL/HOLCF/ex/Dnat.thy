(*  Title:      HOL/HOLCF/ex/Dnat.thy
    Author:     Franz Regensburger

Theory for the domain of natural numbers  dnat = one ++ dnat
*)

theory Dnat
imports HOLCF
begin

domain dnat = dzero | dsucc (dpred :: dnat)

definition
  iterator :: "dnat -> ('a -> 'a) -> 'a -> 'a" where
  "iterator = fix $ (LAM h n f x.
    case n of dzero => x
      | dsucc $ m => f $ (h $ m $ f $ x))"

text {*
  \medskip Expand fixed point properties.
*}

lemma iterator_def2:
  "iterator = (LAM n f x. case n of dzero => x | dsucc$m => f$(iterator$m$f$x))"
  apply (rule trans)
  apply (rule fix_eq2)
  apply (rule iterator_def [THEN eq_reflection])
  apply (rule beta_cfun)
  apply simp
  done

text {* \medskip Recursive properties. *}

lemma iterator1: "iterator $ UU $ f $ x = UU"
  apply (subst iterator_def2)
  apply simp
  done

lemma iterator2: "iterator $ dzero $ f $ x = x"
  apply (subst iterator_def2)
  apply simp
  done

lemma iterator3: "n ~= UU ==> iterator $ (dsucc $ n) $ f $ x = f $ (iterator $ n $ f $ x)"
  apply (rule trans)
   apply (subst iterator_def2)
   apply simp
  apply (rule refl)
  done

lemmas iterator_rews = iterator1 iterator2 iterator3

lemma dnat_flat: "ALL x y::dnat. x<<y --> x=UU | x=y"
  apply (rule allI)
  apply (induct_tac x)
    apply fast
   apply (rule allI)
   apply (case_tac y)
     apply simp
    apply simp
   apply simp
  apply (rule allI)
  apply (case_tac y)
    apply (fast intro!: bottomI)
   apply (thin_tac "ALL y. dnat << y --> dnat = UU | dnat = y")
   apply simp
  apply (simp (no_asm_simp))
  apply (drule_tac x="dnata" in spec)
  apply simp
  done

end
