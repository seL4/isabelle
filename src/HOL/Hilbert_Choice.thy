(*  Title:      HOL/Hilbert_Choice.thy
    ID:         $Id$
    Author:     Lawrence C Paulson
    Copyright   2001  University of Cambridge

Hilbert's epsilon-operator and everything to do with the Axiom of Choice
*)

theory Hilbert_Choice = NatArith
files ("Hilbert_Choice_lemmas.ML") ("meson_lemmas.ML") ("Tools/meson.ML"):

consts
  Eps           :: "('a => bool) => 'a"


syntax (input)
  "_Eps"        :: "[pttrn, bool] => 'a"                 ("(3\<epsilon>_./ _)" [0, 10] 10)

syntax (HOL)
  "_Eps"        :: "[pttrn, bool] => 'a"                 ("(3@ _./ _)" [0, 10] 10)

syntax
  "_Eps"        :: "[pttrn, bool] => 'a"                 ("(3SOME _./ _)" [0, 10] 10)

translations
  "SOME x. P"             == "Eps (%x. P)"

axioms  
  someI:        "P (x::'a) ==> P (SOME x. P x)"


(*used in TFL*)
lemma tfl_some: "\<forall>P x. P x --> P (Eps P)"
  by (blast intro: someI)


constdefs  
  inv :: "('a => 'b) => ('b => 'a)"
    "inv(f::'a=>'b) == % y. @x. f(x)=y"

  Inv :: "['a set, 'a => 'b] => ('b => 'a)"
    "Inv A f == (% x. (@ y. y : A & f y = x))"


use "Hilbert_Choice_lemmas.ML"


(** Least value operator **)

constdefs
  LeastM   :: "['a => 'b::ord, 'a => bool] => 'a"
              "LeastM m P == @x. P x & (ALL y. P y --> m x <= m y)"

syntax
 "@LeastM" :: "[pttrn, 'a=>'b::ord, bool] => 'a" ("LEAST _ WRT _. _" [0,4,10]10)

translations
                "LEAST x WRT m. P" == "LeastM m (%x. P)"

lemma LeastMI2:
  "[| P x; !!y. P y ==> m x <= m y;
           !!x. [| P x; \<forall>y. P y --> m x \<le> m y |] ==> Q x |]
   ==> Q (LeastM m P)";
apply (unfold LeastM_def)
apply (rule someI2_ex)
apply  blast
apply blast
done

lemma LeastM_equality:
 "[| P k; !!x. P x ==> m k <= m x |] ==> m (LEAST x WRT m. P x) = 
     (m k::'a::order)";
apply (rule LeastMI2)
apply   assumption
apply  blast
apply (blast intro!: order_antisym) 
done

lemma wf_linord_ex_has_least:
     "[|wf r;  ALL x y. ((x,y):r^+) = ((y,x)~:r^*);  P k|]  \
\     ==> EX x. P x & (!y. P y --> (m x,m y):r^*)" 
apply (drule wf_trancl [THEN wf_eq_minimal [THEN iffD1]])
apply (drule_tac x = "m`Collect P" in spec)
apply force
done

(* successor of obsolete nonempty_has_least *)
lemma ex_has_least_nat:
     "P k ==> EX x. P x & (ALL y. P y --> m x <= (m y::nat))"
apply (simp only: pred_nat_trancl_eq_le [symmetric])
apply (rule wf_pred_nat [THEN wf_linord_ex_has_least])
apply (simp (no_asm) add: less_eq not_le_iff_less pred_nat_trancl_eq_le)
apply assumption
done

lemma LeastM_nat_lemma: 
  "P k ==> P (LeastM m P) & (ALL y. P y --> m (LeastM m P) <= (m y::nat))"
apply (unfold LeastM_def)
apply (rule someI_ex)
apply (erule ex_has_least_nat)
done

lemmas LeastM_natI = LeastM_nat_lemma [THEN conjunct1, standard]

lemma LeastM_nat_le: "P x ==> m (LeastM m P) <= (m x::nat)"
apply (rule LeastM_nat_lemma [THEN conjunct2, THEN spec, THEN mp])
apply assumption
apply assumption
done


(** Greatest value operator **)

constdefs
  GreatestM   :: "['a => 'b::ord, 'a => bool] => 'a"
              "GreatestM m P == @x. P x & (ALL y. P y --> m y <= m x)"
  
  Greatest    :: "('a::ord => bool) => 'a"         (binder "GREATEST " 10)
              "Greatest     == GreatestM (%x. x)"

syntax
 "@GreatestM" :: "[pttrn, 'a=>'b::ord, bool] => 'a"
                                        ("GREATEST _ WRT _. _" [0,4,10]10)

translations
              "GREATEST x WRT m. P" == "GreatestM m (%x. P)"

lemma GreatestMI2:
     "[| P x;
	 !!y. P y ==> m y <= m x;
         !!x. [| P x; \<forall>y. P y --> m y \<le> m x |] ==> Q x |]
      ==> Q (GreatestM m P)";
apply (unfold GreatestM_def)
apply (rule someI2_ex)
apply  blast
apply blast
done

lemma GreatestM_equality:
 "[| P k;  !!x. P x ==> m x <= m k |]
  ==> m (GREATEST x WRT m. P x) = (m k::'a::order)";
apply (rule_tac m=m in GreatestMI2)
apply   assumption
apply  blast
apply (blast intro!: order_antisym) 
done

lemma Greatest_equality:
  "[| P (k::'a::order); !!x. P x ==> x <= k |] ==> (GREATEST x. P x) = k";
apply (unfold Greatest_def)
apply (erule GreatestM_equality)
apply blast
done

lemma ex_has_greatest_nat_lemma:
     "[|P k;  ALL x. P x --> (EX y. P y & ~ ((m y::nat) <= m x))|]  
      ==> EX y. P y & ~ (m y < m k + n)"
apply (induct_tac "n")
apply force
(*ind step*)
apply (force simp add: le_Suc_eq)
done

lemma ex_has_greatest_nat: "[|P k;  ! y. P y --> m y < b|]  
      ==> ? x. P x & (! y. P y --> (m y::nat) <= m x)"
apply (rule ccontr)
apply (cut_tac P = "P" and n = "b - m k" in ex_has_greatest_nat_lemma)
apply (subgoal_tac [3] "m k <= b")
apply auto
done

lemma GreatestM_nat_lemma: 
     "[|P k;  ! y. P y --> m y < b|]  
      ==> P (GreatestM m P) & (!y. P y --> (m y::nat) <= m (GreatestM m P))"
apply (unfold GreatestM_def)
apply (rule someI_ex)
apply (erule ex_has_greatest_nat)
apply assumption
done

lemmas GreatestM_natI = GreatestM_nat_lemma [THEN conjunct1, standard]

lemma GreatestM_nat_le: "[|P x;  ! y. P y --> m y < b|]  
      ==> (m x::nat) <= m (GreatestM m P)"
apply (blast dest: GreatestM_nat_lemma [THEN conjunct2, THEN spec]) 
done

(** Specialization to GREATEST **)

lemma GreatestI: 
     "[|P (k::nat);  ! y. P y --> y < b|] ==> P (GREATEST x. P x)"

apply (unfold Greatest_def)
apply (rule GreatestM_natI)
apply auto
done

lemma Greatest_le: 
     "[|P x;  ! y. P y --> y < b|] ==> (x::nat) <= (GREATEST x. P x)"
apply (unfold Greatest_def)
apply (rule GreatestM_nat_le)
apply auto
done


use "meson_lemmas.ML"
use "Tools/meson.ML"
setup meson_setup

end
