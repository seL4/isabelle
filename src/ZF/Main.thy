(*$Id$
  theory Main includes everything except AC*)

theory Main = Update + List + EquivClass + IntDiv + CardinalArith:

(* belongs to theory Trancl *)
lemmas rtrancl_induct = rtrancl_induct [case_names initial step, induct set: rtrancl]
  and trancl_induct = trancl_induct [case_names initial step, induct set: trancl]
  and converse_trancl_induct = converse_trancl_induct [case_names initial step, consumes 1]
  and rtrancl_full_induct = rtrancl_full_induct [case_names initial step, consumes 1]

(* belongs to theory WF *)
lemmas wf_induct = wf_induct [induct set: wf]
  and wf_induct_rule = wf_induct [rule_format, induct set: wf]
  and wf_on_induct = wf_on_induct [consumes 2, induct set: wf_on]
  and wf_on_induct_rule = wf_on_induct [rule_format, consumes 2, induct set: wf_on]

(* belongs to theory Nat *)
lemmas nat_induct = nat_induct [case_names 0 succ, induct set: nat]
  and complete_induct = complete_induct [case_names less, consumes 1]
  and complete_induct_rule = complete_induct [rule_format, case_names less, consumes 1]
  and diff_induct = diff_induct [case_names 0 0_succ succ_succ, consumes 2]



subsection{* Iteration of the function @{term F} *}

consts  iterates :: "[i=>i,i,i] => i"   ("(_^_ '(_'))" [60,1000,1000] 60)

primrec
    "F^0 (x) = x"
    "F^(succ(n)) (x) = F(F^n (x))"

constdefs
  iterates_omega :: "[i=>i,i] => i"
    "iterates_omega(F,x) == \<Union>n\<in>nat. F^n (x)"

syntax (xsymbols)
  iterates_omega :: "[i=>i,i] => i"   ("(_^\<omega> '(_'))" [60,1000] 60)

lemma iterates_triv:
     "[| n\<in>nat;  F(x) = x |] ==> F^n (x) = x"  
by (induct n rule: nat_induct, simp_all)

lemma iterates_type [TC]:
     "[| n:nat;  a: A; !!x. x:A ==> F(x) : A |] 
      ==> F^n (a) : A"  
by (induct n rule: nat_induct, simp_all)

lemma iterates_omega_triv:
    "F(x) = x ==> F^\<omega> (x) = x" 
by (simp add: iterates_omega_def iterates_triv) 

lemma Ord_iterates [simp]:
     "[| n\<in>nat;  !!i. Ord(i) ==> Ord(F(i));  Ord(x) |] 
      ==> Ord(F^n (x))"  
by (induct n rule: nat_induct, simp_all)


(* belongs to theory Cardinal *)
declare Ord_Least [intro,simp,TC]

(* belongs to theory Epsilon *)
lemmas eclose_induct = eclose_induct [induct set: eclose]
  and eclose_induct_down = eclose_induct_down [consumes 1]

(* belongs to theory Finite *)
lemmas Fin_induct = Fin_induct [case_names 0 cons, induct set: Fin]

(* belongs to theory CardinalArith *)
lemmas Finite_induct = Finite_induct [case_names 0 cons, induct set: Finite]

(* belongs to theory List *)
lemmas list_append_induct = list_append_induct [case_names Nil snoc, consumes 1]

(* belongs to theory IntDiv *)
lemmas posDivAlg_induct = posDivAlg_induct [consumes 2]
  and negDivAlg_induct = negDivAlg_induct [consumes 2]


(* belongs to theory Epsilon *)

lemma def_transrec2:
     "(!!x. f(x)==transrec2(x,a,b))
      ==> f(0) = a & 
          f(succ(i)) = b(i, f(i)) & 
          (Limit(K) --> f(K) = (UN j<K. f(j)))"
by (simp add: transrec2_Limit)

(* belongs to theory CardinalArith *)

lemma InfCard_square_eqpoll: "InfCard(K) ==> K \<times> K \<approx> K"
apply (rule well_ord_InfCard_square_eq)  
 apply (erule InfCard_is_Card [THEN Card_is_Ord, THEN well_ord_Memrel]) 
apply (simp add: InfCard_is_Card [THEN Card_cardinal_eq]) 
done

lemma Inf_Card_is_InfCard: "[| ~Finite(i); Card(i) |] ==> InfCard(i)"
by (simp add: InfCard_def Card_is_Ord [THEN nat_le_infinite_Ord])

end
