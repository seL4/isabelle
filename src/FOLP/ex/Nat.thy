(*  Title:      FOLP/ex/nat.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge
*)

header {* Theory of the natural numbers: Peano's axioms, primitive recursion *}

theory Nat
imports FOLP
begin

typedecl nat
arities nat :: "term"

consts
  0 :: nat    ("0")
  Suc :: "nat => nat"
  rec :: "[nat, 'a, [nat, 'a] => 'a] => 'a"
  add :: "[nat, nat] => nat"    (infixl "+" 60)

  (*Proof terms*)
  nrec :: "[nat, p, [nat, p] => p] => p"
  ninj :: "p => p"
  nneq :: "p => p"
  rec0 :: "p"
  recSuc :: "p"

axioms
  induct:     "[| b:P(0); !!x u. u:P(x) ==> c(x,u):P(Suc(x))
              |] ==> nrec(n,b,c):P(n)"

  Suc_inject: "p:Suc(m)=Suc(n) ==> ninj(p) : m=n"
  Suc_neq_0:  "p:Suc(m)=0      ==> nneq(p) : R"
  rec_0:      "rec0 : rec(0,a,f) = a"
  rec_Suc:    "recSuc : rec(Suc(m), a, f) = f(m, rec(m,a,f))"

defs
  add_def:    "m+n == rec(m, n, %x y. Suc(y))"

axioms
  nrecB0:     "b: A ==> nrec(0,b,c) = b : A"
  nrecBSuc:   "c(n,nrec(n,b,c)) : A ==> nrec(Suc(n),b,c) = c(n,nrec(n,b,c)) : A"


subsection {* Proofs about the natural numbers *}

lemma Suc_n_not_n: "?p : ~ (Suc(k) = k)"
apply (rule_tac n = k in induct)
apply (rule notI)
apply (erule Suc_neq_0)
apply (rule notI)
apply (erule notE)
apply (erule Suc_inject)
done

lemma "?p : (k+m)+n = k+(m+n)"
apply (rule induct)
back
back
back
back
back
back
oops

lemma add_0 [simp]: "?p : 0+n = n"
apply (unfold add_def)
apply (rule rec_0)
done

lemma add_Suc [simp]: "?p : Suc(m)+n = Suc(m+n)"
apply (unfold add_def)
apply (rule rec_Suc)
done


lemma Suc_cong: "p : x = y \<Longrightarrow> ?p : Suc(x) = Suc(y)"
  apply (erule subst)
  apply (rule refl)
  done

lemma Plus_cong: "[| p : a = x;  q: b = y |] ==> ?p : a + b = x + y"
  apply (erule subst, erule subst, rule refl)
  done

lemmas nat_congs = Suc_cong Plus_cong

ML {*
  val add_ss = FOLP_ss addcongs @{thms nat_congs} addrews [@{thm add_0}, @{thm add_Suc}]
*}

lemma add_assoc: "?p : (k+m)+n = k+(m+n)"
apply (rule_tac n = k in induct)
apply (tactic {* SIMP_TAC add_ss 1 *})
apply (tactic {* ASM_SIMP_TAC add_ss 1 *})
done

lemma add_0_right: "?p : m+0 = m"
apply (rule_tac n = m in induct)
apply (tactic {* SIMP_TAC add_ss 1 *})
apply (tactic {* ASM_SIMP_TAC add_ss 1 *})
done

lemma add_Suc_right: "?p : m+Suc(n) = Suc(m+n)"
apply (rule_tac n = m in induct)
apply (tactic {* ALLGOALS (ASM_SIMP_TAC add_ss) *})
done

(*mk_typed_congs appears not to work with FOLP's version of subst*)

end
