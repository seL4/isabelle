(*  Title:      HOL/Proofs/Lambda/Lambda.thy
    Author:     Tobias Nipkow
    Copyright   1995 TU Muenchen
*)

header {* Basic definitions of Lambda-calculus *}

theory Lambda imports Main begin

declare [[syntax_ambiguity = ignore]]


subsection {* Lambda-terms in de Bruijn notation and substitution *}

datatype dB =
    Var nat
  | App dB dB (infixl "\<degree>" 200)
  | Abs dB

primrec
  lift :: "[dB, nat] => dB"
where
    "lift (Var i) k = (if i < k then Var i else Var (i + 1))"
  | "lift (s \<degree> t) k = lift s k \<degree> lift t k"
  | "lift (Abs s) k = Abs (lift s (k + 1))"

primrec
  subst :: "[dB, dB, nat] => dB"  ("_[_'/_]" [300, 0, 0] 300)
where (* FIXME base names *)
    subst_Var: "(Var i)[s/k] =
      (if k < i then Var (i - 1) else if i = k then s else Var i)"
  | subst_App: "(t \<degree> u)[s/k] = t[s/k] \<degree> u[s/k]"
  | subst_Abs: "(Abs t)[s/k] = Abs (t[lift s 0 / k+1])"

declare subst_Var [simp del]

text {* Optimized versions of @{term subst} and @{term lift}. *}

primrec
  liftn :: "[nat, dB, nat] => dB"
where
    "liftn n (Var i) k = (if i < k then Var i else Var (i + n))"
  | "liftn n (s \<degree> t) k = liftn n s k \<degree> liftn n t k"
  | "liftn n (Abs s) k = Abs (liftn n s (k + 1))"

primrec
  substn :: "[dB, dB, nat] => dB"
where
    "substn (Var i) s k =
      (if k < i then Var (i - 1) else if i = k then liftn k s 0 else Var i)"
  | "substn (t \<degree> u) s k = substn t s k \<degree> substn u s k"
  | "substn (Abs t) s k = Abs (substn t s (k + 1))"


subsection {* Beta-reduction *}

inductive beta :: "[dB, dB] => bool"  (infixl "\<rightarrow>\<^sub>\<beta>" 50)
  where
    beta [simp, intro!]: "Abs s \<degree> t \<rightarrow>\<^sub>\<beta> s[t/0]"
  | appL [simp, intro!]: "s \<rightarrow>\<^sub>\<beta> t ==> s \<degree> u \<rightarrow>\<^sub>\<beta> t \<degree> u"
  | appR [simp, intro!]: "s \<rightarrow>\<^sub>\<beta> t ==> u \<degree> s \<rightarrow>\<^sub>\<beta> u \<degree> t"
  | abs [simp, intro!]: "s \<rightarrow>\<^sub>\<beta> t ==> Abs s \<rightarrow>\<^sub>\<beta> Abs t"

abbreviation
  beta_reds :: "[dB, dB] => bool"  (infixl "->>" 50) where
  "s ->> t == beta^** s t"

notation (latex)
  beta_reds  (infixl "\<rightarrow>\<^sub>\<beta>\<^sup>*" 50)

inductive_cases beta_cases [elim!]:
  "Var i \<rightarrow>\<^sub>\<beta> t"
  "Abs r \<rightarrow>\<^sub>\<beta> s"
  "s \<degree> t \<rightarrow>\<^sub>\<beta> u"

declare if_not_P [simp] not_less_eq [simp]
  -- {* don't add @{text "r_into_rtrancl[intro!]"} *}


subsection {* Congruence rules *}

lemma rtrancl_beta_Abs [intro!]:
    "s \<rightarrow>\<^sub>\<beta>\<^sup>* s' ==> Abs s \<rightarrow>\<^sub>\<beta>\<^sup>* Abs s'"
  by (induct set: rtranclp) (blast intro: rtranclp.rtrancl_into_rtrancl)+

lemma rtrancl_beta_AppL:
    "s \<rightarrow>\<^sub>\<beta>\<^sup>* s' ==> s \<degree> t \<rightarrow>\<^sub>\<beta>\<^sup>* s' \<degree> t"
  by (induct set: rtranclp) (blast intro: rtranclp.rtrancl_into_rtrancl)+

lemma rtrancl_beta_AppR:
    "t \<rightarrow>\<^sub>\<beta>\<^sup>* t' ==> s \<degree> t \<rightarrow>\<^sub>\<beta>\<^sup>* s \<degree> t'"
  by (induct set: rtranclp) (blast intro: rtranclp.rtrancl_into_rtrancl)+

lemma rtrancl_beta_App [intro]:
    "[| s \<rightarrow>\<^sub>\<beta>\<^sup>* s'; t \<rightarrow>\<^sub>\<beta>\<^sup>* t' |] ==> s \<degree> t \<rightarrow>\<^sub>\<beta>\<^sup>* s' \<degree> t'"
  by (blast intro!: rtrancl_beta_AppL rtrancl_beta_AppR intro: rtranclp_trans)


subsection {* Substitution-lemmas *}

lemma subst_eq [simp]: "(Var k)[u/k] = u"
  by (simp add: subst_Var)

lemma subst_gt [simp]: "i < j ==> (Var j)[u/i] = Var (j - 1)"
  by (simp add: subst_Var)

lemma subst_lt [simp]: "j < i ==> (Var j)[u/i] = Var j"
  by (simp add: subst_Var)

lemma lift_lift:
    "i < k + 1 \<Longrightarrow> lift (lift t i) (Suc k) = lift (lift t k) i"
  by (induct t arbitrary: i k) auto

lemma lift_subst [simp]:
    "j < i + 1 \<Longrightarrow> lift (t[s/j]) i = (lift t (i + 1)) [lift s i / j]"
  by (induct t arbitrary: i j s)
    (simp_all add: diff_Suc subst_Var lift_lift split: nat.split)

lemma lift_subst_lt:
    "i < j + 1 \<Longrightarrow> lift (t[s/j]) i = (lift t i) [lift s i / j + 1]"
  by (induct t arbitrary: i j s) (simp_all add: subst_Var lift_lift)

lemma subst_lift [simp]:
    "(lift t k)[s/k] = t"
  by (induct t arbitrary: k s) simp_all

lemma subst_subst:
    "i < j + 1 \<Longrightarrow> t[lift v i / Suc j][u[v/j]/i] = t[u/i][v/j]"
  by (induct t arbitrary: i j u v)
    (simp_all add: diff_Suc subst_Var lift_lift [symmetric] lift_subst_lt
      split: nat.split)


subsection {* Equivalence proof for optimized substitution *}

lemma liftn_0 [simp]: "liftn 0 t k = t"
  by (induct t arbitrary: k) (simp_all add: subst_Var)

lemma liftn_lift [simp]: "liftn (Suc n) t k = lift (liftn n t k) k"
  by (induct t arbitrary: k) (simp_all add: subst_Var)

lemma substn_subst_n [simp]: "substn t s n = t[liftn n s 0 / n]"
  by (induct t arbitrary: n) (simp_all add: subst_Var)

theorem substn_subst_0: "substn t s 0 = t[s/0]"
  by simp


subsection {* Preservation theorems *}

text {* Not used in Church-Rosser proof, but in Strong
  Normalization. \medskip *}

theorem subst_preserves_beta [simp]:
    "r \<rightarrow>\<^sub>\<beta> s ==> r[t/i] \<rightarrow>\<^sub>\<beta> s[t/i]"
  by (induct arbitrary: t i set: beta) (simp_all add: subst_subst [symmetric])

theorem subst_preserves_beta': "r \<rightarrow>\<^sub>\<beta>\<^sup>* s ==> r[t/i] \<rightarrow>\<^sub>\<beta>\<^sup>* s[t/i]"
  apply (induct set: rtranclp)
   apply (rule rtranclp.rtrancl_refl)
  apply (erule rtranclp.rtrancl_into_rtrancl)
  apply (erule subst_preserves_beta)
  done

theorem lift_preserves_beta [simp]:
    "r \<rightarrow>\<^sub>\<beta> s ==> lift r i \<rightarrow>\<^sub>\<beta> lift s i"
  by (induct arbitrary: i set: beta) auto

theorem lift_preserves_beta': "r \<rightarrow>\<^sub>\<beta>\<^sup>* s ==> lift r i \<rightarrow>\<^sub>\<beta>\<^sup>* lift s i"
  apply (induct set: rtranclp)
   apply (rule rtranclp.rtrancl_refl)
  apply (erule rtranclp.rtrancl_into_rtrancl)
  apply (erule lift_preserves_beta)
  done

theorem subst_preserves_beta2 [simp]: "r \<rightarrow>\<^sub>\<beta> s ==> t[r/i] \<rightarrow>\<^sub>\<beta>\<^sup>* t[s/i]"
  apply (induct t arbitrary: r s i)
    apply (simp add: subst_Var r_into_rtranclp)
   apply (simp add: rtrancl_beta_App)
  apply (simp add: rtrancl_beta_Abs)
  done

theorem subst_preserves_beta2': "r \<rightarrow>\<^sub>\<beta>\<^sup>* s ==> t[r/i] \<rightarrow>\<^sub>\<beta>\<^sup>* t[s/i]"
  apply (induct set: rtranclp)
   apply (rule rtranclp.rtrancl_refl)
  apply (erule rtranclp_trans)
  apply (erule subst_preserves_beta2)
  done

end
