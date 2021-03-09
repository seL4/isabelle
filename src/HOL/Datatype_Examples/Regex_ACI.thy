theory Regex_ACI
  imports "HOL-Library.Confluent_Quotient"
begin

datatype 'a rexp = Zero | Eps | Atom 'a | Alt "'a rexp" "'a rexp" | Conc "'a rexp" "'a rexp" | Star "'a rexp"

inductive ACI (infix "~" 64) where
  a1: "Alt (Alt r s) t ~ Alt r (Alt s t)"
| a2: "Alt r (Alt s t) ~ Alt (Alt r s) t"
| c: "Alt r s ~ Alt s r"
| i: "r ~ Alt r r"
| R: "r ~ r"
| A: "r ~ r' \<Longrightarrow> s ~ s' \<Longrightarrow> Alt r s ~ Alt r' s'"
| C: "r ~ r' \<Longrightarrow> s ~ s' \<Longrightarrow> Conc r s ~ Conc r' s'"
| S: "r ~ r' \<Longrightarrow> Star r ~ Star r'"

declare ACI.intros[intro]

abbreviation ACIcl (infix "~~" 64) where "(~~) \<equiv> equivclp (~)"

lemma eq_set_preserves_inter:
  fixes eq set
  assumes "\<And>r s. eq r s \<Longrightarrow> set r = set s" and "Ss \<noteq> {}"
  shows "(\<Inter>As\<in>Ss. {(x, x'). eq x x'} `` {x. set x \<subseteq> As}) \<subseteq> {(x, x'). eq x x'} `` {x. set x \<subseteq> \<Inter> Ss}"
  using assms by (auto simp: subset_eq) metis

lemma ACI_map_respects:
  fixes f :: "'a \<Rightarrow> 'b" and r s :: "'a rexp"
  assumes "r ~ s"
  shows "map_rexp f r ~ map_rexp f s"
  using assms by (induct r s rule: ACI.induct) auto

lemma ACIcl_map_respects:
  fixes f :: "'a \<Rightarrow> 'b" and r s :: "'a rexp"
  assumes "r ~~ s"
  shows "map_rexp f r ~~ map_rexp f s"
  using assms by (induct rule: equivclp_induct) (auto intro: ACI_map_respects equivclp_trans)

lemma ACI_set_eq:
  fixes r s :: "'a rexp"
  assumes "r ~ s"
  shows "set_rexp r = set_rexp s"
  using assms by (induct r s rule: ACI.induct) auto

lemma ACIcl_set_eq:
  fixes r s :: "'a rexp"
  assumes "r ~~ s"
  shows "set_rexp r = set_rexp s"
  using assms by (induct rule: equivclp_induct) (auto dest: ACI_set_eq)

lemma Alt_eq_map_rexp_iff:
  "Alt r s = map_rexp f x \<longleftrightarrow> (\<exists>r' s'. x = Alt r' s' \<and> map_rexp f r' = r \<and> map_rexp f s' = s)"
  "map_rexp f x = Alt r s \<longleftrightarrow> (\<exists>r' s'. x = Alt r' s' \<and> map_rexp f r' = r \<and> map_rexp f s' = s)"
  by (cases x; auto)+

lemma Conc_eq_map_rexp_iff:
  "Conc r s = map_rexp f x \<longleftrightarrow> (\<exists>r' s'. x = Conc r' s' \<and> map_rexp f r' = r \<and> map_rexp f s' = s)"
  "map_rexp f x = Conc r s \<longleftrightarrow> (\<exists>r' s'. x = Conc r' s' \<and> map_rexp f r' = r \<and> map_rexp f s' = s)"
  by (cases x; auto)+

lemma Star_eq_map_rexp_iff:
  "Star r = map_rexp f x \<longleftrightarrow> (\<exists>r'. x = Star r' \<and> map_rexp f r' = r)"
  "map_rexp f x = Star r \<longleftrightarrow> (\<exists>r'. x = Star r' \<and> map_rexp f r' = r)"
  by (cases x; auto)+

lemma AA: "r ~~ r' \<Longrightarrow> s ~~ s' \<Longrightarrow> Alt r s ~~ Alt r' s'"
proof (induct rule: equivclp_induct)
  case base
  then show ?case
    by (induct rule: equivclp_induct) (auto elim!: equivclp_trans)
next
  case (step s t)
  then show ?case
    by (auto elim!: equivclp_trans)
qed

lemma AAA: "(~)\<^sup>*\<^sup>* r  r' \<Longrightarrow> (~)\<^sup>*\<^sup>* s s' \<Longrightarrow> (~)\<^sup>*\<^sup>* (Alt r s) (Alt r' s')"
proof (induct r r' rule: rtranclp.induct)
  case (rtrancl_refl r)
  then show ?case
    by (induct s s' rule: rtranclp.induct)
      (auto elim!: rtranclp.rtrancl_into_rtrancl)
next
  case (rtrancl_into_rtrancl a b c)
  then show ?case
    by (auto elim!: rtranclp.rtrancl_into_rtrancl)
qed

lemma CC: "r ~~ r' \<Longrightarrow> s ~~ s' \<Longrightarrow> Conc r s ~~ Conc r' s'"
proof (induct rule: equivclp_induct)
  case base
  then show ?case
    by (induct rule: equivclp_induct) (auto elim!: equivclp_trans)
next
  case (step s t)
  then show ?case
    by (auto elim!: equivclp_trans)
qed

lemma CCC: "(~)\<^sup>*\<^sup>* r r' \<Longrightarrow> (~)\<^sup>*\<^sup>* s s' \<Longrightarrow> (~)\<^sup>*\<^sup>* (Conc r s) (Conc r' s')"
proof (induct r r' rule: rtranclp.induct)
  case (rtrancl_refl r)
  then show ?case
    by (induct s s' rule: rtranclp.induct)
      (auto elim!: rtranclp.rtrancl_into_rtrancl)
next
  case (rtrancl_into_rtrancl a b c)
  then show ?case
    by (auto elim!: rtranclp.rtrancl_into_rtrancl)
qed

lemma SS: "r ~~ r' \<Longrightarrow> Star r ~~ Star r'"
proof (induct rule: equivclp_induct)
  case (step s t)
  then show ?case
    by (auto elim!: equivclp_trans)
qed auto

lemma SSS: "(~)\<^sup>*\<^sup>* r r' \<Longrightarrow> (~)\<^sup>*\<^sup>* (Star r) (Star r')"
proof (induct r r' rule: rtranclp.induct)
  case (rtrancl_into_rtrancl a b c)
  then show ?case
    by (auto elim!: rtranclp.rtrancl_into_rtrancl)
qed auto

lemma map_rexp_ACI_inv: "map_rexp f x ~ y \<Longrightarrow> \<exists>z. x ~~ z \<and> y = map_rexp f z \<and> set_rexp z \<subseteq> set_rexp x"
proof (induct "map_rexp f x" y arbitrary: x rule: ACI.induct)
  case (a1 r s t)
  then obtain r' s' t' where "x = Alt (Alt r' s') t'"
    "map_rexp f r' = r" "map_rexp f s' = s" "map_rexp f t' = t"
    by (auto simp: Alt_eq_map_rexp_iff)
  then show ?case
    by (intro exI[of _ "Alt r' (Alt s' t')"]) auto
next
  case (a2 r s t)
  then obtain r' s' t' where "x = Alt r' (Alt s' t')"
    "map_rexp f r' = r" "map_rexp f s' = s" "map_rexp f t' = t"
    by (auto simp: Alt_eq_map_rexp_iff)
  then show ?case
    by (intro exI[of _ "Alt (Alt r' s') t'"]) auto
next
  case (c r s)
  then obtain r' s' where "x = Alt r' s'"
    "map_rexp f r' = r" "map_rexp f s' = s"
    by (auto simp: Alt_eq_map_rexp_iff)
  then show ?case
    by (intro exI[of _ "Alt s' r'"]) auto
next
  case (i r)
  then show ?case
    by (intro exI[of _ "Alt r r"]) auto
next
  case (R r)
  then show ?case by (auto intro: exI[of _ r])
next
  case (A r rr s ss)
  then obtain r' s' where "x = Alt r' s'"
    "map_rexp f r' = r" "map_rexp f s' = s"
    by (auto simp: Alt_eq_map_rexp_iff)
  moreover from A(2)[OF this(2)[symmetric]] A(4)[OF this(3)[symmetric]] obtain rr' ss' where
    "r' ~~ rr'" "rr = map_rexp f rr'" "s' ~~ ss'" "ss = map_rexp f ss'"
    "set_rexp rr' \<subseteq> set_rexp r'" "set_rexp ss' \<subseteq> set_rexp s'"
    by blast
  ultimately show ?case using A(1,3)
    by (intro exI[of _ "Alt rr' ss'"]) (auto intro!: AA)
next
  case (C r rr s ss)
  then obtain r' s' where "x = Conc r' s'"
    "map_rexp f r' = r" "map_rexp f s' = s"
    by (auto simp: Conc_eq_map_rexp_iff)
  moreover from C(2)[OF this(2)[symmetric]] C(4)[OF this(3)[symmetric]] obtain rr' ss' where
    "r' ~~ rr'" "rr = map_rexp f rr'" "s' ~~ ss'" "ss = map_rexp f ss'"
    "set_rexp rr' \<subseteq> set_rexp r'" "set_rexp ss' \<subseteq> set_rexp s'"
    by blast
  ultimately show ?case using C(1,3)
    by (intro exI[of _ "Conc rr' ss'"]) (auto intro!: CC)
next
  case (S r rr)
  then obtain r' where "x = Star r'" "map_rexp f r' = r"
    by (auto simp: Star_eq_map_rexp_iff)
  moreover from S(2)[OF this(2)[symmetric]] obtain rr' where "r' ~~ rr'" "rr = map_rexp f rr'"
    "set_rexp rr' \<subseteq> set_rexp r'"
    by blast
  ultimately show ?case
    by (intro exI[of _ "Star rr'"]) (auto intro!: SS)
qed

lemma reflclp_ACI: "(~)\<^sup>=\<^sup>= = (~)"
  unfolding fun_eq_iff
  by auto

lemma strong_confluentp_ACI: "strong_confluentp (~)"
  apply (rule strong_confluentpI, unfold reflclp_ACI)
  subgoal for x y z
  proof (induct x y arbitrary: z rule: ACI.induct)
    case (a1 r s t)
    then show ?case
      by (auto intro: AAA converse_rtranclp_into_rtranclp)
  next
    case (a2 r s t)
    then show ?case
      by (auto intro: AAA converse_rtranclp_into_rtranclp)
  next
    case (c r s)
    then show ?case
      by (cases rule: ACI.cases) (auto intro: AAA)
  next
    case (i r)
    then show ?case
      by (auto intro: AAA)
  next
    case (R r)
    then show ?case
      by auto
  next
    note A1 = ACI.A[OF _ R]
    note A2 = ACI.A[OF R]
    case (A r r' s s')
    from A(5,1-4) show ?case
    proof (cases rule: ACI.cases)
      case inner: (a1 r'' s'')
      from A(1,3) show ?thesis
        unfolding inner
      proof (elim ACI.cases[of _ r'], goal_cases Xa1 Xa2 XC XI XR XP XT XS)
        case (Xa1 rr ss tt)
        with A(3) show ?case
          by (elim exI[where P = "\<lambda>x. _ x \<and> _ ~ x", OF conjI[OF _ A2[OF A2]], rotated])
            (metis a1 a2 A1 r_into_rtranclp rtranclp.rtrancl_into_rtrancl)
      next
        case (Xa2 r s t)
        then show ?case
          by (elim exI[where P = "\<lambda>x. _ x \<and> _ ~ x", OF conjI[OF _ A2[OF A2]], rotated])
            (metis a1 A1 r_into_rtranclp rtranclp.rtrancl_into_rtrancl)
      next
        case (XC r s)
        then show ?case
          by (elim exI[where P = "\<lambda>x. _ x \<and> _ ~ x", OF conjI[OF _ A2[OF A2]], rotated])
            (metis a1 c A1 r_into_rtranclp rtranclp.rtrancl_into_rtrancl)
      next
        case (XI r)
        then show ?case
          apply (elim exI[where P = "\<lambda>x. _ x \<and> _ ~ x", OF conjI[OF _ ACI.A[OF i ACI.A[OF i]]], rotated])
          apply hypsubst
          apply (rule converse_rtranclp_into_rtranclp, rule a1)
          apply (rule converse_rtranclp_into_rtranclp, rule a1)
          apply (rule converse_rtranclp_into_rtranclp, rule A2, rule a2)
          apply (rule converse_rtranclp_into_rtranclp, rule A2, rule A1, rule c)
          apply (rule converse_rtranclp_into_rtranclp, rule A2, rule a1)
          apply (rule converse_rtranclp_into_rtranclp, rule A2, rule a1)
          apply (rule converse_rtranclp_into_rtranclp, rule a2)
          apply (rule converse_rtranclp_into_rtranclp, rule A2, rule a2)
          apply blast
          done
      qed auto
    next
      case inner: (a2 s'' t'')
      with A(1,3) show ?thesis
        unfolding inner
      proof (elim ACI.cases[of _ s'], goal_cases Xa1 Xa2 XC XI XR XP XT XS)
        case (Xa1 rr ss tt)
        with A(3) show ?case
          by (elim exI[where P = "\<lambda>x. _ x \<and> _ ~ x", OF conjI[OF _ A1[OF A1]], rotated])
            (metis a2 A2 r_into_rtranclp rtranclp.rtrancl_into_rtrancl)
      next
        case (Xa2 r s t)
        then show ?case
          by (elim exI[where P = "\<lambda>x. _ x \<and> _ ~ x", OF conjI[OF _ A1[OF A1]], rotated])
            (metis a1 a2 A2 r_into_rtranclp rtranclp.rtrancl_into_rtrancl)
      next
        case (XC r s)
        then show ?case
          by (elim exI[where P = "\<lambda>x. _ x \<and> _ ~ x", OF conjI[OF _ A1[OF A1]], rotated])
            (metis a2 c A2 r_into_rtranclp rtranclp.rtrancl_into_rtrancl)
      next
        case (XI r)
        then show ?case
          apply (elim exI[where P = "\<lambda>x. _ x \<and> _ ~ x", OF conjI[OF _ ACI.A[OF ACI.A[OF _ i] i]], rotated])
          apply hypsubst
          apply (rule converse_rtranclp_into_rtranclp, rule A2, rule a2)
          apply (rule converse_rtranclp_into_rtranclp, rule A2, rule A1, rule c)
          apply (rule converse_rtranclp_into_rtranclp, rule A2, rule a1)
          apply (rule converse_rtranclp_into_rtranclp, rule A2, rule A2, rule a1)
          apply (rule converse_rtranclp_into_rtranclp, rule A2, rule a2)
          apply (rule converse_rtranclp_into_rtranclp, rule a2)
          apply blast
          done
      qed auto
    qed (auto 5 0 intro: AAA)
  next
    case (C r r' s s')
    from C(5,1-4) show ?case
      by (cases rule: ACI.cases) (auto 5 0 intro: CCC)
  next
    case (S r r')
    from S(3,1,2) show ?case
      by (cases rule: ACI.cases) (auto intro: SSS)
  qed
  done

lemma confluent_quotient_ACI:
  "confluent_quotient (~) (~~) (~~) (~~) (~~) (~~)
     (map_rexp fst) (map_rexp snd) (map_rexp fst) (map_rexp snd)
     rel_rexp rel_rexp rel_rexp set_rexp set_rexp"
  by unfold_locales (auto dest: ACIcl_set_eq ACIcl_map_respects simp: rexp.in_rel rexp.rel_compp map_rexp_ACI_inv
      intro: equivpI reflpI sympI transpI
      strong_confluentp_imp_confluentp[OF strong_confluentp_ACI])

inductive ACIEQ (infix "\<approx>" 64) where
  a: "Alt (Alt r s) t \<approx> Alt r (Alt s t)"
| c: "Alt r s \<approx> Alt s r"
| i: "Alt r r \<approx> r"
| A: "r \<approx> r' \<Longrightarrow> s \<approx> s' \<Longrightarrow> Alt r s \<approx> Alt r' s'"
| C: "r \<approx> r' \<Longrightarrow> s \<approx> s' \<Longrightarrow> Conc r s \<approx> Conc r' s'"
| S: "r \<approx> r' \<Longrightarrow> Star r \<approx> Star r'"
| r: "r \<approx> r"
| s: "r \<approx> s \<Longrightarrow> s \<approx> r"
| t: "r \<approx> s \<Longrightarrow> s \<approx> t \<Longrightarrow> r \<approx> t"

lemma ACIEQ_le_ACIcl: "r \<approx> s \<Longrightarrow> r ~~ s"
  by (induct r s rule: ACIEQ.induct) (auto intro: AA CC SS equivclp_sym equivclp_trans)

lemma ACI_le_ACIEQ: "r ~ s \<Longrightarrow> r \<approx> s"
  by (induct r s rule: ACI.induct) (auto intro: ACIEQ.intros)

lemma ACIcl_le_ACIEQ: "r ~~ s \<Longrightarrow> r \<approx> s"
  by (induct rule: equivclp_induct) (auto 0 3 intro: ACIEQ.intros ACI_le_ACIEQ)

lemma ACIEQ_alt: "(\<approx>) = (~~)"
  by (simp add: ACIEQ_le_ACIcl ACIcl_le_ACIEQ antisym predicate2I)

quotient_type 'a ACI_rexp = "'a rexp" / "(\<approx>)"
  unfolding ACIEQ_alt by (auto intro!: equivpI reflpI sympI transpI)

lift_bnf 'a ACI_rexp
  unfolding ACIEQ_alt
  subgoal for A Q by (rule confluent_quotient.subdistributivity[OF confluent_quotient_ACI])
  subgoal for Ss by (intro eq_set_preserves_inter[rotated] ACIcl_set_eq; auto)
  done

datatype ldl = Prop string | And ldl ldl | Not ldl | Match "ldl ACI_rexp"

end