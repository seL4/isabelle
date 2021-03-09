theory Regex_ACIDZ
  imports "HOL-Library.Confluent_Quotient"
begin

datatype (discs_sels) 'a rexp = Zero | Eps | Atom 'a
  | Alt "'a rexp" "'a rexp" | Conc "'a rexp" "'a rexp" | Star "'a rexp"

fun elim_zeros where
  "elim_zeros (Alt r s) =
    (let r' = elim_zeros r; s' = elim_zeros s in
     if r' = Zero then s' else if s' = Zero then r' else Alt r' s')"
| "elim_zeros (Conc r s) = (let r' = elim_zeros r in if r' = Zero then Zero else Conc r' s)"
| "elim_zeros r = r"

fun distribute where
  "distribute t (Alt r s) = Alt (distribute t r) (distribute t s)"
| "distribute t (Conc r s) = Conc (distribute s r) t"
| "distribute t r = Conc r t"

inductive ACIDZ (infix "~" 64) where
  a1: "Alt (Alt r s) t ~ Alt r (Alt s t)"
| a2: "Alt r (Alt s t) ~ Alt (Alt r s) t"
| c: "Alt r s ~ Alt s r"
| i: "r ~ Alt r r"
| z: "r ~ s \<Longrightarrow> r ~ elim_zeros s"
| d: "Conc r t ~ distribute t r"
| R: "r ~ r"
| A: "r ~ r' \<Longrightarrow> s ~ s' \<Longrightarrow> Alt r s ~ Alt r' s'"
| C: "r ~ r' \<Longrightarrow> Conc r s ~ Conc r' s"

inductive_cases ACIDZ_AltE[elim]: "Alt r s ~ t"
inductive_cases ACIDZ_ConcE[elim]: "Conc r s ~ t"
inductive_cases ACIDZ_StarE[elim]: "Star r ~ t"

declare ACIDZ.intros[intro]

abbreviation ACIDZcl (infix "~~" 64) where "(~~) \<equiv> equivclp (~)"

lemma map_rexp_distribute[simp]: "map_rexp f (distribute t r) = distribute (map_rexp f t) (map_rexp f r)"
  by (induct r arbitrary: t) auto

lemma set_rexp_distribute[simp]: "set_rexp (distribute t r) = set_rexp r \<union> set_rexp t"
  by (induct r arbitrary: t) auto

lemma Zero_eq_map_rexp_iff[simp]:
  "Zero = map_rexp f x \<longleftrightarrow> x = Zero"
  "map_rexp f x = Zero \<longleftrightarrow> x = Zero"
  by (cases x; auto)+

lemma Alt_eq_map_rexp_iff:
  "Alt r s = map_rexp f x \<longleftrightarrow> (\<exists>r' s'. x = Alt r' s' \<and> map_rexp f r' = r \<and> map_rexp f s' = s)"
  "map_rexp f x = Alt r s \<longleftrightarrow> (\<exists>r' s'. x = Alt r' s' \<and> map_rexp f r' = r \<and> map_rexp f s' = s)"
  by (cases x; auto)+

lemma map_rexp_elim_zeros[simp]: "map_rexp f (elim_zeros r) = elim_zeros (map_rexp f r)"
  by (induct r rule: elim_zeros.induct) (auto simp: Let_def)

lemma set_rexp_elim_zeros: "set_rexp (elim_zeros r) \<subseteq> set_rexp r"
  by (induct r rule: elim_zeros.induct) (auto simp: Let_def)

lemma ACIDZ_map_respects:
  fixes f :: "'a \<Rightarrow> 'b" and r s :: "'a rexp"
  assumes "r ~ s"
  shows "map_rexp f r ~ map_rexp f s"
  using assms by (induct r s rule: ACIDZ.induct) (auto simp: Let_def)

lemma ACIDZcl_map_respects:
  fixes f :: "'a \<Rightarrow> 'b" and r s :: "'a rexp"
  assumes "r ~~ s"
  shows "map_rexp f r ~~ map_rexp f s"
  using assms by (induct rule: equivclp_induct) (auto intro: ACIDZ_map_respects equivclp_trans)

lemma finite_set_rexp: "finite (set_rexp r)"
  by (induct r) auto

lemma ACIDZ_set_rexp: "r ~ s \<Longrightarrow> set_rexp s \<subseteq> set_rexp r"
  by (induct r s rule: ACIDZ.induct) (auto dest: set_mp[OF set_rexp_elim_zeros] simp: Let_def)

lemma ACIDZ_set_rexp': "(~)\<^sup>*\<^sup>* r s \<Longrightarrow> set_rexp s \<subseteq> set_rexp r"
  by (induct rule: rtranclp.induct) (auto dest: ACIDZ_set_rexp)


lemma Conc_eq_map_rexp_iff:
  "Conc r s = map_rexp f x \<longleftrightarrow> (\<exists>r' s'. x = Conc r' s' \<and> map_rexp f r' = r \<and> map_rexp f s' = s)"
  "map_rexp f x = Conc r s \<longleftrightarrow> (\<exists>r' s'. x = Conc r' s' \<and> map_rexp f r' = r \<and> map_rexp f s' = s)"
  by (cases x; auto)+

lemma Star_eq_map_rexp_iff:
  "Star r = map_rexp f x \<longleftrightarrow> (\<exists>r'. x = Star r' \<and> map_rexp f r' = r)"
  "map_rexp f x = Star r \<longleftrightarrow> (\<exists>r'. x = Star r' \<and> map_rexp f r' = r)"
  by (cases x; auto)+

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

lemma CCC: "(~)\<^sup>*\<^sup>* r r' \<Longrightarrow> (~)\<^sup>*\<^sup>* (Conc r s) (Conc r' s)"
proof (induct r r' rule: rtranclp.induct)
  case (rtrancl_refl r)
  then show ?case
    by simp
next
  case (rtrancl_into_rtrancl a b c)
  then show ?case
    by (auto elim!: rtranclp.rtrancl_into_rtrancl)
qed

lemma map_rexp_ACIDZ_inv: "map_rexp f x ~ y \<Longrightarrow> \<exists>z. (~)\<^sup>*\<^sup>* x z \<and> y = map_rexp f z"
proof (induct "map_rexp f x" y arbitrary: x rule: ACIDZ.induct)
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
  case (z r)
  then show ?case
    by (metis ACIDZ.z R map_rexp_elim_zeros rtranclp.simps)
next
  case (d r s)
  then obtain r' s' where "x = Conc r' s'"
    "map_rexp f r' = r" "map_rexp f s' = s"
    by (auto simp: Conc_eq_map_rexp_iff)
  then show ?case
    by (intro exI[of _ "distribute s' r'"]) auto
next
  case (R r)
  then show ?case by (auto intro: exI[of _ r])
next
  case (A r rr s ss)
  then obtain r' s' where "x = Alt r' s'"
    "map_rexp f r' = r" "map_rexp f s' = s"
    by (auto simp: Alt_eq_map_rexp_iff)
  moreover from A(2)[OF this(2)[symmetric]] A(4)[OF this(3)[symmetric]] obtain rr' ss' where
    "(~)\<^sup>*\<^sup>* r' rr'" "rr = map_rexp f rr'" "(~)\<^sup>*\<^sup>* s' ss'" "ss = map_rexp f ss'"
    by blast
  ultimately show ?case using A(1,3)
    by (intro exI[of _ "Alt rr' ss'"]) (auto intro!: AAA)
next
  case (C r rr s)
  then obtain r' s' where "x = Conc r' s'"
    "map_rexp f r' = r" "map_rexp f s' = s"
    by (auto simp: Conc_eq_map_rexp_iff)
  moreover from C(2)[OF this(2)[symmetric]] obtain rr' where
    "(~)\<^sup>*\<^sup>* r' rr'" "rr = map_rexp f rr'"
    by blast
  ultimately show ?case using C(1,3)
    by (intro exI[of _ "Conc rr' s'"]) (auto intro!: CCC)
qed

lemma reflclp_ACIDZ: "(~)\<^sup>=\<^sup>= = (~)"
  unfolding fun_eq_iff
  by auto

lemma elim_zeros_distribute_Zero: "elim_zeros r = Zero \<Longrightarrow> elim_zeros (distribute t r) = Zero"
  by (induct r arbitrary: t) (auto simp: Let_def split: if_splits)

lemma elim_zeros_ACIDZ_Zero: "r ~ s \<Longrightarrow> elim_zeros r = Zero \<Longrightarrow> elim_zeros s = Zero"
  by (induct r s rule: ACIDZ.induct) (auto simp: Let_def elim_zeros_distribute_Zero split: if_splits)

lemma AZZ[simp]: "Alt Zero Zero ~ Zero"
  by (metis elim_zeros.simps(3) elim_zeros_ACIDZ_Zero i z)

lemma elim_zeros_idem[simp]: "elim_zeros (elim_zeros r) = elim_zeros r"
  by (induct r rule: elim_zeros.induct) (auto simp: Let_def)

lemma elim_zeros_distribute_idem: "elim_zeros (distribute s (elim_zeros r)) = elim_zeros (distribute s r)"
  by (induct r arbitrary: s rule: elim_zeros.induct) (auto simp: Let_def)

lemma zz: "r ~ s \<Longrightarrow> t = elim_zeros s \<Longrightarrow> r ~ t"
  by (metis z)

lemma elim_zeros_ACIDZ1: "r ~ s \<Longrightarrow> elim_zeros r ~ elim_zeros s"
proof (induct r s rule: ACIDZ.induct)
  case (c r s)
  then show ?case by (auto simp: Let_def)
next
  case (d r t)
  then show ?case
    by (smt (z3) ACIDZ.d R distribute.simps(3) elim_zeros.simps(2) elim_zeros.simps(3) elim_zeros_distribute_idem z)
next
  case (A r r' s s')
  then show ?case
    by (auto 0 2 simp: Let_def dest: elim_zeros_ACIDZ_Zero elim: zz[OF ACIDZ.A])
next
  case (C r r' s)
  then show ?case
    by (smt (z3) ACIDZ.C elim_zeros.simps(2,3) z elim_zeros_ACIDZ_Zero)
qed (auto simp: Let_def)

lemma AA': "r ~ r' \<Longrightarrow> s ~ s' \<Longrightarrow> t = elim_zeros (Alt r' s') \<Longrightarrow> Alt r s ~ t"
  by (auto simp del: elim_zeros.simps)

lemma distribute_ACIDZ1: "r ~ r' \<Longrightarrow> distribute s r ~ elim_zeros (distribute s r')"
proof (induct r r' arbitrary: s rule: ACIDZ.induct)
  case (A r r' s s' u)
  from A(2,4)[of u] show ?case
    by (auto simp: Let_def elim: zz[OF ACIDZ.A])
next
  case (C r r' s)
  then show ?case
    by (smt (verit, best) ACIDZ.C distribute.simps(2,3) elim_zeros.simps(2,3) z)
qed (auto simp del: elim_zeros.simps simp: elim_zeros_distribute_idem)

lemma elim_zeros_ACIDZ: "r ~ s \<Longrightarrow> (~)\<^sup>*\<^sup>* (elim_zeros r) (elim_zeros s)"
  using elim_zeros_ACIDZ1 by blast

lemma elim_zeros_ACIDZ_rtranclp: "(~)\<^sup>*\<^sup>* r s \<Longrightarrow> (~)\<^sup>*\<^sup>* (elim_zeros r) (elim_zeros s)"
  by (induct rule: rtranclp_induct) (auto elim!: rtranclp_trans elim_zeros_ACIDZ)

lemma distribute_ACIDZ: "(~) r r' \<Longrightarrow> (~)\<^sup>*\<^sup>* (distribute s r) (elim_zeros (distribute s r'))"
  by (metis distribute_ACIDZ1 rtranclp.simps)

lemma ACIDZ_elim_zeros: "(~) r s \<Longrightarrow> elim_zeros r = Zero \<Longrightarrow> elim_zeros s = Zero"
  by (meson elim_zeros_ACIDZ1 elim_zeros_ACIDZ_Zero)

lemma ACIDZ_elim_zeros_rtranclp:
  "(~)\<^sup>*\<^sup>* r s \<Longrightarrow> elim_zeros r = Zero \<Longrightarrow> elim_zeros s = Zero"
  by (induct rule: rtranclp_induct) (auto elim: ACIDZ_elim_zeros)

lemma Alt_elim_zeros[simp]:
  "Alt (elim_zeros r) s ~ elim_zeros (Alt r s)"
  "Alt r (elim_zeros s) ~ elim_zeros (Alt r s)"
  by (smt (verit, ccfv_threshold) ACIDZ.simps elim_zeros.simps(1) elim_zeros_idem)+

lemma strong_confluentp_ACIDZ: "strong_confluentp (~)"
proof (rule strong_confluentpI, unfold reflclp_ACIDZ)
  fix x y z :: "'a rexp"
  assume "x ~ y" "x ~ z"
  then show "\<exists>u. (~)\<^sup>*\<^sup>* y u \<and> z ~ u"
  proof (induct x y arbitrary: z rule: ACIDZ.induct)
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
      by (cases rule: ACIDZ.cases)
        (auto 0 4 intro: exI[where P = "\<lambda>x. _ x \<and> _ ~ x", OF conjI[OF _ R], rotated]
          converse_rtranclp_into_rtranclp[where r="(~)", OF ACIDZ.c])
  next
    case (i r)
    then show ?case
      by (auto intro: AAA)
  next
    case (z r s)
    then show ?case
      by (meson ACIDZ.z elim_zeros_ACIDZ_rtranclp)
  next
    case (d r s t)
    then show ?case
      by (induct "Conc r s" t rule: ACIDZ.induct)
        (force intro: exI[where P = "\<lambda>x. _ x \<and> _ ~ x", OF conjI[OF _ z], rotated]
          exI[where P = "\<lambda>x. _ x \<and> _ ~ x", OF conjI[OF _ z[OF elim_zeros_ACIDZ1]], rotated]
          distribute_ACIDZ1 elim!: rtranclp_trans)+
  next
    case (R r)
    then show ?case
      by auto
  next
    note A1 = ACIDZ.A[OF _ R]
    note A2 = ACIDZ.A[OF R]
    case (A r r' s s')
    from A(5,1-4) show ?case
    proof (induct "Alt r s" z rule: ACIDZ.induct)
      case inner: (a1 r'' s'')
      from A(1,3) show ?case
        unfolding inner.hyps[symmetric]
      proof (induct "Alt r'' s''" r' rule: ACIDZ.induct[consumes 1, case_names Xa1 Xa2 Xc Xi Xz Xd XR XA XC])
        case Xa1
        with A(3) show ?case
          by (elim exI[where P = "\<lambda>x. _ x \<and> _ ~ x", OF conjI[OF _ A2[OF A2]], rotated])
           (metis A1 a1 a2 r_into_rtranclp rtranclp.rtrancl_into_rtrancl)
      next
        case Xa2
        then show ?case
          by (elim exI[where P = "\<lambda>x. _ x \<and> _ ~ x", OF conjI[OF _ A2[OF A2]], rotated])
            (metis a1 A1 r_into_rtranclp rtranclp.rtrancl_into_rtrancl)
      next
        case Xc
        then show ?case
          by (elim exI[where P = "\<lambda>x. _ x \<and> _ ~ x", OF conjI[OF _ A2[OF A2]], rotated])
            (metis a1 c A1 r_into_rtranclp rtranclp.rtrancl_into_rtrancl)
      next
        case Xi
        then show ?case
          apply (elim exI[where P = "\<lambda>x. _ x \<and> _ ~ x", OF conjI[OF _ ACIDZ.A[OF i ACIDZ.A[OF i]]], rotated])
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
      next
        case Xz
        with A show ?case
          by (auto elim!: exI[where P = "\<lambda>x. _ x \<and> _ ~ x", OF conjI[OF _ z], rotated]
            converse_rtranclp_into_rtranclp[rotated, OF elim_zeros_ACIDZ_rtranclp]
            simp del: elim_zeros.simps)
      qed auto
    next
      case inner: (a2 s'' t'')
      from A(3,1) show ?case
        unfolding inner.hyps[symmetric]
      proof (induct "Alt s'' t''" s' rule: ACIDZ.induct[consumes 1, case_names Xa1 Xa2 Xc Xi Xz Xd XR XA XC])
        case Xa1
        with A(3) show ?case
          by (elim exI[where P = "\<lambda>x. _ x \<and> _ ~ x", OF conjI[OF _ A1[OF A1]], rotated])
            (metis a2 A2 r_into_rtranclp rtranclp.rtrancl_into_rtrancl)
      next
        case Xa2
        then show ?case
          by (elim exI[where P = "\<lambda>x. _ x \<and> _ ~ x", OF conjI[OF _ A1[OF A1]], rotated])
            (metis a1 a2 A2 r_into_rtranclp rtranclp.rtrancl_into_rtrancl)
      next
        case Xc
        then show ?case
          by (elim exI[where P = "\<lambda>x. _ x \<and> _ ~ x", OF conjI[OF _ A1[OF A1]], rotated])
            (metis a2 c A2 r_into_rtranclp rtranclp.rtrancl_into_rtrancl)
      next
        case Xi
        then show ?case
          apply (elim exI[where P = "\<lambda>x. _ x \<and> _ ~ x", OF conjI[OF _ ACIDZ.A[OF ACIDZ.A[OF _ i] i]], rotated])
          apply (rule converse_rtranclp_into_rtranclp, rule A2, rule a2)
          apply (rule converse_rtranclp_into_rtranclp, rule A2, rule A1, rule c)
          apply (rule converse_rtranclp_into_rtranclp, rule A2, rule a1)
          apply (rule converse_rtranclp_into_rtranclp, rule A2, rule A2, rule a1)
          apply (rule converse_rtranclp_into_rtranclp, rule A2, rule a2)
          apply (rule converse_rtranclp_into_rtranclp, rule a2)
          apply blast
          done
      next
        case Xz
        then show ?case
          by (auto elim!: exI[where P = "\<lambda>x. _ x \<and> _ ~ x", OF conjI[OF _ z], rotated]
            converse_rtranclp_into_rtranclp[rotated, OF elim_zeros_ACIDZ_rtranclp]
            simp del: elim_zeros.simps)
      qed auto
    next
      case (z rs) with A show ?case
        by (auto elim!: rtranclp_trans
          intro!: exI[where P = "\<lambda>x. _ x \<and> _ ~ x", OF conjI[OF _ elim_zeros_ACIDZ1], rotated])
    qed (auto 5 0 intro: AAA)
  next
    case (C r r' s s')
    from C(3,1-2) show ?case
      by (induct "Conc r s" s' rule: ACIDZ.induct)
        (auto intro: CCC elim!: rtranclp_trans
          exI[where P = "\<lambda>x. _ x \<and> _ ~ x", OF conjI[OF _ elim_zeros_ACIDZ1], rotated]
          exI[where P = "\<lambda>x. _ x \<and> _ ~ x", OF conjI[OF _ distribute_ACIDZ1], rotated])
  qed
qed

lemma confluent_quotient_ACIDZ:
  "confluent_quotient (~) (~~) (~~) (~~) (~~) (~~)
     (map_rexp fst) (map_rexp snd) (map_rexp fst) (map_rexp snd)
     rel_rexp rel_rexp rel_rexp set_rexp set_rexp"
  by unfold_locales
    (auto 4 4 dest: ACIDZ_set_rexp' simp: rexp.in_rel rexp.rel_compp dest: map_rexp_ACIDZ_inv intro: rtranclp_into_equivclp
      intro: equivpI reflpI sympI transpI ACIDZcl_map_respects
      strong_confluentp_imp_confluentp[OF strong_confluentp_ACIDZ])

lemma wide_intersection_finite_ACIDZ: "wide_intersection_finite (~~) map_rexp set_rexp"
  by unfold_locales
    (auto intro: ACIDZcl_map_respects rexp.map_cong simp: rexp.map_id rexp.set_map finite_set_rexp)

inductive ACIDZEQ (infix "\<approx>" 64) where
  a: "Alt (Alt r s) t \<approx> Alt r (Alt s t)"
| c: "Alt r s \<approx> Alt s r"
| i: "Alt r r \<approx> r"
| cz: "Conc Zero r \<approx> Zero"
| az: "Alt Zero r \<approx> r"
| d: "Conc (Alt r s) t \<approx> Alt (Conc r t) (Conc s t)"
| A: "r \<approx> r' \<Longrightarrow> s \<approx> s' \<Longrightarrow> Alt r s \<approx> Alt r' s'"
| C: "r \<approx> r' \<Longrightarrow> Conc r s \<approx> Conc r' s"
| r: "r \<approx> r"
| s: "r \<approx> s \<Longrightarrow> s \<approx> r"
| t: "r \<approx> s \<Longrightarrow> s \<approx> t \<Longrightarrow> r \<approx> t"

context begin

private lemma AA: "r ~~ r' \<Longrightarrow> s ~~ s' \<Longrightarrow> Alt r s ~~ Alt r' s'"
proof (induct rule: equivclp_induct)
  case base
  then show ?case
    by (induct rule: equivclp_induct) (auto elim!: equivclp_trans)
next
  case (step s t)
  then show ?case
    by (auto elim!: equivclp_trans)
qed

private lemma CC: "r ~~ r' \<Longrightarrow> Conc r s ~~ Conc r' s"
proof (induct rule: equivclp_induct)
  case base
  then show ?case
    by simp
next
  case (step s t)
  then show ?case
    by (auto elim!: equivclp_trans)
qed

private lemma CZ: "Conc Zero r ~~ Zero"
  by (smt (z3) R elim_zeros.simps(2) elim_zeros.simps(3) r_into_equivclp z)

private lemma AZ: "Alt Zero r ~~ r"
  by (smt (verit, ccfv_threshold) converse_r_into_equivclp converse_rtranclp_into_rtranclp
    elim_zeros.simps(1) elim_zeros.simps(3) equivclp_def symclpI1 z R)

private lemma D: "Conc (Alt r s) t ~~ Alt (Conc r t) (Conc s t)"
  by (smt (verit, ccfv_threshold) AA ACIDZ.d converse_r_into_equivclp distribute.simps(1)
    equivclp_sym rtranclp.simps rtranclp_equivclp)

lemma ACIDZEQ_le_ACIDZcl: "r \<approx> s \<Longrightarrow> r ~~ s"
  by (induct r s rule: ACIDZEQ.induct) (auto intro: AA CC AZ CZ D equivclp_sym equivclp_trans)

end

lemma ACIDZEQ_z[simp]: "r \<approx> elim_zeros r"
  by (induct r rule: elim_zeros.induct) (auto 0 3 intro: ACIDZEQ.intros simp: Let_def)

lemma ACIDZEQ_d[simp]: "Conc r s \<approx> distribute s r"
  by (induct s r rule: distribute.induct) (auto 0 3 intro: ACIDZEQ.intros)

lemma ACIDZ_le_ACIDZEQ: "r ~ s \<Longrightarrow> r \<approx> s"
  by (induct r s rule: ACIDZ.induct) (auto 0 2 intro: ACIDZEQ.intros simp: Let_def)

lemma ACIDZcl_le_ACIDZEQ: "r ~~ s \<Longrightarrow> r \<approx> s"
  by (induct rule: equivclp_induct) (auto 0 3 intro: ACIDZEQ.intros ACIDZ_le_ACIDZEQ)

lemma ACIDZEQ_alt: "(\<approx>) = (~~)"
  by (simp add: ACIDZEQ_le_ACIDZcl ACIDZcl_le_ACIDZEQ antisym predicate2I)

quotient_type 'a rexp_ACIDZ = "'a rexp" / "(\<approx>)"
  unfolding ACIDZEQ_alt by (auto intro!: equivpI reflpI sympI transpI)

lift_bnf 'a rexp_ACIDZ
  unfolding ACIDZEQ_alt
  subgoal for A Q by (rule confluent_quotient.subdistributivity[OF confluent_quotient_ACIDZ])
  subgoal for Ss by (elim wide_intersection_finite.wide_intersection[OF wide_intersection_finite_ACIDZ])
  done

datatype ldl = Prop string | And ldl ldl | Not ldl | Match "ldl rexp_ACIDZ"

end
