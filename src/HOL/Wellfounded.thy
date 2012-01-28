(*  Title:      HOL/Wellfounded.thy
    Author:     Tobias Nipkow
    Author:     Lawrence C Paulson
    Author:     Konrad Slind
    Author:     Alexander Krauss
*)

header {*Well-founded Recursion*}

theory Wellfounded
imports Transitive_Closure
uses ("Tools/Function/size.ML")
begin

subsection {* Basic Definitions *}

definition wf :: "('a * 'a) set => bool" where
  "wf r \<longleftrightarrow> (!P. (!x. (!y. (y,x):r --> P(y)) --> P(x)) --> (!x. P(x)))"

definition wfP :: "('a => 'a => bool) => bool" where
  "wfP r \<longleftrightarrow> wf {(x, y). r x y}"

lemma wfP_wf_eq [pred_set_conv]: "wfP (\<lambda>x y. (x, y) \<in> r) = wf r"
  by (simp add: wfP_def)

lemma wfUNIVI: 
   "(!!P x. (ALL x. (ALL y. (y,x) : r --> P(y)) --> P(x)) ==> P(x)) ==> wf(r)"
  unfolding wf_def by blast

lemmas wfPUNIVI = wfUNIVI [to_pred]

text{*Restriction to domain @{term A} and range @{term B}.  If @{term r} is
    well-founded over their intersection, then @{term "wf r"}*}
lemma wfI: 
 "[| r \<subseteq> A <*> B; 
     !!x P. [|\<forall>x. (\<forall>y. (y,x) : r --> P y) --> P x;  x : A; x : B |] ==> P x |]
  ==>  wf r"
  unfolding wf_def by blast

lemma wf_induct: 
    "[| wf(r);           
        !!x.[| ALL y. (y,x): r --> P(y) |] ==> P(x)  
     |]  ==>  P(a)"
  unfolding wf_def by blast

lemmas wfP_induct = wf_induct [to_pred]

lemmas wf_induct_rule = wf_induct [rule_format, consumes 1, case_names less, induct set: wf]

lemmas wfP_induct_rule = wf_induct_rule [to_pred, induct set: wfP]

lemma wf_not_sym: "wf r ==> (a, x) : r ==> (x, a) ~: r"
  by (induct a arbitrary: x set: wf) blast

lemma wf_asym:
  assumes "wf r" "(a, x) \<in> r"
  obtains "(x, a) \<notin> r"
  by (drule wf_not_sym[OF assms])

lemma wf_not_refl [simp]: "wf r ==> (a, a) ~: r"
  by (blast elim: wf_asym)

lemma wf_irrefl: assumes "wf r" obtains "(a, a) \<notin> r"
by (drule wf_not_refl[OF assms])

lemma wf_wellorderI:
  assumes wf: "wf {(x::'a::ord, y). x < y}"
  assumes lin: "OFCLASS('a::ord, linorder_class)"
  shows "OFCLASS('a::ord, wellorder_class)"
using lin by (rule wellorder_class.intro)
  (blast intro: class.wellorder_axioms.intro wf_induct_rule [OF wf])

lemma (in wellorder) wf:
  "wf {(x, y). x < y}"
unfolding wf_def by (blast intro: less_induct)


subsection {* Basic Results *}

text {* Point-free characterization of well-foundedness *}

lemma wfE_pf:
  assumes wf: "wf R"
  assumes a: "A \<subseteq> R `` A"
  shows "A = {}"
proof -
  { fix x
    from wf have "x \<notin> A"
    proof induct
      fix x assume "\<And>y. (y, x) \<in> R \<Longrightarrow> y \<notin> A"
      then have "x \<notin> R `` A" by blast
      with a show "x \<notin> A" by blast
    qed
  } thus ?thesis by auto
qed

lemma wfI_pf:
  assumes a: "\<And>A. A \<subseteq> R `` A \<Longrightarrow> A = {}"
  shows "wf R"
proof (rule wfUNIVI)
  fix P :: "'a \<Rightarrow> bool" and x
  let ?A = "{x. \<not> P x}"
  assume "\<forall>x. (\<forall>y. (y, x) \<in> R \<longrightarrow> P y) \<longrightarrow> P x"
  then have "?A \<subseteq> R `` ?A" by blast
  with a show "P x" by blast
qed

text{*Minimal-element characterization of well-foundedness*}

lemma wfE_min:
  assumes wf: "wf R" and Q: "x \<in> Q"
  obtains z where "z \<in> Q" "\<And>y. (y, z) \<in> R \<Longrightarrow> y \<notin> Q"
  using Q wfE_pf[OF wf, of Q] by blast

lemma wfI_min:
  assumes a: "\<And>x Q. x \<in> Q \<Longrightarrow> \<exists>z\<in>Q. \<forall>y. (y, z) \<in> R \<longrightarrow> y \<notin> Q"
  shows "wf R"
proof (rule wfI_pf)
  fix A assume b: "A \<subseteq> R `` A"
  { fix x assume "x \<in> A"
    from a[OF this] b have "False" by blast
  }
  thus "A = {}" by blast
qed

lemma wf_eq_minimal: "wf r = (\<forall>Q x. x\<in>Q --> (\<exists>z\<in>Q. \<forall>y. (y,z)\<in>r --> y\<notin>Q))"
apply auto
apply (erule wfE_min, assumption, blast)
apply (rule wfI_min, auto)
done

lemmas wfP_eq_minimal = wf_eq_minimal [to_pred]

text{* Well-foundedness of transitive closure *}

lemma wf_trancl:
  assumes "wf r"
  shows "wf (r^+)"
proof -
  {
    fix P and x
    assume induct_step: "!!x. (!!y. (y, x) : r^+ ==> P y) ==> P x"
    have "P x"
    proof (rule induct_step)
      fix y assume "(y, x) : r^+"
      with `wf r` show "P y"
      proof (induct x arbitrary: y)
        case (less x)
        note hyp = `\<And>x' y'. (x', x) : r ==> (y', x') : r^+ ==> P y'`
        from `(y, x) : r^+` show "P y"
        proof cases
          case base
          show "P y"
          proof (rule induct_step)
            fix y' assume "(y', y) : r^+"
            with `(y, x) : r` show "P y'" by (rule hyp [of y y'])
          qed
        next
          case step
          then obtain x' where "(x', x) : r" and "(y, x') : r^+" by simp
          then show "P y" by (rule hyp [of x' y])
        qed
      qed
    qed
  } then show ?thesis unfolding wf_def by blast
qed

lemmas wfP_trancl = wf_trancl [to_pred]

lemma wf_converse_trancl: "wf (r^-1) ==> wf ((r^+)^-1)"
  apply (subst trancl_converse [symmetric])
  apply (erule wf_trancl)
  done

text {* Well-foundedness of subsets *}

lemma wf_subset: "[| wf(r);  p<=r |] ==> wf(p)"
  apply (simp (no_asm_use) add: wf_eq_minimal)
  apply fast
  done

lemmas wfP_subset = wf_subset [to_pred]

text {* Well-foundedness of the empty relation *}

lemma wf_empty [iff]: "wf {}"
  by (simp add: wf_def)

lemma wfP_empty [iff]:
  "wfP (\<lambda>x y. False)"
proof -
  have "wfP bot" by (fact wf_empty [to_pred bot_empty_eq2])
  then show ?thesis by (simp add: bot_fun_def)
qed

lemma wf_Int1: "wf r ==> wf (r Int r')"
  apply (erule wf_subset)
  apply (rule Int_lower1)
  done

lemma wf_Int2: "wf r ==> wf (r' Int r)"
  apply (erule wf_subset)
  apply (rule Int_lower2)
  done  

text {* Exponentiation *}

lemma wf_exp:
  assumes "wf (R ^^ n)"
  shows "wf R"
proof (rule wfI_pf)
  fix A assume "A \<subseteq> R `` A"
  then have "A \<subseteq> (R ^^ n) `` A" by (induct n) force+
  with `wf (R ^^ n)`
  show "A = {}" by (rule wfE_pf)
qed

text {* Well-foundedness of insert *}

lemma wf_insert [iff]: "wf(insert (y,x) r) = (wf(r) & (x,y) ~: r^*)"
apply (rule iffI)
 apply (blast elim: wf_trancl [THEN wf_irrefl]
              intro: rtrancl_into_trancl1 wf_subset 
                     rtrancl_mono [THEN [2] rev_subsetD])
apply (simp add: wf_eq_minimal, safe)
apply (rule allE, assumption, erule impE, blast) 
apply (erule bexE)
apply (rename_tac "a", case_tac "a = x")
 prefer 2
apply blast 
apply (case_tac "y:Q")
 prefer 2 apply blast
apply (rule_tac x = "{z. z:Q & (z,y) : r^*}" in allE)
 apply assumption
apply (erule_tac V = "ALL Q. (EX x. x : Q) --> ?P Q" in thin_rl) 
  --{*essential for speed*}
txt{*Blast with new substOccur fails*}
apply (fast intro: converse_rtrancl_into_rtrancl)
done

text{*Well-foundedness of image*}

lemma wf_map_pair_image: "[| wf r; inj f |] ==> wf(map_pair f f ` r)"
apply (simp only: wf_eq_minimal, clarify)
apply (case_tac "EX p. f p : Q")
apply (erule_tac x = "{p. f p : Q}" in allE)
apply (fast dest: inj_onD, blast)
done


subsection {* Well-Foundedness Results for Unions *}

lemma wf_union_compatible:
  assumes "wf R" "wf S"
  assumes "R O S \<subseteq> R"
  shows "wf (R \<union> S)"
proof (rule wfI_min)
  fix x :: 'a and Q 
  let ?Q' = "{x \<in> Q. \<forall>y. (y, x) \<in> R \<longrightarrow> y \<notin> Q}"
  assume "x \<in> Q"
  obtain a where "a \<in> ?Q'"
    by (rule wfE_min [OF `wf R` `x \<in> Q`]) blast
  with `wf S`
  obtain z where "z \<in> ?Q'" and zmin: "\<And>y. (y, z) \<in> S \<Longrightarrow> y \<notin> ?Q'" by (erule wfE_min)
  { 
    fix y assume "(y, z) \<in> S"
    then have "y \<notin> ?Q'" by (rule zmin)

    have "y \<notin> Q"
    proof 
      assume "y \<in> Q"
      with `y \<notin> ?Q'` 
      obtain w where "(w, y) \<in> R" and "w \<in> Q" by auto
      from `(w, y) \<in> R` `(y, z) \<in> S` have "(w, z) \<in> R O S" by (rule rel_compI)
      with `R O S \<subseteq> R` have "(w, z) \<in> R" ..
      with `z \<in> ?Q'` have "w \<notin> Q" by blast 
      with `w \<in> Q` show False by contradiction
    qed
  }
  with `z \<in> ?Q'` show "\<exists>z\<in>Q. \<forall>y. (y, z) \<in> R \<union> S \<longrightarrow> y \<notin> Q" by blast
qed


text {* Well-foundedness of indexed union with disjoint domains and ranges *}

lemma wf_UN: "[| ALL i:I. wf(r i);  
         ALL i:I. ALL j:I. r i ~= r j --> Domain(r i) Int Range(r j) = {}  
      |] ==> wf(UN i:I. r i)"
apply (simp only: wf_eq_minimal, clarify)
apply (rename_tac A a, case_tac "EX i:I. EX a:A. EX b:A. (b,a) : r i")
 prefer 2
 apply force 
apply clarify
apply (drule bspec, assumption)  
apply (erule_tac x="{a. a:A & (EX b:A. (b,a) : r i) }" in allE)
apply (blast elim!: allE)  
done

lemma wfP_SUP:
  "\<forall>i. wfP (r i) \<Longrightarrow> \<forall>i j. r i \<noteq> r j \<longrightarrow> inf (DomainP (r i)) (RangeP (r j)) = bot \<Longrightarrow> wfP (SUPR UNIV r)"
  apply (rule wf_UN [where I=UNIV and r="\<lambda>i. {(x, y). r i x y}", to_pred])
  apply (simp_all add: inf_set_def)
  apply auto
  done

lemma wf_Union: 
 "[| ALL r:R. wf r;  
     ALL r:R. ALL s:R. r ~= s --> Domain r Int Range s = {}  
  |] ==> wf(Union R)"
  using wf_UN[of R "\<lambda>i. i"] by (simp add: SUP_def)

(*Intuition: we find an (R u S)-min element of a nonempty subset A
             by case distinction.
  1. There is a step a -R-> b with a,b : A.
     Pick an R-min element z of the (nonempty) set {a:A | EX b:A. a -R-> b}.
     By definition, there is z':A s.t. z -R-> z'. Because z is R-min in the
     subset, z' must be R-min in A. Because z' has an R-predecessor, it cannot
     have an S-successor and is thus S-min in A as well.
  2. There is no such step.
     Pick an S-min element of A. In this case it must be an R-min
     element of A as well.

*)
lemma wf_Un:
     "[| wf r; wf s; Domain r Int Range s = {} |] ==> wf(r Un s)"
  using wf_union_compatible[of s r] 
  by (auto simp: Un_ac)

lemma wf_union_merge: 
  "wf (R \<union> S) = wf (R O R \<union> S O R \<union> S)" (is "wf ?A = wf ?B")
proof
  assume "wf ?A"
  with wf_trancl have wfT: "wf (?A^+)" .
  moreover have "?B \<subseteq> ?A^+"
    by (subst trancl_unfold, subst trancl_unfold) blast
  ultimately show "wf ?B" by (rule wf_subset)
next
  assume "wf ?B"

  show "wf ?A"
  proof (rule wfI_min)
    fix Q :: "'a set" and x 
    assume "x \<in> Q"

    with `wf ?B`
    obtain z where "z \<in> Q" and "\<And>y. (y, z) \<in> ?B \<Longrightarrow> y \<notin> Q" 
      by (erule wfE_min)
    then have A1: "\<And>y. (y, z) \<in> R O R \<Longrightarrow> y \<notin> Q"
      and A2: "\<And>y. (y, z) \<in> S O R \<Longrightarrow> y \<notin> Q"
      and A3: "\<And>y. (y, z) \<in> S \<Longrightarrow> y \<notin> Q"
      by auto
    
    show "\<exists>z\<in>Q. \<forall>y. (y, z) \<in> ?A \<longrightarrow> y \<notin> Q"
    proof (cases "\<forall>y. (y, z) \<in> R \<longrightarrow> y \<notin> Q")
      case True
      with `z \<in> Q` A3 show ?thesis by blast
    next
      case False 
      then obtain z' where "z'\<in>Q" "(z', z) \<in> R" by blast

      have "\<forall>y. (y, z') \<in> ?A \<longrightarrow> y \<notin> Q"
      proof (intro allI impI)
        fix y assume "(y, z') \<in> ?A"
        then show "y \<notin> Q"
        proof
          assume "(y, z') \<in> R" 
          then have "(y, z) \<in> R O R" using `(z', z) \<in> R` ..
          with A1 show "y \<notin> Q" .
        next
          assume "(y, z') \<in> S" 
          then have "(y, z) \<in> S O R" using  `(z', z) \<in> R` ..
          with A2 show "y \<notin> Q" .
        qed
      qed
      with `z' \<in> Q` show ?thesis ..
    qed
  qed
qed

lemma wf_comp_self: "wf R = wf (R O R)"  -- {* special case *}
  by (rule wf_union_merge [where S = "{}", simplified])


subsection {* Acyclic relations *}

lemma wf_acyclic: "wf r ==> acyclic r"
apply (simp add: acyclic_def)
apply (blast elim: wf_trancl [THEN wf_irrefl])
done

lemmas wfP_acyclicP = wf_acyclic [to_pred]

text{* Wellfoundedness of finite acyclic relations*}

lemma finite_acyclic_wf [rule_format]: "finite r ==> acyclic r --> wf r"
apply (erule finite_induct, blast)
apply (simp (no_asm_simp) only: split_tupled_all)
apply simp
done

lemma finite_acyclic_wf_converse: "[|finite r; acyclic r|] ==> wf (r^-1)"
apply (erule finite_converse [THEN iffD2, THEN finite_acyclic_wf])
apply (erule acyclic_converse [THEN iffD2])
done

lemma wf_iff_acyclic_if_finite: "finite r ==> wf r = acyclic r"
by (blast intro: finite_acyclic_wf wf_acyclic)


subsection {* @{typ nat} is well-founded *}

lemma less_nat_rel: "op < = (\<lambda>m n. n = Suc m)^++"
proof (rule ext, rule ext, rule iffI)
  fix n m :: nat
  assume "m < n"
  then show "(\<lambda>m n. n = Suc m)^++ m n"
  proof (induct n)
    case 0 then show ?case by auto
  next
    case (Suc n) then show ?case
      by (auto simp add: less_Suc_eq_le le_less intro: tranclp.trancl_into_trancl)
  qed
next
  fix n m :: nat
  assume "(\<lambda>m n. n = Suc m)^++ m n"
  then show "m < n"
    by (induct n)
      (simp_all add: less_Suc_eq_le reflexive le_less)
qed

definition
  pred_nat :: "(nat * nat) set" where
  "pred_nat = {(m, n). n = Suc m}"

definition
  less_than :: "(nat * nat) set" where
  "less_than = pred_nat^+"

lemma less_eq: "(m, n) \<in> pred_nat^+ \<longleftrightarrow> m < n"
  unfolding less_nat_rel pred_nat_def trancl_def by simp

lemma pred_nat_trancl_eq_le:
  "(m, n) \<in> pred_nat^* \<longleftrightarrow> m \<le> n"
  unfolding less_eq rtrancl_eq_or_trancl by auto

lemma wf_pred_nat: "wf pred_nat"
  apply (unfold wf_def pred_nat_def, clarify)
  apply (induct_tac x, blast+)
  done

lemma wf_less_than [iff]: "wf less_than"
  by (simp add: less_than_def wf_pred_nat [THEN wf_trancl])

lemma trans_less_than [iff]: "trans less_than"
  by (simp add: less_than_def)

lemma less_than_iff [iff]: "((x,y): less_than) = (x<y)"
  by (simp add: less_than_def less_eq)

lemma wf_less: "wf {(x, y::nat). x < y}"
  using wf_less_than by (simp add: less_than_def less_eq [symmetric])


subsection {* Accessible Part *}

text {*
 Inductive definition of the accessible part @{term "acc r"} of a
 relation; see also \cite{paulin-tlca}.
*}

inductive_set
  acc :: "('a * 'a) set => 'a set"
  for r :: "('a * 'a) set"
  where
    accI: "(!!y. (y, x) : r ==> y : acc r) ==> x : acc r"

abbreviation
  termip :: "('a => 'a => bool) => 'a => bool" where
  "termip r \<equiv> accp (r\<inverse>\<inverse>)"

abbreviation
  termi :: "('a * 'a) set => 'a set" where
  "termi r \<equiv> acc (r\<inverse>)"

lemmas accpI = accp.accI

text {* Induction rules *}

theorem accp_induct:
  assumes major: "accp r a"
  assumes hyp: "!!x. accp r x ==> \<forall>y. r y x --> P y ==> P x"
  shows "P a"
  apply (rule major [THEN accp.induct])
  apply (rule hyp)
   apply (rule accp.accI)
   apply fast
  apply fast
  done

theorems accp_induct_rule = accp_induct [rule_format, induct set: accp]

theorem accp_downward: "accp r b ==> r a b ==> accp r a"
  apply (erule accp.cases)
  apply fast
  done

lemma not_accp_down:
  assumes na: "\<not> accp R x"
  obtains z where "R z x" and "\<not> accp R z"
proof -
  assume a: "\<And>z. \<lbrakk>R z x; \<not> accp R z\<rbrakk> \<Longrightarrow> thesis"

  show thesis
  proof (cases "\<forall>z. R z x \<longrightarrow> accp R z")
    case True
    hence "\<And>z. R z x \<Longrightarrow> accp R z" by auto
    hence "accp R x"
      by (rule accp.accI)
    with na show thesis ..
  next
    case False then obtain z where "R z x" and "\<not> accp R z"
      by auto
    with a show thesis .
  qed
qed

lemma accp_downwards_aux: "r\<^sup>*\<^sup>* b a ==> accp r a --> accp r b"
  apply (erule rtranclp_induct)
   apply blast
  apply (blast dest: accp_downward)
  done

theorem accp_downwards: "accp r a ==> r\<^sup>*\<^sup>* b a ==> accp r b"
  apply (blast dest: accp_downwards_aux)
  done

theorem accp_wfPI: "\<forall>x. accp r x ==> wfP r"
  apply (rule wfPUNIVI)
  apply (rule_tac P=P in accp_induct)
   apply blast
  apply blast
  done

theorem accp_wfPD: "wfP r ==> accp r x"
  apply (erule wfP_induct_rule)
  apply (rule accp.accI)
  apply blast
  done

theorem wfP_accp_iff: "wfP r = (\<forall>x. accp r x)"
  apply (blast intro: accp_wfPI dest: accp_wfPD)
  done


text {* Smaller relations have bigger accessible parts: *}

lemma accp_subset:
  assumes sub: "R1 \<le> R2"
  shows "accp R2 \<le> accp R1"
proof (rule predicate1I)
  fix x assume "accp R2 x"
  then show "accp R1 x"
  proof (induct x)
    fix x
    assume ih: "\<And>y. R2 y x \<Longrightarrow> accp R1 y"
    with sub show "accp R1 x"
      by (blast intro: accp.accI)
  qed
qed


text {* This is a generalized induction theorem that works on
  subsets of the accessible part. *}

lemma accp_subset_induct:
  assumes subset: "D \<le> accp R"
    and dcl: "\<And>x z. \<lbrakk>D x; R z x\<rbrakk> \<Longrightarrow> D z"
    and "D x"
    and istep: "\<And>x. \<lbrakk>D x; (\<And>z. R z x \<Longrightarrow> P z)\<rbrakk> \<Longrightarrow> P x"
  shows "P x"
proof -
  from subset and `D x`
  have "accp R x" ..
  then show "P x" using `D x`
  proof (induct x)
    fix x
    assume "D x"
      and "\<And>y. R y x \<Longrightarrow> D y \<Longrightarrow> P y"
    with dcl and istep show "P x" by blast
  qed
qed


text {* Set versions of the above theorems *}

lemmas acc_induct = accp_induct [to_set]

lemmas acc_induct_rule = acc_induct [rule_format, induct set: acc]

lemmas acc_downward = accp_downward [to_set]

lemmas not_acc_down = not_accp_down [to_set]

lemmas acc_downwards_aux = accp_downwards_aux [to_set]

lemmas acc_downwards = accp_downwards [to_set]

lemmas acc_wfI = accp_wfPI [to_set]

lemmas acc_wfD = accp_wfPD [to_set]

lemmas wf_acc_iff = wfP_accp_iff [to_set]

lemmas acc_subset = accp_subset [to_set]

lemmas acc_subset_induct = accp_subset_induct [to_set]


subsection {* Tools for building wellfounded relations *}

text {* Inverse Image *}

lemma wf_inv_image [simp,intro!]: "wf(r) ==> wf(inv_image r (f::'a=>'b))"
apply (simp (no_asm_use) add: inv_image_def wf_eq_minimal)
apply clarify
apply (subgoal_tac "EX (w::'b) . w : {w. EX (x::'a) . x: Q & (f x = w) }")
prefer 2 apply (blast del: allE)
apply (erule allE)
apply (erule (1) notE impE)
apply blast
done

text {* Measure functions into @{typ nat} *}

definition measure :: "('a => nat) => ('a * 'a)set"
where "measure = inv_image less_than"

lemma in_measure[simp]: "((x,y) : measure f) = (f x < f y)"
  by (simp add:measure_def)

lemma wf_measure [iff]: "wf (measure f)"
apply (unfold measure_def)
apply (rule wf_less_than [THEN wf_inv_image])
done

lemma wf_if_measure: fixes f :: "'a \<Rightarrow> nat"
shows "(!!x. P x \<Longrightarrow> f(g x) < f x) \<Longrightarrow> wf {(y,x). P x \<and> y = g x}"
apply(insert wf_measure[of f])
apply(simp only: measure_def inv_image_def less_than_def less_eq)
apply(erule wf_subset)
apply auto
done


text{* Lexicographic combinations *}

definition lex_prod :: "('a \<times>'a) set \<Rightarrow> ('b \<times> 'b) set \<Rightarrow> (('a \<times> 'b) \<times> ('a \<times> 'b)) set" (infixr "<*lex*>" 80) where
  "ra <*lex*> rb = {((a, b), (a', b')). (a, a') \<in> ra \<or> a = a' \<and> (b, b') \<in> rb}"

lemma wf_lex_prod [intro!]: "[| wf(ra); wf(rb) |] ==> wf(ra <*lex*> rb)"
apply (unfold wf_def lex_prod_def) 
apply (rule allI, rule impI)
apply (simp (no_asm_use) only: split_paired_All)
apply (drule spec, erule mp) 
apply (rule allI, rule impI)
apply (drule spec, erule mp, blast) 
done

lemma in_lex_prod[simp]: 
  "(((a,b),(a',b')): r <*lex*> s) = ((a,a'): r \<or> (a = a' \<and> (b, b') : s))"
  by (auto simp:lex_prod_def)

text{* @{term "op <*lex*>"} preserves transitivity *}

lemma trans_lex_prod [intro!]: 
    "[| trans R1; trans R2 |] ==> trans (R1 <*lex*> R2)"
by (unfold trans_def lex_prod_def, blast) 

text {* lexicographic combinations with measure functions *}

definition 
  mlex_prod :: "('a \<Rightarrow> nat) \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> ('a \<times> 'a) set" (infixr "<*mlex*>" 80)
where
  "f <*mlex*> R = inv_image (less_than <*lex*> R) (%x. (f x, x))"

lemma wf_mlex: "wf R \<Longrightarrow> wf (f <*mlex*> R)"
unfolding mlex_prod_def
by auto

lemma mlex_less: "f x < f y \<Longrightarrow> (x, y) \<in> f <*mlex*> R"
unfolding mlex_prod_def by simp

lemma mlex_leq: "f x \<le> f y \<Longrightarrow> (x, y) \<in> R \<Longrightarrow> (x, y) \<in> f <*mlex*> R"
unfolding mlex_prod_def by auto

text {* proper subset relation on finite sets *}

definition finite_psubset  :: "('a set * 'a set) set"
where "finite_psubset = {(A,B). A < B & finite B}"

lemma wf_finite_psubset[simp]: "wf(finite_psubset)"
apply (unfold finite_psubset_def)
apply (rule wf_measure [THEN wf_subset])
apply (simp add: measure_def inv_image_def less_than_def less_eq)
apply (fast elim!: psubset_card_mono)
done

lemma trans_finite_psubset: "trans finite_psubset"
by (simp add: finite_psubset_def less_le trans_def, blast)

lemma in_finite_psubset[simp]: "(A, B) \<in> finite_psubset = (A < B & finite B)"
unfolding finite_psubset_def by auto

text {* max- and min-extension of order to finite sets *}

inductive_set max_ext :: "('a \<times> 'a) set \<Rightarrow> ('a set \<times> 'a set) set" 
for R :: "('a \<times> 'a) set"
where
  max_extI[intro]: "finite X \<Longrightarrow> finite Y \<Longrightarrow> Y \<noteq> {} \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> \<exists>y\<in>Y. (x, y) \<in> R) \<Longrightarrow> (X, Y) \<in> max_ext R"

lemma max_ext_wf:
  assumes wf: "wf r"
  shows "wf (max_ext r)"
proof (rule acc_wfI, intro allI)
  fix M show "M \<in> acc (max_ext r)" (is "_ \<in> ?W")
  proof cases
    assume "finite M"
    thus ?thesis
    proof (induct M)
      show "{} \<in> ?W"
        by (rule accI) (auto elim: max_ext.cases)
    next
      fix M a assume "M \<in> ?W" "finite M"
      with wf show "insert a M \<in> ?W"
      proof (induct arbitrary: M)
        fix M a
        assume "M \<in> ?W"  and  [intro]: "finite M"
        assume hyp: "\<And>b M. (b, a) \<in> r \<Longrightarrow> M \<in> ?W \<Longrightarrow> finite M \<Longrightarrow> insert b M \<in> ?W"
        {
          fix N M :: "'a set"
          assume "finite N" "finite M"
          then
          have "\<lbrakk>M \<in> ?W ; (\<And>y. y \<in> N \<Longrightarrow> (y, a) \<in> r)\<rbrakk> \<Longrightarrow>  N \<union> M \<in> ?W"
            by (induct N arbitrary: M) (auto simp: hyp)
        }
        note add_less = this
        
        show "insert a M \<in> ?W"
        proof (rule accI)
          fix N assume Nless: "(N, insert a M) \<in> max_ext r"
          hence asm1: "\<And>x. x \<in> N \<Longrightarrow> (x, a) \<in> r \<or> (\<exists>y \<in> M. (x, y) \<in> r)"
            by (auto elim!: max_ext.cases)

          let ?N1 = "{ n \<in> N. (n, a) \<in> r }"
          let ?N2 = "{ n \<in> N. (n, a) \<notin> r }"
          have N: "?N1 \<union> ?N2 = N" by (rule set_eqI) auto
          from Nless have "finite N" by (auto elim: max_ext.cases)
          then have finites: "finite ?N1" "finite ?N2" by auto
          
          have "?N2 \<in> ?W"
          proof cases
            assume [simp]: "M = {}"
            have Mw: "{} \<in> ?W" by (rule accI) (auto elim: max_ext.cases)

            from asm1 have "?N2 = {}" by auto
            with Mw show "?N2 \<in> ?W" by (simp only:)
          next
            assume "M \<noteq> {}"
            have N2: "(?N2, M) \<in> max_ext r" 
              by (rule max_extI[OF _ _ `M \<noteq> {}`]) (insert asm1, auto intro: finites)
            
            with `M \<in> ?W` show "?N2 \<in> ?W" by (rule acc_downward)
          qed
          with finites have "?N1 \<union> ?N2 \<in> ?W" 
            by (rule add_less) simp
          then show "N \<in> ?W" by (simp only: N)
        qed
      qed
    qed
  next
    assume [simp]: "\<not> finite M"
    show ?thesis
      by (rule accI) (auto elim: max_ext.cases)
  qed
qed

lemma max_ext_additive: 
 "(A, B) \<in> max_ext R \<Longrightarrow> (C, D) \<in> max_ext R \<Longrightarrow>
  (A \<union> C, B \<union> D) \<in> max_ext R"
by (force elim!: max_ext.cases)


definition min_ext :: "('a \<times> 'a) set \<Rightarrow> ('a set \<times> 'a set) set"  where
  "min_ext r = {(X, Y) | X Y. X \<noteq> {} \<and> (\<forall>y \<in> Y. (\<exists>x \<in> X. (x, y) \<in> r))}"

lemma min_ext_wf:
  assumes "wf r"
  shows "wf (min_ext r)"
proof (rule wfI_min)
  fix Q :: "'a set set"
  fix x
  assume nonempty: "x \<in> Q"
  show "\<exists>m \<in> Q. (\<forall> n. (n, m) \<in> min_ext r \<longrightarrow> n \<notin> Q)"
  proof cases
    assume "Q = {{}}" thus ?thesis by (simp add: min_ext_def)
  next
    assume "Q \<noteq> {{}}"
    with nonempty
    obtain e x where "x \<in> Q" "e \<in> x" by force
    then have eU: "e \<in> \<Union>Q" by auto
    with `wf r` 
    obtain z where z: "z \<in> \<Union>Q" "\<And>y. (y, z) \<in> r \<Longrightarrow> y \<notin> \<Union>Q" 
      by (erule wfE_min)
    from z obtain m where "m \<in> Q" "z \<in> m" by auto
    from `m \<in> Q`
    show ?thesis
    proof (rule, intro bexI allI impI)
      fix n
      assume smaller: "(n, m) \<in> min_ext r"
      with `z \<in> m` obtain y where y: "y \<in> n" "(y, z) \<in> r" by (auto simp: min_ext_def)
      then show "n \<notin> Q" using z(2) by auto
    qed      
  qed
qed

text{* Bounded increase must terminate: *}

lemma wf_bounded_measure:
fixes ub :: "'a \<Rightarrow> nat" and f :: "'a \<Rightarrow> nat"
assumes "!!a b. (b,a) : r \<Longrightarrow> ub b \<le> ub a & ub a \<ge> f b & f b > f a"
shows "wf r"
apply(rule wf_subset[OF wf_measure[of "%a. ub a - f a"]])
apply (auto dest: assms)
done

lemma wf_bounded_set:
fixes ub :: "'a \<Rightarrow> 'b set" and f :: "'a \<Rightarrow> 'b set"
assumes "!!a b. (b,a) : r \<Longrightarrow>
  finite(ub a) & ub b \<subseteq> ub a & ub a \<supseteq> f b & f b \<supset> f a"
shows "wf r"
apply(rule wf_bounded_measure[of r "%a. card(ub a)" "%a. card(f a)"])
apply(drule assms)
apply (blast intro: card_mono finite_subset psubset_card_mono dest: psubset_eq[THEN iffD2])
done


subsection {* size of a datatype value *}

use "Tools/Function/size.ML"

setup Size.setup

lemma size_bool [code]:
  "size (b\<Colon>bool) = 0" by (cases b) auto

lemma nat_size [simp, code]: "size (n\<Colon>nat) = n"
  by (induct n) simp_all

declare "prod.size" [no_atp]

lemma [code]:
  "size (P :: 'a Predicate.pred) = 0" by (cases P) simp

lemma [code]:
  "pred_size f P = 0" by (cases P) simp

end
