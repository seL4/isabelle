(*  Title:      HOL/Lambda/WeakNorm.thy
    ID:         $Id$
    Author:     Stefan Berghofer
    Copyright   2003 TU Muenchen
*)

header {* Weak normalization for simply-typed lambda calculus *}

theory WeakNorm = Type:

text {*
Formalization by Stefan Berghofer. Partly based on a paper proof by
Felix Joachimski and Ralph Matthes \cite{Matthes-Joachimski-AML}.
*}


subsection {* Terms in normal form *}

constdefs
  listall :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool"
  "listall P xs \<equiv> (\<forall>i. i < length xs \<longrightarrow> P (xs ! i))"

declare listall_def [extraction_expand]

theorem listall_nil: "listall P []"
  by (simp add: listall_def)

theorem listall_nil_eq [simp]: "listall P [] = True"
  by (rules intro: listall_nil)

theorem listall_cons: "P x \<Longrightarrow> listall P xs \<Longrightarrow> listall P (x # xs)"
  apply (simp add: listall_def)
  apply (rule allI impI)+
  apply (case_tac i)
  apply simp+
  done

theorem listall_cons_eq [simp]: "listall P (x # xs) = (P x \<and> listall P xs)"
  apply (rule iffI)
  prefer 2
  apply (erule conjE)
  apply (erule listall_cons)
  apply assumption
  apply (unfold listall_def)
  apply (rule conjI)
  apply (erule_tac x=0 in allE)
  apply simp
  apply simp
  apply (rule allI)
  apply (erule_tac x="Suc i" in allE)
  apply simp
  done

lemma listall_conj1: "listall (\<lambda>x. P x \<and> Q x) xs \<Longrightarrow> listall P xs"
  by (induct xs) simp+

lemma listall_conj2: "listall (\<lambda>x. P x \<and> Q x) xs \<Longrightarrow> listall Q xs"
  by (induct xs) simp+

lemma listall_app: "listall P (xs @ ys) = (listall P xs \<and> listall P ys)"
  apply (induct xs)
  apply (rule iffI, simp, simp)
  apply (rule iffI, simp, simp)
  done

lemma listall_snoc [simp]: "listall P (xs @ [x]) = (listall P xs \<and> P x)"
  apply (rule iffI)
  apply (simp add: listall_app)+
  done

lemma listall_cong [cong, extraction_expand]:
  "xs = ys \<Longrightarrow> listall P xs = listall P ys"
  -- {* Currently needed for strange technical reasons *}
  by (unfold listall_def) simp

consts NF :: "dB set"
inductive NF
intros
  App: "listall (\<lambda>t. t \<in> NF) ts \<Longrightarrow> Var x \<degree>\<degree> ts \<in> NF"
  Abs: "t \<in> NF \<Longrightarrow> Abs t \<in> NF"
monos listall_def

lemma nat_eq_dec: "\<And>n::nat. m = n \<or> m \<noteq> n"
  apply (induct m)
  apply (case_tac n)
  apply (case_tac [3] na)
  apply (simp only: nat.simps, rules?)+
  done

lemma nat_le_dec: "\<And>n::nat. m < n \<or> \<not> (m < n)"
  apply (induct m)
  apply (case_tac n)
  apply (case_tac [3] na)
  apply (simp del: simp_thms, rules?)+
  done

lemma App_NF_D: assumes NF: "Var n \<degree>\<degree> ts \<in> NF"
  shows "listall (\<lambda>t. t \<in> NF) ts" using NF
  by cases simp_all


subsection {* Properties of @{text NF} *}

lemma Var_NF: "Var n \<in> NF"
  apply (subgoal_tac "Var n \<degree>\<degree> [] \<in> NF")
   apply simp
  apply (rule NF.App)
  apply simp
  done

lemma subst_terms_NF: "listall (\<lambda>t. t \<in> NF) ts \<Longrightarrow>
  listall (\<lambda>t. \<forall>i j. t[Var i/j] \<in> NF) ts \<Longrightarrow>
  listall (\<lambda>t. t \<in> NF) (map (\<lambda>t. t[Var i/j]) ts)"
  by (induct ts) simp+

lemma subst_Var_NF: "t \<in> NF \<Longrightarrow> (\<And>i j. t[Var i/j] \<in> NF)"
  apply (induct set: NF)
  apply simp
  apply (frule listall_conj1)
  apply (drule listall_conj2)
  apply (drule_tac i=i and j=j in subst_terms_NF)
  apply assumption
  apply (rule_tac m=x and n=j in nat_eq_dec [THEN disjE, standard])
  apply simp
  apply (erule NF.App)
  apply (rule_tac m=j and n=x in nat_le_dec [THEN disjE, standard])
  apply simp
  apply (rules intro: NF.App)
  apply simp
  apply (rules intro: NF.App)
  apply simp
  apply (rules intro: NF.Abs)
  done

lemma app_Var_NF: "t \<in> NF \<Longrightarrow> \<exists>t'. t \<degree> Var i \<rightarrow>\<^sub>\<beta>\<^sup>* t' \<and> t' \<in> NF"
  apply (induct set: NF)
  apply (subst app_last)
  apply (rule exI)
  apply (rule conjI)
  apply (rule rtrancl_refl)
  apply (rule NF.App)
  apply (drule listall_conj1)
  apply (simp add: listall_app)
  apply (rule Var_NF)
  apply (rule exI)
  apply (rule conjI)
  apply (rule rtrancl_into_rtrancl)
  apply (rule rtrancl_refl)
  apply (rule beta)
  apply (erule subst_Var_NF)
  done

lemma lift_terms_NF: "listall (\<lambda>t. t \<in> NF) ts \<Longrightarrow>
  listall (\<lambda>t. \<forall>i. lift t i \<in> NF) ts \<Longrightarrow>
  listall (\<lambda>t. t \<in> NF) (map (\<lambda>t. lift t i) ts)"
  by (induct ts) simp+

lemma lift_NF: "t \<in> NF \<Longrightarrow> (\<And>i. lift t i \<in> NF)"
  apply (induct set: NF)
  apply (frule listall_conj1)
  apply (drule listall_conj2)
  apply (drule_tac i=i in lift_terms_NF)
  apply assumption
  apply (rule_tac m=x and n=i in nat_le_dec [THEN disjE, standard])
  apply simp
  apply (rule NF.App)
  apply assumption
  apply simp
  apply (rule NF.App)
  apply assumption
  apply simp
  apply (rule NF.Abs)
  apply simp
  done


subsection {* Main theorems *}

lemma subst_type_NF:
  "\<And>t e T u i. t \<in> NF \<Longrightarrow> e\<langle>i:U\<rangle> \<turnstile> t : T \<Longrightarrow> u \<in> NF \<Longrightarrow> e \<turnstile> u : U \<Longrightarrow> \<exists>t'. t[u/i] \<rightarrow>\<^sub>\<beta>\<^sup>* t' \<and> t' \<in> NF"
  (is "PROP ?P U" is "\<And>t e T u i. _ \<Longrightarrow> PROP ?Q t e T u i U")
proof (induct U)
  fix T t
  let ?R = "\<lambda>t. \<forall>e T' u i.
    e\<langle>i:T\<rangle> \<turnstile> t : T' \<longrightarrow> u \<in> NF \<longrightarrow> e \<turnstile> u : T \<longrightarrow> (\<exists>t'. t[u/i] \<rightarrow>\<^sub>\<beta>\<^sup>* t' \<and> t' \<in> NF)"
  assume MI1: "\<And>T1 T2. T = T1 \<Rightarrow> T2 \<Longrightarrow> PROP ?P T1"
  assume MI2: "\<And>T1 T2. T = T1 \<Rightarrow> T2 \<Longrightarrow> PROP ?P T2"
  assume "t \<in> NF"
  thus "\<And>e T' u i. PROP ?Q t e T' u i T"
  proof induct
    fix e T' u i assume uNF: "u \<in> NF" and uT: "e \<turnstile> u : T"
    {
      case (App ts x e_ T'_ u_ i_)
      assume appT: "e\<langle>i:T\<rangle> \<turnstile> Var x \<degree>\<degree> ts : T'"
      from nat_eq_dec show "\<exists>t'. (Var x \<degree>\<degree> ts)[u/i] \<rightarrow>\<^sub>\<beta>\<^sup>* t' \<and> t' \<in> NF"
      proof
	assume eq: "x = i"
	show ?thesis
	proof (cases ts)
	  case Nil
	  with eq have "(Var x \<degree>\<degree> [])[u/i] \<rightarrow>\<^sub>\<beta>\<^sup>* u" by simp
	  with Nil and uNF show ?thesis by simp rules
	next
	  case (Cons a as)
          with appT have "e\<langle>i:T\<rangle> \<turnstile> Var x \<degree>\<degree> (a # as) : T'" by simp
	  then obtain Us
	    where varT': "e\<langle>i:T\<rangle> \<turnstile> Var x : Us \<Rrightarrow> T'"
	    and argsT': "e\<langle>i:T\<rangle> \<tturnstile> a # as : Us"
	    by (rule var_app_typesE)
	  from argsT' obtain T'' Ts where Us: "Us = T'' # Ts"
	    by (cases Us) (rule FalseE, simp+)
	  from varT' and Us have varT: "e\<langle>i:T\<rangle> \<turnstile> Var x : T'' \<Rightarrow> Ts \<Rrightarrow> T'"
	    by simp
          from varT eq have T: "T = T'' \<Rightarrow> Ts \<Rrightarrow> T'" by cases auto
          with uT have uT': "e \<turnstile> u : T'' \<Rightarrow> Ts \<Rrightarrow> T'" by simp
	  from argsT' and Us have argsT: "e\<langle>i:T\<rangle> \<tturnstile> as : Ts" by simp
	  from argsT' and Us have argT: "e\<langle>i:T\<rangle> \<turnstile> a : T''" by simp
	  from argT uT refl have aT: "e \<turnstile> a[u/i] : T''" by (rule subst_lemma)
	  have as: "\<And>Us. e\<langle>i:T\<rangle> \<tturnstile> as : Us \<Longrightarrow> listall ?R as \<Longrightarrow>
	    \<exists>as'. Var 0 \<degree>\<degree> map (\<lambda>t. lift (t[u/i]) 0) as \<rightarrow>\<^sub>\<beta>\<^sup>*
	        Var 0 \<degree>\<degree> map (\<lambda>t. lift t 0) as' \<and>
	      Var 0 \<degree>\<degree> map (\<lambda>t. lift t 0) as' \<in> NF"
	    (is "\<And>Us. _ \<Longrightarrow> _ \<Longrightarrow> \<exists>as'. ?ex Us as as'")
	  proof (induct as rule: rev_induct)
	    case (Nil Us)
	    with Var_NF have "?ex Us [] []" by simp
	    thus ?case ..
	  next
	    case (snoc b bs Us)
	    have "e\<langle>i:T\<rangle> \<tturnstile> bs  @ [b] : Us" .
	    then obtain Vs W where Us: "Us = Vs @ [W]"
	      and bs: "e\<langle>i:T\<rangle> \<tturnstile> bs : Vs" and bT: "e\<langle>i:T\<rangle> \<turnstile> b : W" by (rule types_snocE)
	    from snoc have "listall ?R bs" by simp
	    with bs have "\<exists>bs'. ?ex Vs bs bs'" by (rule snoc)
	    then obtain bs' where
	      bsred: "Var 0 \<degree>\<degree> map (\<lambda>t. lift (t[u/i]) 0) bs \<rightarrow>\<^sub>\<beta>\<^sup>*
	        Var 0 \<degree>\<degree> map (\<lambda>t. lift t 0) bs'"
	      and bsNF: "Var 0 \<degree>\<degree> map (\<lambda>t. lift t 0) bs' \<in> NF" by rules
	    from snoc have "?R b" by simp
	    with bT and uNF and uT have "\<exists>b'. b[u/i] \<rightarrow>\<^sub>\<beta>\<^sup>* b' \<and> b' \<in> NF" by rules
	    then obtain b' where bred: "b[u/i] \<rightarrow>\<^sub>\<beta>\<^sup>* b'" and bNF: "b' \<in> NF" by rules
	    from bsNF have "listall (\<lambda>t. t \<in> NF) (map (\<lambda>t. lift t 0) bs')"
	      by (rule App_NF_D)
	    moreover have "lift b' 0 \<in> NF" by (rule lift_NF)
	    ultimately have "listall (\<lambda>t. t \<in> NF) (map (\<lambda>t. lift t 0) (bs' @ [b']))"
	      by simp
	    hence "Var 0 \<degree>\<degree> map (\<lambda>t. lift t 0) (bs' @ [b']) \<in> NF" by (rule NF.App)
	    moreover from bred have "lift (b[u/i]) 0 \<rightarrow>\<^sub>\<beta>\<^sup>* lift b' 0"
	      by (rule lift_preserves_beta')
	    with bsred have
	      "(Var 0 \<degree>\<degree> map (\<lambda>t. lift (t[u/i]) 0) bs) \<degree> lift (b[u/i]) 0 \<rightarrow>\<^sub>\<beta>\<^sup>*
              (Var 0 \<degree>\<degree> map (\<lambda>t. lift t 0) bs') \<degree> lift b' 0" by (rule rtrancl_beta_App)
	    ultimately have "?ex Us (bs @ [b]) (bs' @ [b'])" by simp
	    thus ?case ..
	  qed
	  from App and Cons have "listall ?R as" by simp (rules dest: listall_conj2)
	  with argsT have "\<exists>as'. ?ex Ts as as'" by (rule as)
	  then obtain as' where
	    asred: "Var 0 \<degree>\<degree> map (\<lambda>t. lift (t[u/i]) 0) as \<rightarrow>\<^sub>\<beta>\<^sup>*
	      Var 0 \<degree>\<degree> map (\<lambda>t. lift t 0) as'"
	    and asNF: "Var 0 \<degree>\<degree> map (\<lambda>t. lift t 0) as' \<in> NF" by rules
	  from App and Cons have "?R a" by simp
	  with argT and uNF and uT have "\<exists>a'. a[u/i] \<rightarrow>\<^sub>\<beta>\<^sup>* a' \<and> a' \<in> NF"
	    by rules
	  then obtain a' where ared: "a[u/i] \<rightarrow>\<^sub>\<beta>\<^sup>* a'" and aNF: "a' \<in> NF" by rules
	  from uNF have "lift u 0 \<in> NF" by (rule lift_NF)
	  hence "\<exists>u'. lift u 0 \<degree> Var 0 \<rightarrow>\<^sub>\<beta>\<^sup>* u' \<and> u' \<in> NF" by (rule app_Var_NF)
	  then obtain u' where ured: "lift u 0 \<degree> Var 0 \<rightarrow>\<^sub>\<beta>\<^sup>* u'" and u'NF: "u' \<in> NF"
	    by rules
	  from T and u'NF have "\<exists>ua. u'[a'/0] \<rightarrow>\<^sub>\<beta>\<^sup>* ua \<and> ua \<in> NF"
	  proof (rule MI1)
	    have "e\<langle>0:T''\<rangle> \<turnstile> lift u 0 \<degree> Var 0 : Ts \<Rrightarrow> T'"
	    proof (rule typing.App)
	      from uT' show "e\<langle>0:T''\<rangle> \<turnstile> lift u 0 : T'' \<Rightarrow> Ts \<Rrightarrow> T'" by (rule lift_type)
	      show "e\<langle>0:T''\<rangle> \<turnstile> Var 0 : T''" by (rule typing.Var) simp
	    qed
	    with ured show "e\<langle>0:T''\<rangle> \<turnstile> u' : Ts \<Rrightarrow> T'" by (rule subject_reduction')
	    from ared aT show "e \<turnstile> a' : T''" by (rule subject_reduction')
	  qed
	  then obtain ua where uared: "u'[a'/0] \<rightarrow>\<^sub>\<beta>\<^sup>* ua" and uaNF: "ua \<in> NF"
	    by rules
	  from ared have "(lift u 0 \<degree> Var 0)[a[u/i]/0] \<rightarrow>\<^sub>\<beta>\<^sup>* (lift u 0 \<degree> Var 0)[a'/0]"
	    by (rule subst_preserves_beta2')
	  also from ured have "(lift u 0 \<degree> Var 0)[a'/0] \<rightarrow>\<^sub>\<beta>\<^sup>* u'[a'/0]"
	    by (rule subst_preserves_beta')
	  also note uared
	  finally have "(lift u 0 \<degree> Var 0)[a[u/i]/0] \<rightarrow>\<^sub>\<beta>\<^sup>* ua" .
	  hence uared': "u \<degree> a[u/i] \<rightarrow>\<^sub>\<beta>\<^sup>* ua" by simp
	  from T have "\<exists>r. (Var 0 \<degree>\<degree> map (\<lambda>t. lift t 0) as')[ua/0] \<rightarrow>\<^sub>\<beta>\<^sup>* r \<and> r \<in> NF"
	  proof (rule MI2)
	    have "e\<langle>0:Ts \<Rrightarrow> T'\<rangle> \<turnstile> Var 0 \<degree>\<degree> map (\<lambda>t. lift (t[u/i]) 0) as : T'"
	    proof (rule list_app_typeI)
	      show "e\<langle>0:Ts \<Rrightarrow> T'\<rangle> \<turnstile> Var 0 : Ts \<Rrightarrow> T'" by (rule typing.Var) simp
	      from uT argsT have "e \<tturnstile> map (\<lambda>t. t[u/i]) as : Ts"
		by (rule substs_lemma)
	      hence "e\<langle>0:Ts \<Rrightarrow> T'\<rangle> \<tturnstile> map (\<lambda>t. lift t 0) (map (\<lambda>t. t[u/i]) as) : Ts"
		by (rule lift_types)
	      thus "e\<langle>0:Ts \<Rrightarrow> T'\<rangle> \<tturnstile> map (\<lambda>t. lift (t[u/i]) 0) as : Ts"
		by (simp_all add: map_compose [symmetric] o_def)
	    qed
	    with asred show "e\<langle>0:Ts \<Rrightarrow> T'\<rangle> \<turnstile> Var 0 \<degree>\<degree> map (\<lambda>t. lift t 0) as' : T'"
	      by (rule subject_reduction')
	    from argT uT refl have "e \<turnstile> a[u/i] : T''" by (rule subst_lemma)
	    with uT' have "e \<turnstile> u \<degree> a[u/i] : Ts \<Rrightarrow> T'" by (rule typing.App)
	    with uared' show "e \<turnstile> ua : Ts \<Rrightarrow> T'" by (rule subject_reduction')
	  qed
	  then obtain r where rred: "(Var 0 \<degree>\<degree> map (\<lambda>t. lift t 0) as')[ua/0] \<rightarrow>\<^sub>\<beta>\<^sup>* r"
	    and rnf: "r \<in> NF" by rules
	  from asred have
	    "(Var 0 \<degree>\<degree> map (\<lambda>t. lift (t[u/i]) 0) as)[u \<degree> a[u/i]/0] \<rightarrow>\<^sub>\<beta>\<^sup>*
	    (Var 0 \<degree>\<degree> map (\<lambda>t. lift t 0) as')[u \<degree> a[u/i]/0]"
	    by (rule subst_preserves_beta')
	  also from uared' have "(Var 0 \<degree>\<degree> map (\<lambda>t. lift t 0) as')[u \<degree> a[u/i]/0] \<rightarrow>\<^sub>\<beta>\<^sup>*
	    (Var 0 \<degree>\<degree> map (\<lambda>t. lift t 0) as')[ua/0]" by (rule subst_preserves_beta2')
	  also note rred
	  finally have "(Var 0 \<degree>\<degree> map (\<lambda>t. lift (t[u/i]) 0) as)[u \<degree> a[u/i]/0] \<rightarrow>\<^sub>\<beta>\<^sup>* r" .
	  with rnf Cons eq show ?thesis
	    by (simp add: map_compose [symmetric] o_def) rules
	qed
      next
	assume neq: "x \<noteq> i"
	show ?thesis
	proof -
	  from appT obtain Us
	      where varT: "e\<langle>i:T\<rangle> \<turnstile> Var x : Us \<Rrightarrow> T'"
	      and argsT: "e\<langle>i:T\<rangle> \<tturnstile> ts : Us"
	    by (rule var_app_typesE)
	  have ts: "\<And>Us. e\<langle>i:T\<rangle> \<tturnstile> ts : Us \<Longrightarrow> listall ?R ts \<Longrightarrow>
	    \<exists>ts'. \<forall>x'. Var x' \<degree>\<degree> map (\<lambda>t. t[u/i]) ts \<rightarrow>\<^sub>\<beta>\<^sup>* Var x' \<degree>\<degree> ts' \<and>
	      Var x' \<degree>\<degree> ts' \<in> NF"
	    (is "\<And>Us. _ \<Longrightarrow> _ \<Longrightarrow> \<exists>ts'. ?ex Us ts ts'")
	  proof (induct ts rule: rev_induct)
	    case (Nil Us)
	    with Var_NF have "?ex Us [] []" by simp
	    thus ?case ..
	  next
	    case (snoc b bs Us)
	    have "e\<langle>i:T\<rangle> \<tturnstile> bs  @ [b] : Us" .
	    then obtain Vs W where Us: "Us = Vs @ [W]"
	      and bs: "e\<langle>i:T\<rangle> \<tturnstile> bs : Vs" and bT: "e\<langle>i:T\<rangle> \<turnstile> b : W" by (rule types_snocE)
	    from snoc have "listall ?R bs" by simp
	    with bs have "\<exists>bs'. ?ex Vs bs bs'" by (rule snoc)
	    then obtain bs' where
	      bsred: "\<And>x'. Var x' \<degree>\<degree> map (\<lambda>t. t[u/i]) bs \<rightarrow>\<^sub>\<beta>\<^sup>* Var x' \<degree>\<degree> bs'"
	      and bsNF: "\<And>x'. Var x' \<degree>\<degree> bs' \<in> NF" by rules
	    from snoc have "?R b" by simp
	    with bT and uNF and uT have "\<exists>b'. b[u/i] \<rightarrow>\<^sub>\<beta>\<^sup>* b' \<and> b' \<in> NF" by rules
	    then obtain b' where bred: "b[u/i] \<rightarrow>\<^sub>\<beta>\<^sup>* b'" and bNF: "b' \<in> NF" by rules
	    from bsred bred have "\<And>x'. (Var x' \<degree>\<degree> map (\<lambda>t. t[u/i]) bs) \<degree> b[u/i] \<rightarrow>\<^sub>\<beta>\<^sup>*
              (Var x' \<degree>\<degree> bs') \<degree> b'" by (rule rtrancl_beta_App)
	    moreover from bsNF [of 0] have "listall (\<lambda>t. t \<in> NF) bs'"
	      by (rule App_NF_D)
	    with bNF have "listall (\<lambda>t. t \<in> NF) (bs' @ [b'])" by simp
	    hence "\<And>x'. Var x' \<degree>\<degree> (bs' @ [b']) \<in> NF" by (rule NF.App)
	    ultimately have "?ex Us (bs @ [b]) (bs' @ [b'])" by simp
	    thus ?case ..
	  qed
	  from App have "listall ?R ts" by (rules dest: listall_conj2)
	  with argsT have "\<exists>ts'. ?ex Ts ts ts'" by (rule ts)
	  then obtain ts' where NF: "?ex Ts ts ts'" ..
	  from nat_le_dec show ?thesis
	  proof
	    assume "i < x"
	    with NF show ?thesis by simp rules
	  next
	    assume "\<not> (i < x)"
	    with NF neq show ?thesis by (simp add: subst_Var) rules
	  qed
	qed
      qed
    next
      case (Abs r e_ T'_ u_ i_)
      assume absT: "e\<langle>i:T\<rangle> \<turnstile> Abs r : T'"
      then obtain R S where "e\<langle>0:R\<rangle>\<langle>Suc i:T\<rangle>  \<turnstile> r : S" by (rule abs_typeE) simp
      moreover have "lift u 0 \<in> NF" by (rule lift_NF)
      moreover have "e\<langle>0:R\<rangle> \<turnstile> lift u 0 : T" by (rule lift_type)
      ultimately have "\<exists>t'. r[lift u 0/Suc i] \<rightarrow>\<^sub>\<beta>\<^sup>* t' \<and> t' \<in> NF" by (rule Abs)
      thus "\<exists>t'. Abs r[u/i] \<rightarrow>\<^sub>\<beta>\<^sup>* t' \<and> t' \<in> NF"
	by simp (rules intro: rtrancl_beta_Abs NF.Abs)
    }
  qed
qed


consts -- {* A computationally relevant copy of @{term "e \<turnstile> t : T"} *}
  rtyping :: "((nat \<Rightarrow> type) \<times> dB \<times> type) set"

syntax
  "_rtyping" :: "(nat \<Rightarrow> type) \<Rightarrow> dB \<Rightarrow> type \<Rightarrow> bool"    ("_ |-\<^sub>R _ : _" [50, 50, 50] 50)
syntax (xsymbols)
  "_rtyping" :: "(nat \<Rightarrow> type) \<Rightarrow> dB \<Rightarrow> type \<Rightarrow> bool"    ("_ \<turnstile>\<^sub>R _ : _" [50, 50, 50] 50)
translations
  "e \<turnstile>\<^sub>R t : T" \<rightleftharpoons> "(e, t, T) \<in> rtyping"

inductive rtyping
  intros
    Var: "e x = T \<Longrightarrow> e \<turnstile>\<^sub>R Var x : T"
    Abs: "e\<langle>0:T\<rangle> \<turnstile>\<^sub>R t : U \<Longrightarrow> e \<turnstile>\<^sub>R Abs t : (T \<Rightarrow> U)"
    App: "e \<turnstile>\<^sub>R s : T \<Rightarrow> U \<Longrightarrow> e \<turnstile>\<^sub>R t : T \<Longrightarrow> e \<turnstile>\<^sub>R (s \<degree> t) : U"

lemma rtyping_imp_typing: "e \<turnstile>\<^sub>R t : T \<Longrightarrow> e \<turnstile> t : T"
  apply (induct set: rtyping)
  apply (erule typing.Var)
  apply (erule typing.Abs)
  apply (erule typing.App)
  apply assumption
  done


theorem type_NF: assumes T: "e \<turnstile>\<^sub>R t : T"
  shows "\<exists>t'. t \<rightarrow>\<^sub>\<beta>\<^sup>* t' \<and> t' \<in> NF" using T
proof induct
  case Var
  show ?case by (rules intro: Var_NF)
next
  case Abs
  thus ?case by (rules intro: rtrancl_beta_Abs NF.Abs)
next
  case (App T U e s t)
  from App obtain s' t' where
    sred: "s \<rightarrow>\<^sub>\<beta>\<^sup>* s'" and sNF: "s' \<in> NF"
    and tred: "t \<rightarrow>\<^sub>\<beta>\<^sup>* t'" and tNF: "t' \<in> NF" by rules
  have "\<exists>u. (Var 0 \<degree> lift t' 0)[s'/0] \<rightarrow>\<^sub>\<beta>\<^sup>* u \<and> u \<in> NF"
  proof (rule subst_type_NF)
    have "lift t' 0 \<in> NF" by (rule lift_NF)
    hence "listall (\<lambda>t. t \<in> NF) [lift t' 0]" by (rule listall_cons) (rule listall_nil)
    hence "Var 0 \<degree>\<degree> [lift t' 0] \<in> NF" by (rule NF.App)
    thus "Var 0 \<degree> lift t' 0 \<in> NF" by simp
    show "e\<langle>0:T \<Rightarrow> U\<rangle> \<turnstile> Var 0 \<degree> lift t' 0 : U"
    proof (rule typing.App)
      show "e\<langle>0:T \<Rightarrow> U\<rangle> \<turnstile> Var 0 : T \<Rightarrow> U"
      	by (rule typing.Var) simp
      from tred have "e \<turnstile> t' : T"
      	by (rule subject_reduction') (rule rtyping_imp_typing)
      thus "e\<langle>0:T \<Rightarrow> U\<rangle> \<turnstile> lift t' 0 : T"
      	by (rule lift_type)
    qed
    from sred show "e \<turnstile> s' : T \<Rightarrow> U"
      by (rule subject_reduction') (rule rtyping_imp_typing)
  qed
  then obtain u where ured: "s' \<degree> t' \<rightarrow>\<^sub>\<beta>\<^sup>* u" and unf: "u \<in> NF" by simp rules
  from sred tred have "s \<degree> t \<rightarrow>\<^sub>\<beta>\<^sup>* s' \<degree> t'" by (rule rtrancl_beta_App)
  hence "s \<degree> t \<rightarrow>\<^sub>\<beta>\<^sup>* u" using ured by (rule rtrancl_trans)
  with unf show ?case by rules
qed


subsection {* Extracting the program *}

declare NF.induct [ind_realizer]
declare rtrancl.induct [ind_realizer irrelevant]
declare rtyping.induct [ind_realizer]
lemmas [extraction_expand] = trans_def conj_assoc listall_cons_eq

extract type_NF

lemma rtranclR_rtrancl_eq: "((a, b) \<in> rtranclR r) = ((a, b) \<in> rtrancl (Collect r))"
  apply (rule iffI)
  apply (erule rtranclR.induct)
  apply (rule rtrancl_refl)
  apply (erule rtrancl_into_rtrancl)
  apply (erule CollectI)
  apply (erule rtrancl.induct)
  apply (rule rtranclR.rtrancl_refl)
  apply (erule rtranclR.rtrancl_into_rtrancl)
  apply (erule CollectD)
  done

lemma NFR_imp_NF: "(nf, t) \<in> NFR \<Longrightarrow> t \<in> NF"
  apply (erule NFR.induct)
  apply (rule NF.intros)
  apply (simp add: listall_def)
  apply (erule NF.intros)
  done

text_raw {*
\begin{figure}
\renewcommand{\isastyle}{\scriptsize\it}%
@{thm [display,eta_contract=false,margin=100] subst_type_NF_def}
\renewcommand{\isastyle}{\small\it}%
\caption{Program extracted from @{text subst_type_NF}}
\label{fig:extr-subst-type-nf}
\end{figure}

\begin{figure}
\renewcommand{\isastyle}{\scriptsize\it}%
@{thm [display,margin=100] subst_Var_NF_def}
@{thm [display,margin=100] app_Var_NF_def}
@{thm [display,margin=100] lift_NF_def}
@{thm [display,eta_contract=false,margin=100] type_NF_def}
\renewcommand{\isastyle}{\small\it}%
\caption{Program extracted from lemmas and main theorem}
\label{fig:extr-type-nf}
\end{figure}
*}

text {*
The program corresponding to the proof of the central lemma, which
performs substitution and normalization, is shown in Figure
\ref{fig:extr-subst-type-nf}. The correctness
theorem corresponding to the program @{text "subst_type_NF"} is
@{thm [display,margin=100] subst_type_NF_correctness
  [simplified rtranclR_rtrancl_eq Collect_mem_eq, no_vars]}
where @{text NFR} is the realizability predicate corresponding to
the datatype @{text NFT}, which is inductively defined by the rules
\pagebreak
@{thm [display,margin=90] NFR.App [of ts nfs x] NFR.Abs [of nf t]}

The programs corresponding to the main theorem @{text "type_NF"}, as
well as to some lemmas, are shown in Figure \ref{fig:extr-type-nf}.
The correctness statement for the main function @{text "type_NF"} is
@{thm [display,margin=100] type_NF_correctness
  [simplified rtranclR_rtrancl_eq Collect_mem_eq, no_vars]}
where the realizability predicate @{text "rtypingR"} corresponding to the
computationally relevant version of the typing judgement is inductively
defined by the rules
@{thm [display,margin=100] rtypingR.Var [no_vars]
  rtypingR.Abs [of ty, no_vars] rtypingR.App [of ty e s T U ty' t]}
*}

subsection {* Generating executable code *}

consts_code
  arbitrary :: "'a"       ("(error \"arbitrary\")")
  arbitrary :: "'a \<Rightarrow> 'b" ("(fn '_ => error \"arbitrary\")")

generate_code
  test = "type_NF"

text {*
The following functions convert between Isabelle's built-in {\tt term}
datatype and the generated {\tt dB} datatype. This allows to
generate example terms using Isabelle's parser and inspect
normalized terms using Isabelle's pretty printer.
*}

ML {*
fun nat_of_int 0 = id0
  | nat_of_int n = Suc (nat_of_int (n-1));

fun int_of_nat id0 = 0
  | int_of_nat (Suc n) = 1 + int_of_nat n;

fun dBtype_of_typ (Type ("fun", [T, U])) =
      Fun (dBtype_of_typ T, dBtype_of_typ U)
  | dBtype_of_typ (TFree (s, _)) = (case explode s of
        ["'", a] => Atom (nat_of_int (ord a - 97))
      | _ => error "dBtype_of_typ: variable name")
  | dBtype_of_typ _ = error "dBtype_of_typ: bad type";

fun dB_of_term (Bound i) = dB_Var (nat_of_int i)
  | dB_of_term (t $ u) = dB_App (dB_of_term t, dB_of_term u)
  | dB_of_term (Abs (_, _, t)) = dB_Abs (dB_of_term t)
  | dB_of_term _ = error "dB_of_term: bad term";

fun term_of_dB Ts (Type ("fun", [T, U])) (dB_Abs dBt) =
      Abs ("x", T, term_of_dB (T :: Ts) U dBt)
  | term_of_dB Ts _ dBt = term_of_dB' Ts dBt
and term_of_dB' Ts (dB_Var n) = Bound (int_of_nat n)
  | term_of_dB' Ts (dB_App (dBt, dBu)) =
      let val t = term_of_dB' Ts dBt
      in case fastype_of1 (Ts, t) of
          Type ("fun", [T, U]) => t $ term_of_dB Ts T dBu
        | _ => error "term_of_dB: function type expected"
      end
  | term_of_dB' _ _ = error "term_of_dB: term not in normal form";

fun typing_of_term Ts e (Bound i) =
      rtypingT_Var (e, nat_of_int i, dBtype_of_typ (nth_elem (i, Ts)))
  | typing_of_term Ts e (t $ u) = (case fastype_of1 (Ts, t) of
        Type ("fun", [T, U]) => rtypingT_App (e, dB_of_term t,
          dBtype_of_typ T, dBtype_of_typ U, dB_of_term u,
          typing_of_term Ts e t, typing_of_term Ts e u)
      | _ => error "typing_of_term: function type expected")
  | typing_of_term Ts e (Abs (s, T, t)) =
      let val dBT = dBtype_of_typ T
      in rtypingT_Abs (e, dBT, dB_of_term t,
        dBtype_of_typ (fastype_of1 (T :: Ts, t)),
        typing_of_term (T :: Ts) (shift e id0 dBT) t)
      end
  | typing_of_term _ _ _ = error "typing_of_term: bad term";

fun dummyf _ = error "dummy";
*}

text {*
We now try out the extracted program @{text "type_NF"} on some example terms.
*}

ML {*
val sg = sign_of (the_context());
fun rd s = read_cterm sg (s, TypeInfer.logicT);

val ct1 = rd "%f. ((%f x. f (f (f x))) ((%f x. f (f (f (f x)))) f))";
val (dB1, _) = type_NF (typing_of_term [] dummyf (term_of ct1));
val ct1' = cterm_of sg (term_of_dB [] (#T (rep_cterm ct1)) dB1);

val ct2 = rd
  "%f x. (%x. f x x) ((%x. f x x) ((%x. f x x) ((%x. f x x) ((%x. f x x) ((%x. f x x) x)))))";
val (dB2, _) = type_NF (typing_of_term [] dummyf (term_of ct2));
val ct2' = cterm_of sg (term_of_dB [] (#T (rep_cterm ct2)) dB2);
*}

end
