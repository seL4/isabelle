(*  Title:      HOL/HOLCF/Domain.thy
    Author:     Brian Huffman
*)

section \<open>Domain package\<close>

theory Domain
imports Representable Map_Functions Fixrec
keywords
  "lazy" "unsafe" and
  "domaindef" "domain" :: thy_defn and
  "domain_isomorphism" :: thy_decl
begin

subsection \<open>Continuous isomorphisms\<close>

text \<open>A locale for continuous isomorphisms\<close>

locale iso =
  fixes abs :: "'a \<rightarrow> 'b"
  fixes rep :: "'b \<rightarrow> 'a"
  assumes abs_iso [simp]: "rep\<cdot>(abs\<cdot>x) = x"
  assumes rep_iso [simp]: "abs\<cdot>(rep\<cdot>y) = y"
begin

lemma swap: "iso rep abs"
  by (rule iso.intro [OF rep_iso abs_iso])

lemma abs_below: "(abs\<cdot>x \<sqsubseteq> abs\<cdot>y) = (x \<sqsubseteq> y)"
proof
  assume "abs\<cdot>x \<sqsubseteq> abs\<cdot>y"
  then have "rep\<cdot>(abs\<cdot>x) \<sqsubseteq> rep\<cdot>(abs\<cdot>y)" by (rule monofun_cfun_arg)
  then show "x \<sqsubseteq> y" by simp
next
  assume "x \<sqsubseteq> y"
  then show "abs\<cdot>x \<sqsubseteq> abs\<cdot>y" by (rule monofun_cfun_arg)
qed

lemma rep_below: "(rep\<cdot>x \<sqsubseteq> rep\<cdot>y) = (x \<sqsubseteq> y)"
  by (rule iso.abs_below [OF swap])

lemma abs_eq: "(abs\<cdot>x = abs\<cdot>y) = (x = y)"
  by (simp add: po_eq_conv abs_below)

lemma rep_eq: "(rep\<cdot>x = rep\<cdot>y) = (x = y)"
  by (rule iso.abs_eq [OF swap])

lemma abs_strict: "abs\<cdot>\<bottom> = \<bottom>"
proof -
  have "\<bottom> \<sqsubseteq> rep\<cdot>\<bottom>" ..
  then have "abs\<cdot>\<bottom> \<sqsubseteq> abs\<cdot>(rep\<cdot>\<bottom>)" by (rule monofun_cfun_arg)
  then have "abs\<cdot>\<bottom> \<sqsubseteq> \<bottom>" by simp
  then show ?thesis by (rule bottomI)
qed

lemma rep_strict: "rep\<cdot>\<bottom> = \<bottom>"
  by (rule iso.abs_strict [OF swap])

lemma abs_defin': "abs\<cdot>x = \<bottom> \<Longrightarrow> x = \<bottom>"
proof -
  have "x = rep\<cdot>(abs\<cdot>x)" by simp
  also assume "abs\<cdot>x = \<bottom>"
  also note rep_strict
  finally show "x = \<bottom>" .
qed

lemma rep_defin': "rep\<cdot>z = \<bottom> \<Longrightarrow> z = \<bottom>"
  by (rule iso.abs_defin' [OF swap])

lemma abs_defined: "z \<noteq> \<bottom> \<Longrightarrow> abs\<cdot>z \<noteq> \<bottom>"
  by (erule contrapos_nn, erule abs_defin')

lemma rep_defined: "z \<noteq> \<bottom> \<Longrightarrow> rep\<cdot>z \<noteq> \<bottom>"
  by (rule iso.abs_defined [OF iso.swap]) (rule iso_axioms)

lemma abs_bottom_iff: "(abs\<cdot>x = \<bottom>) = (x = \<bottom>)"
  by (auto elim: abs_defin' intro: abs_strict)

lemma rep_bottom_iff: "(rep\<cdot>x = \<bottom>) = (x = \<bottom>)"
  by (rule iso.abs_bottom_iff [OF iso.swap]) (rule iso_axioms)

lemma casedist_rule: "rep\<cdot>x = \<bottom> \<or> P \<Longrightarrow> x = \<bottom> \<or> P"
  by (simp add: rep_bottom_iff)

lemma compact_abs_rev: "compact (abs\<cdot>x) \<Longrightarrow> compact x"
proof (unfold compact_def)
  assume "adm (\<lambda>y. abs\<cdot>x \<notsqsubseteq> y)"
  with cont_Rep_cfun2
  have "adm (\<lambda>y. abs\<cdot>x \<notsqsubseteq> abs\<cdot>y)" by (rule adm_subst)
  then show "adm (\<lambda>y. x \<notsqsubseteq> y)" using abs_below by simp
qed

lemma compact_rep_rev: "compact (rep\<cdot>x) \<Longrightarrow> compact x"
  by (rule iso.compact_abs_rev [OF iso.swap]) (rule iso_axioms)

lemma compact_abs: "compact x \<Longrightarrow> compact (abs\<cdot>x)"
  by (rule compact_rep_rev) simp

lemma compact_rep: "compact x \<Longrightarrow> compact (rep\<cdot>x)"
  by (rule iso.compact_abs [OF iso.swap]) (rule iso_axioms)

lemma iso_swap: "(x = abs\<cdot>y) = (rep\<cdot>x = y)"
proof
  assume "x = abs\<cdot>y"
  then have "rep\<cdot>x = rep\<cdot>(abs\<cdot>y)" by simp
  then show "rep\<cdot>x = y" by simp
next
  assume "rep\<cdot>x = y"
  then have "abs\<cdot>(rep\<cdot>x) = abs\<cdot>y" by simp
  then show "x = abs\<cdot>y" by simp
qed

end

subsection \<open>Proofs about take functions\<close>

text \<open>
  This section contains lemmas that are used in a module that supports
  the domain isomorphism package; the module contains proofs related
  to take functions and the finiteness predicate.
\<close>

lemma deflation_abs_rep:
  fixes abs and rep and d
  assumes abs_iso: "\<And>x. rep\<cdot>(abs\<cdot>x) = x"
  assumes rep_iso: "\<And>y. abs\<cdot>(rep\<cdot>y) = y"
  shows "deflation d \<Longrightarrow> deflation (abs oo d oo rep)"
by (rule ep_pair.deflation_e_d_p) (simp add: ep_pair.intro assms)

lemma deflation_chain_min:
  assumes chain: "chain d"
  assumes defl: "\<And>n. deflation (d n)"
  shows "d m\<cdot>(d n\<cdot>x) = d (min m n)\<cdot>x"
proof (rule linorder_le_cases)
  assume "m \<le> n"
  with chain have "d m \<sqsubseteq> d n" by (rule chain_mono)
  then have "d m\<cdot>(d n\<cdot>x) = d m\<cdot>x"
    by (rule deflation_below_comp1 [OF defl defl])
  moreover from \<open>m \<le> n\<close> have "min m n = m" by simp
  ultimately show ?thesis by simp
next
  assume "n \<le> m"
  with chain have "d n \<sqsubseteq> d m" by (rule chain_mono)
  then have "d m\<cdot>(d n\<cdot>x) = d n\<cdot>x"
    by (rule deflation_below_comp2 [OF defl defl])
  moreover from \<open>n \<le> m\<close> have "min m n = n" by simp
  ultimately show ?thesis by simp
qed

lemma lub_ID_take_lemma:
  assumes "chain t" and "(\<Squnion>n. t n) = ID"
  assumes "\<And>n. t n\<cdot>x = t n\<cdot>y" shows "x = y"
proof -
  have "(\<Squnion>n. t n\<cdot>x) = (\<Squnion>n. t n\<cdot>y)"
    using assms(3) by simp
  then have "(\<Squnion>n. t n)\<cdot>x = (\<Squnion>n. t n)\<cdot>y"
    using assms(1) by (simp add: lub_distribs)
  then show "x = y"
    using assms(2) by simp
qed

lemma lub_ID_reach:
  assumes "chain t" and "(\<Squnion>n. t n) = ID"
  shows "(\<Squnion>n. t n\<cdot>x) = x"
using assms by (simp add: lub_distribs)

lemma lub_ID_take_induct:
  assumes "chain t" and "(\<Squnion>n. t n) = ID"
  assumes "adm P" and "\<And>n. P (t n\<cdot>x)" shows "P x"
proof -
  from \<open>chain t\<close> have "chain (\<lambda>n. t n\<cdot>x)" by simp
  from \<open>adm P\<close> this \<open>\<And>n. P (t n\<cdot>x)\<close> have "P (\<Squnion>n. t n\<cdot>x)" by (rule admD)
  with \<open>chain t\<close> \<open>(\<Squnion>n. t n) = ID\<close> show "P x" by (simp add: lub_distribs)
qed

subsection \<open>Finiteness\<close>

text \<open>
  Let a ``decisive'' function be a deflation that maps every input to
  either itself or bottom.  Then if a domain's take functions are all
  decisive, then all values in the domain are finite.
\<close>

definition
  decisive :: "('a::pcpo \<rightarrow> 'a) \<Rightarrow> bool"
where
  "decisive d \<longleftrightarrow> (\<forall>x. d\<cdot>x = x \<or> d\<cdot>x = \<bottom>)"

lemma decisiveI: "(\<And>x. d\<cdot>x = x \<or> d\<cdot>x = \<bottom>) \<Longrightarrow> decisive d"
  unfolding decisive_def by simp

lemma decisive_cases:
  assumes "decisive d" obtains "d\<cdot>x = x" | "d\<cdot>x = \<bottom>"
using assms unfolding decisive_def by auto

lemma decisive_bottom: "decisive \<bottom>"
  unfolding decisive_def by simp

lemma decisive_ID: "decisive ID"
  unfolding decisive_def by simp

lemma decisive_ssum_map:
  assumes f: "decisive f"
  assumes g: "decisive g"
  shows "decisive (ssum_map\<cdot>f\<cdot>g)"
  apply (rule decisiveI)
  subgoal for s
    apply (cases s, simp_all)
     apply (rule_tac x=x in decisive_cases [OF f], simp_all)
    apply (rule_tac x=y in decisive_cases [OF g], simp_all)
    done
  done

lemma decisive_sprod_map:
  assumes f: "decisive f"
  assumes g: "decisive g"
  shows "decisive (sprod_map\<cdot>f\<cdot>g)"
  apply (rule decisiveI)
  subgoal for s
    apply (cases s, simp)
    subgoal for x y
      apply (rule decisive_cases [OF f, where x = x], simp_all)
      apply (rule decisive_cases [OF g, where x = y], simp_all)
      done
    done
  done

lemma decisive_abs_rep:
  fixes abs rep
  assumes iso: "iso abs rep"
  assumes d: "decisive d"
  shows "decisive (abs oo d oo rep)"
  apply (rule decisiveI)
  subgoal for s
    apply (rule decisive_cases [OF d, where x="rep\<cdot>s"])
     apply (simp add: iso.rep_iso [OF iso])
    apply (simp add: iso.abs_strict [OF iso])
    done
  done

lemma lub_ID_finite:
  assumes chain: "chain d"
  assumes lub: "(\<Squnion>n. d n) = ID"
  assumes decisive: "\<And>n. decisive (d n)"
  shows "\<exists>n. d n\<cdot>x = x"
proof -
  have 1: "chain (\<lambda>n. d n\<cdot>x)" using chain by simp
  have 2: "(\<Squnion>n. d n\<cdot>x) = x" using chain lub by (rule lub_ID_reach)
  have "\<forall>n. d n\<cdot>x = x \<or> d n\<cdot>x = \<bottom>"
    using decisive unfolding decisive_def by simp
  hence "range (\<lambda>n. d n\<cdot>x) \<subseteq> {x, \<bottom>}"
    by auto
  hence "finite (range (\<lambda>n. d n\<cdot>x))"
    by (rule finite_subset, simp)
  with 1 have "finite_chain (\<lambda>n. d n\<cdot>x)"
    by (rule finite_range_imp_finch)
  then have "\<exists>n. (\<Squnion>n. d n\<cdot>x) = d n\<cdot>x"
    unfolding finite_chain_def by (auto simp add: maxinch_is_thelub)
  with 2 show "\<exists>n. d n\<cdot>x = x" by (auto elim: sym)
qed

lemma lub_ID_finite_take_induct:
  assumes "chain d" and "(\<Squnion>n. d n) = ID" and "\<And>n. decisive (d n)"
  shows "(\<And>n. P (d n\<cdot>x)) \<Longrightarrow> P x"
using lub_ID_finite [OF assms] by metis

subsection \<open>Proofs about constructor functions\<close>

text \<open>Lemmas for proving nchotomy rule:\<close>

lemma ex_one_bottom_iff:
  "(\<exists>x. P x \<and> x \<noteq> \<bottom>) = P ONE"
by simp

lemma ex_up_bottom_iff:
  "(\<exists>x. P x \<and> x \<noteq> \<bottom>) = (\<exists>x. P (up\<cdot>x))"
by (safe, case_tac x, auto)

lemma ex_sprod_bottom_iff:
 "(\<exists>y. P y \<and> y \<noteq> \<bottom>) =
  (\<exists>x y. (P (:x, y:) \<and> x \<noteq> \<bottom>) \<and> y \<noteq> \<bottom>)"
by (safe, case_tac y, auto)

lemma ex_sprod_up_bottom_iff:
 "(\<exists>y. P y \<and> y \<noteq> \<bottom>) =
  (\<exists>x y. P (:up\<cdot>x, y:) \<and> y \<noteq> \<bottom>)"
by (safe, case_tac y, simp, case_tac x, auto)

lemma ex_ssum_bottom_iff:
 "(\<exists>x. P x \<and> x \<noteq> \<bottom>) =
 ((\<exists>x. P (sinl\<cdot>x) \<and> x \<noteq> \<bottom>) \<or>
  (\<exists>x. P (sinr\<cdot>x) \<and> x \<noteq> \<bottom>))"
by (safe, case_tac x, auto)

lemma exh_start: "p = \<bottom> \<or> (\<exists>x. p = x \<and> x \<noteq> \<bottom>)"
  by auto

lemmas ex_bottom_iffs =
   ex_ssum_bottom_iff
   ex_sprod_up_bottom_iff
   ex_sprod_bottom_iff
   ex_up_bottom_iff
   ex_one_bottom_iff

text \<open>Rules for turning nchotomy into exhaust:\<close>

lemma exh_casedist0: "\<lbrakk>R; R \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P" (* like make_elim *)
  by auto

lemma exh_casedist1: "((P \<or> Q \<Longrightarrow> R) \<Longrightarrow> S) \<equiv> (\<lbrakk>P \<Longrightarrow> R; Q \<Longrightarrow> R\<rbrakk> \<Longrightarrow> S)"
  by rule auto

lemma exh_casedist2: "(\<exists>x. P x \<Longrightarrow> Q) \<equiv> (\<And>x. P x \<Longrightarrow> Q)"
  by rule auto

lemma exh_casedist3: "(P \<and> Q \<Longrightarrow> R) \<equiv> (P \<Longrightarrow> Q \<Longrightarrow> R)"
  by rule auto

lemmas exh_casedists = exh_casedist1 exh_casedist2 exh_casedist3

text \<open>Rules for proving constructor properties\<close>

lemmas con_strict_rules =
  sinl_strict sinr_strict spair_strict1 spair_strict2

lemmas con_bottom_iff_rules =
  sinl_bottom_iff sinr_bottom_iff spair_bottom_iff up_defined ONE_defined

lemmas con_below_iff_rules =
  sinl_below sinr_below sinl_below_sinr sinr_below_sinl con_bottom_iff_rules

lemmas con_eq_iff_rules =
  sinl_eq sinr_eq sinl_eq_sinr sinr_eq_sinl con_bottom_iff_rules

lemmas sel_strict_rules =
  cfcomp2 sscase1 sfst_strict ssnd_strict fup1

lemma sel_app_extra_rules:
  "sscase\<cdot>ID\<cdot>\<bottom>\<cdot>(sinr\<cdot>x) = \<bottom>"
  "sscase\<cdot>ID\<cdot>\<bottom>\<cdot>(sinl\<cdot>x) = x"
  "sscase\<cdot>\<bottom>\<cdot>ID\<cdot>(sinl\<cdot>x) = \<bottom>"
  "sscase\<cdot>\<bottom>\<cdot>ID\<cdot>(sinr\<cdot>x) = x"
  "fup\<cdot>ID\<cdot>(up\<cdot>x) = x"
by (cases "x = \<bottom>", simp, simp)+

lemmas sel_app_rules =
  sel_strict_rules sel_app_extra_rules
  ssnd_spair sfst_spair up_defined spair_defined

lemmas sel_bottom_iff_rules =
  cfcomp2 sfst_bottom_iff ssnd_bottom_iff

lemmas take_con_rules =
  ssum_map_sinl' ssum_map_sinr' sprod_map_spair' u_map_up
  deflation_strict deflation_ID ID1 cfcomp2

subsection \<open>ML setup\<close>

named_theorems domain_deflation "theorems like deflation a ==> deflation (foo_map$a)"
  and domain_map_ID "theorems like foo_map$ID = ID"

ML_file \<open>Tools/Domain/domain_take_proofs.ML\<close>
ML_file \<open>Tools/cont_consts.ML\<close>
ML_file \<open>Tools/cont_proc.ML\<close>
simproc_setup cont ("cont f") = \<open>K ContProc.cont_proc\<close>

ML_file \<open>Tools/Domain/domain_constructors.ML\<close>
ML_file \<open>Tools/Domain/domain_induction.ML\<close>


subsection \<open>Representations of types\<close>

default_sort "domain"

lemma emb_prj: "emb\<cdot>((prj\<cdot>x)::'a) = cast\<cdot>DEFL('a)\<cdot>x"
by (simp add: cast_DEFL)

lemma emb_prj_emb:
  fixes x :: "'a"
  assumes "DEFL('a) \<sqsubseteq> DEFL('b)"
  shows "emb\<cdot>(prj\<cdot>(emb\<cdot>x) :: 'b) = emb\<cdot>x"
unfolding emb_prj
apply (rule cast.belowD)
apply (rule monofun_cfun_arg [OF assms])
apply (simp add: cast_DEFL)
done

lemma prj_emb_prj:
  assumes "DEFL('a) \<sqsubseteq> DEFL('b)"
  shows "prj\<cdot>(emb\<cdot>(prj\<cdot>x :: 'b)) = (prj\<cdot>x :: 'a)"
 apply (rule emb_eq_iff [THEN iffD1])
 apply (simp only: emb_prj)
 apply (rule deflation_below_comp1)
   apply (rule deflation_cast)
  apply (rule deflation_cast)
 apply (rule monofun_cfun_arg [OF assms])
done

text \<open>Isomorphism lemmas used internally by the domain package:\<close>

lemma domain_abs_iso:
  fixes abs and rep
  assumes DEFL: "DEFL('b) = DEFL('a)"
  assumes abs_def: "(abs :: 'a \<rightarrow> 'b) \<equiv> prj oo emb"
  assumes rep_def: "(rep :: 'b \<rightarrow> 'a) \<equiv> prj oo emb"
  shows "rep\<cdot>(abs\<cdot>x) = x"
unfolding abs_def rep_def
by (simp add: emb_prj_emb DEFL)

lemma domain_rep_iso:
  fixes abs and rep
  assumes DEFL: "DEFL('b) = DEFL('a)"
  assumes abs_def: "(abs :: 'a \<rightarrow> 'b) \<equiv> prj oo emb"
  assumes rep_def: "(rep :: 'b \<rightarrow> 'a) \<equiv> prj oo emb"
  shows "abs\<cdot>(rep\<cdot>x) = x"
unfolding abs_def rep_def
by (simp add: emb_prj_emb DEFL)

subsection \<open>Deflations as sets\<close>

definition defl_set :: "'a::bifinite defl \<Rightarrow> 'a set"
where "defl_set A = {x. cast\<cdot>A\<cdot>x = x}"

lemma adm_defl_set: "adm (\<lambda>x. x \<in> defl_set A)"
unfolding defl_set_def by simp

lemma defl_set_bottom: "\<bottom> \<in> defl_set A"
unfolding defl_set_def by simp

lemma defl_set_cast [simp]: "cast\<cdot>A\<cdot>x \<in> defl_set A"
unfolding defl_set_def by simp

lemma defl_set_subset_iff: "defl_set A \<subseteq> defl_set B \<longleftrightarrow> A \<sqsubseteq> B"
apply (simp add: defl_set_def subset_eq cast_below_cast [symmetric])
apply (auto simp add: cast.belowI cast.belowD)
done

subsection \<open>Proving a subtype is representable\<close>

text \<open>Temporarily relax type constraints.\<close>

setup \<open>
  fold Sign.add_const_constraint
  [ (\<^const_name>\<open>defl\<close>, SOME \<^typ>\<open>'a::pcpo itself \<Rightarrow> udom defl\<close>)
  , (\<^const_name>\<open>emb\<close>, SOME \<^typ>\<open>'a::pcpo \<rightarrow> udom\<close>)
  , (\<^const_name>\<open>prj\<close>, SOME \<^typ>\<open>udom \<rightarrow> 'a::pcpo\<close>)
  , (\<^const_name>\<open>liftdefl\<close>, SOME \<^typ>\<open>'a::pcpo itself \<Rightarrow> udom u defl\<close>)
  , (\<^const_name>\<open>liftemb\<close>, SOME \<^typ>\<open>'a::pcpo u \<rightarrow> udom u\<close>)
  , (\<^const_name>\<open>liftprj\<close>, SOME \<^typ>\<open>udom u \<rightarrow> 'a::pcpo u\<close>) ]
\<close>

lemma typedef_domain_class:
  fixes Rep :: "'a::pcpo \<Rightarrow> udom"
  fixes Abs :: "udom \<Rightarrow> 'a::pcpo"
  fixes t :: "udom defl"
  assumes type: "type_definition Rep Abs (defl_set t)"
  assumes below: "(\<sqsubseteq>) \<equiv> \<lambda>x y. Rep x \<sqsubseteq> Rep y"
  assumes emb: "emb \<equiv> (\<Lambda> x. Rep x)"
  assumes prj: "prj \<equiv> (\<Lambda> x. Abs (cast\<cdot>t\<cdot>x))"
  assumes defl: "defl \<equiv> (\<lambda> a::'a itself. t)"
  assumes liftemb: "(liftemb :: 'a u \<rightarrow> udom u) \<equiv> u_map\<cdot>emb"
  assumes liftprj: "(liftprj :: udom u \<rightarrow> 'a u) \<equiv> u_map\<cdot>prj"
  assumes liftdefl: "(liftdefl :: 'a itself \<Rightarrow> _) \<equiv> (\<lambda>t. liftdefl_of\<cdot>DEFL('a))"
  shows "OFCLASS('a, domain_class)"
proof
  have emb_beta: "\<And>x. emb\<cdot>x = Rep x"
    unfolding emb
    apply (rule beta_cfun)
    apply (rule typedef_cont_Rep [OF type below adm_defl_set cont_id])
    done
  have prj_beta: "\<And>y. prj\<cdot>y = Abs (cast\<cdot>t\<cdot>y)"
    unfolding prj
    apply (rule beta_cfun)
    apply (rule typedef_cont_Abs [OF type below adm_defl_set])
    apply simp_all
    done
  have prj_emb: "\<And>x::'a. prj\<cdot>(emb\<cdot>x) = x"
    using type_definition.Rep [OF type]
    unfolding prj_beta emb_beta defl_set_def
    by (simp add: type_definition.Rep_inverse [OF type])
  have emb_prj: "\<And>y. emb\<cdot>(prj\<cdot>y :: 'a) = cast\<cdot>t\<cdot>y"
    unfolding prj_beta emb_beta
    by (simp add: type_definition.Abs_inverse [OF type])
  show "ep_pair (emb :: 'a \<rightarrow> udom) prj"
    apply standard
    apply (simp add: prj_emb)
    apply (simp add: emb_prj cast.below)
    done
  show "cast\<cdot>DEFL('a) = emb oo (prj :: udom \<rightarrow> 'a)"
    by (rule cfun_eqI, simp add: defl emb_prj)
qed (simp_all only: liftemb liftprj liftdefl)

lemma typedef_DEFL:
  assumes "defl \<equiv> (\<lambda>a::'a::pcpo itself. t)"
  shows "DEFL('a::pcpo) = t"
unfolding assms ..

text \<open>Restore original typing constraints.\<close>

setup \<open>
  fold Sign.add_const_constraint
   [(\<^const_name>\<open>defl\<close>, SOME \<^typ>\<open>'a::domain itself \<Rightarrow> udom defl\<close>),
    (\<^const_name>\<open>emb\<close>, SOME \<^typ>\<open>'a::domain \<rightarrow> udom\<close>),
    (\<^const_name>\<open>prj\<close>, SOME \<^typ>\<open>udom \<rightarrow> 'a::domain\<close>),
    (\<^const_name>\<open>liftdefl\<close>, SOME \<^typ>\<open>'a::predomain itself \<Rightarrow> udom u defl\<close>),
    (\<^const_name>\<open>liftemb\<close>, SOME \<^typ>\<open>'a::predomain u \<rightarrow> udom u\<close>),
    (\<^const_name>\<open>liftprj\<close>, SOME \<^typ>\<open>udom u \<rightarrow> 'a::predomain u\<close>)]
\<close>

ML_file \<open>Tools/domaindef.ML\<close>

subsection \<open>Isomorphic deflations\<close>

definition isodefl :: "('a \<rightarrow> 'a) \<Rightarrow> udom defl \<Rightarrow> bool"
  where "isodefl d t \<longleftrightarrow> cast\<cdot>t = emb oo d oo prj"

definition isodefl' :: "('a::predomain \<rightarrow> 'a) \<Rightarrow> udom u defl \<Rightarrow> bool"
  where "isodefl' d t \<longleftrightarrow> cast\<cdot>t = liftemb oo u_map\<cdot>d oo liftprj"

lemma isodeflI: "(\<And>x. cast\<cdot>t\<cdot>x = emb\<cdot>(d\<cdot>(prj\<cdot>x))) \<Longrightarrow> isodefl d t"
unfolding isodefl_def by (simp add: cfun_eqI)

lemma cast_isodefl: "isodefl d t \<Longrightarrow> cast\<cdot>t = (\<Lambda> x. emb\<cdot>(d\<cdot>(prj\<cdot>x)))"
unfolding isodefl_def by (simp add: cfun_eqI)

lemma isodefl_strict: "isodefl d t \<Longrightarrow> d\<cdot>\<bottom> = \<bottom>"
unfolding isodefl_def
by (drule cfun_fun_cong [where x="\<bottom>"], simp)

lemma isodefl_imp_deflation:
  fixes d :: "'a \<rightarrow> 'a"
  assumes "isodefl d t" shows "deflation d"
proof
  note assms [unfolded isodefl_def, simp]
  fix x :: 'a
  show "d\<cdot>(d\<cdot>x) = d\<cdot>x"
    using cast.idem [of t "emb\<cdot>x"] by simp
  show "d\<cdot>x \<sqsubseteq> x"
    using cast.below [of t "emb\<cdot>x"] by simp
qed

lemma isodefl_ID_DEFL: "isodefl (ID :: 'a \<rightarrow> 'a) DEFL('a)"
unfolding isodefl_def by (simp add: cast_DEFL)

lemma isodefl_LIFTDEFL:
  "isodefl' (ID :: 'a \<rightarrow> 'a) LIFTDEFL('a::predomain)"
unfolding isodefl'_def by (simp add: cast_liftdefl u_map_ID)

lemma isodefl_DEFL_imp_ID: "isodefl (d :: 'a \<rightarrow> 'a) DEFL('a) \<Longrightarrow> d = ID"
unfolding isodefl_def
apply (simp add: cast_DEFL)
apply (simp add: cfun_eq_iff)
apply (rule allI)
apply (drule_tac x="emb\<cdot>x" in spec)
apply simp
done

lemma isodefl_bottom: "isodefl \<bottom> \<bottom>"
unfolding isodefl_def by (simp add: cfun_eq_iff)

lemma adm_isodefl:
  "cont f \<Longrightarrow> cont g \<Longrightarrow> adm (\<lambda>x. isodefl (f x) (g x))"
unfolding isodefl_def by simp

lemma isodefl_lub:
  assumes "chain d" and "chain t"
  assumes "\<And>i. isodefl (d i) (t i)"
  shows "isodefl (\<Squnion>i. d i) (\<Squnion>i. t i)"
using assms unfolding isodefl_def
by (simp add: contlub_cfun_arg contlub_cfun_fun)

lemma isodefl_fix:
  assumes "\<And>d t. isodefl d t \<Longrightarrow> isodefl (f\<cdot>d) (g\<cdot>t)"
  shows "isodefl (fix\<cdot>f) (fix\<cdot>g)"
unfolding fix_def2
apply (rule isodefl_lub, simp, simp)
apply (induct_tac i)
apply (simp add: isodefl_bottom)
apply (simp add: assms)
done

lemma isodefl_abs_rep:
  fixes abs and rep and d
  assumes DEFL: "DEFL('b) = DEFL('a)"
  assumes abs_def: "(abs :: 'a \<rightarrow> 'b) \<equiv> prj oo emb"
  assumes rep_def: "(rep :: 'b \<rightarrow> 'a) \<equiv> prj oo emb"
  shows "isodefl d t \<Longrightarrow> isodefl (abs oo d oo rep) t"
unfolding isodefl_def
by (simp add: cfun_eq_iff assms prj_emb_prj emb_prj_emb)

lemma isodefl'_liftdefl_of: "isodefl d t \<Longrightarrow> isodefl' d (liftdefl_of\<cdot>t)"
unfolding isodefl_def isodefl'_def
by (simp add: cast_liftdefl_of u_map_oo liftemb_eq liftprj_eq)

lemma isodefl_sfun:
  "isodefl d1 t1 \<Longrightarrow> isodefl d2 t2 \<Longrightarrow>
    isodefl (sfun_map\<cdot>d1\<cdot>d2) (sfun_defl\<cdot>t1\<cdot>t2)"
apply (rule isodeflI)
apply (simp add: cast_sfun_defl cast_isodefl)
apply (simp add: emb_sfun_def prj_sfun_def)
apply (simp add: sfun_map_map isodefl_strict)
done

lemma isodefl_ssum:
  "isodefl d1 t1 \<Longrightarrow> isodefl d2 t2 \<Longrightarrow>
    isodefl (ssum_map\<cdot>d1\<cdot>d2) (ssum_defl\<cdot>t1\<cdot>t2)"
apply (rule isodeflI)
apply (simp add: cast_ssum_defl cast_isodefl)
apply (simp add: emb_ssum_def prj_ssum_def)
apply (simp add: ssum_map_map isodefl_strict)
done

lemma isodefl_sprod:
  "isodefl d1 t1 \<Longrightarrow> isodefl d2 t2 \<Longrightarrow>
    isodefl (sprod_map\<cdot>d1\<cdot>d2) (sprod_defl\<cdot>t1\<cdot>t2)"
apply (rule isodeflI)
apply (simp add: cast_sprod_defl cast_isodefl)
apply (simp add: emb_sprod_def prj_sprod_def)
apply (simp add: sprod_map_map isodefl_strict)
done

lemma isodefl_prod:
  "isodefl d1 t1 \<Longrightarrow> isodefl d2 t2 \<Longrightarrow>
    isodefl (prod_map\<cdot>d1\<cdot>d2) (prod_defl\<cdot>t1\<cdot>t2)"
apply (rule isodeflI)
apply (simp add: cast_prod_defl cast_isodefl)
apply (simp add: emb_prod_def prj_prod_def)
apply (simp add: prod_map_map cfcomp1)
done

lemma isodefl_u:
  "isodefl d t \<Longrightarrow> isodefl (u_map\<cdot>d) (u_defl\<cdot>t)"
apply (rule isodeflI)
apply (simp add: cast_u_defl cast_isodefl)
apply (simp add: emb_u_def prj_u_def liftemb_eq liftprj_eq u_map_map)
done

lemma isodefl_u_liftdefl:
  "isodefl' d t \<Longrightarrow> isodefl (u_map\<cdot>d) (u_liftdefl\<cdot>t)"
apply (rule isodeflI)
apply (simp add: cast_u_liftdefl isodefl'_def)
apply (simp add: emb_u_def prj_u_def liftemb_eq liftprj_eq)
done

lemma encode_prod_u_map:
  "encode_prod_u\<cdot>(u_map\<cdot>(prod_map\<cdot>f\<cdot>g)\<cdot>(decode_prod_u\<cdot>x))
    = sprod_map\<cdot>(u_map\<cdot>f)\<cdot>(u_map\<cdot>g)\<cdot>x"
unfolding encode_prod_u_def decode_prod_u_def
apply (case_tac x, simp, rename_tac a b)
apply (case_tac a, simp, case_tac b, simp, simp)
done

lemma isodefl_prod_u:
  assumes "isodefl' d1 t1" and "isodefl' d2 t2"
  shows "isodefl' (prod_map\<cdot>d1\<cdot>d2) (prod_liftdefl\<cdot>t1\<cdot>t2)"
using assms unfolding isodefl'_def
unfolding liftemb_prod_def liftprj_prod_def
by (simp add: cast_prod_liftdefl cfcomp1 encode_prod_u_map sprod_map_map)

lemma encode_cfun_map:
  "encode_cfun\<cdot>(cfun_map\<cdot>f\<cdot>g\<cdot>(decode_cfun\<cdot>x))
    = sfun_map\<cdot>(u_map\<cdot>f)\<cdot>g\<cdot>x"
unfolding encode_cfun_def decode_cfun_def
apply (simp add: sfun_eq_iff cfun_map_def sfun_map_def)
apply (rule cfun_eqI, rename_tac y, case_tac y, simp_all)
done

lemma isodefl_cfun:
  assumes "isodefl (u_map\<cdot>d1) t1" and "isodefl d2 t2"
  shows "isodefl (cfun_map\<cdot>d1\<cdot>d2) (sfun_defl\<cdot>t1\<cdot>t2)"
using isodefl_sfun [OF assms] unfolding isodefl_def
by (simp add: emb_cfun_def prj_cfun_def cfcomp1 encode_cfun_map)

subsection \<open>Setting up the domain package\<close>

named_theorems domain_defl_simps "theorems like DEFL('a t) = t_defl$DEFL('a)"
  and domain_isodefl "theorems like isodefl d t ==> isodefl (foo_map$d) (foo_defl$t)"

ML_file \<open>Tools/Domain/domain_isomorphism.ML\<close>
ML_file \<open>Tools/Domain/domain_axioms.ML\<close>
ML_file \<open>Tools/Domain/domain.ML\<close>

lemmas [domain_defl_simps] =
  DEFL_cfun DEFL_sfun DEFL_ssum DEFL_sprod DEFL_prod DEFL_u
  liftdefl_eq LIFTDEFL_prod u_liftdefl_liftdefl_of

lemmas [domain_map_ID] =
  cfun_map_ID sfun_map_ID ssum_map_ID sprod_map_ID prod_map_ID u_map_ID

lemmas [domain_isodefl] =
  isodefl_u isodefl_sfun isodefl_ssum isodefl_sprod
  isodefl_cfun isodefl_prod isodefl_prod_u isodefl'_liftdefl_of
  isodefl_u_liftdefl

lemmas [domain_deflation] =
  deflation_cfun_map deflation_sfun_map deflation_ssum_map
  deflation_sprod_map deflation_prod_map deflation_u_map

setup \<open>
  fold Domain_Take_Proofs.add_rec_type
    [(\<^type_name>\<open>cfun\<close>, [true, true]),
     (\<^type_name>\<open>sfun\<close>, [true, true]),
     (\<^type_name>\<open>ssum\<close>, [true, true]),
     (\<^type_name>\<open>sprod\<close>, [true, true]),
     (\<^type_name>\<open>prod\<close>, [true, true]),
     (\<^type_name>\<open>u\<close>, [true])]
\<close>

end
