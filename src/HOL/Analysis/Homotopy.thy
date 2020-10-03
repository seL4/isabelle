(*  Title:      HOL/Analysis/Path_Connected.thy
    Authors:    LC Paulson and Robert Himmelmann (TU Muenchen), based on material from HOL Light
*)

section \<open>Homotopy of Maps\<close>

theory Homotopy
  imports Path_Connected Continuum_Not_Denumerable Product_Topology
begin

definition\<^marker>\<open>tag important\<close> homotopic_with
where
 "homotopic_with P X Y f g \<equiv>
   (\<exists>h. continuous_map (prod_topology (top_of_set {0..1::real}) X) Y h \<and>
       (\<forall>x. h(0, x) = f x) \<and>
       (\<forall>x. h(1, x) = g x) \<and>
       (\<forall>t \<in> {0..1}. P(\<lambda>x. h(t,x))))"

text\<open>\<open>p\<close>, \<open>q\<close> are functions \<open>X \<rightarrow> Y\<close>, and the property \<open>P\<close> restricts all intermediate maps.
We often just want to require that \<open>P\<close> fixes some subset, but to include the case of a loop homotopy,
it is convenient to have a general property \<open>P\<close>.\<close>

abbreviation homotopic_with_canon ::
  "[('a::topological_space \<Rightarrow> 'b::topological_space) \<Rightarrow> bool, 'a set, 'b set, 'a \<Rightarrow> 'b, 'a \<Rightarrow> 'b] \<Rightarrow> bool"
where
 "homotopic_with_canon P S T p q \<equiv> homotopic_with P (top_of_set S) (top_of_set T) p q"

lemma split_01: "{0..1::real} = {0..1/2} \<union> {1/2..1}"
  by force

lemma split_01_prod: "{0..1::real} \<times> X = ({0..1/2} \<times> X) \<union> ({1/2..1} \<times> X)"
  by force

lemma image_Pair_const: "(\<lambda>x. (x, c)) ` A = A \<times> {c}"
  by auto

lemma fst_o_paired [simp]: "fst \<circ> (\<lambda>(x,y). (f x y, g x y)) = (\<lambda>(x,y). f x y)"
  by auto

lemma snd_o_paired [simp]: "snd \<circ> (\<lambda>(x,y). (f x y, g x y)) = (\<lambda>(x,y). g x y)"
  by auto

lemma continuous_on_o_Pair: "\<lbrakk>continuous_on (T \<times> X) h; t \<in> T\<rbrakk> \<Longrightarrow> continuous_on X (h \<circ> Pair t)"
  by (fast intro: continuous_intros elim!: continuous_on_subset)

lemma continuous_map_o_Pair: 
  assumes h: "continuous_map (prod_topology X Y) Z h" and t: "t \<in> topspace X"
  shows "continuous_map Y Z (h \<circ> Pair t)"
  by (intro continuous_map_compose [OF _ h] continuous_intros; simp add: t)

subsection\<^marker>\<open>tag unimportant\<close>\<open>Trivial properties\<close>

text \<open>We often want to just localize the ending function equality or whatever.\<close>
text\<^marker>\<open>tag important\<close> \<open>%whitespace\<close>
proposition homotopic_with:
  assumes "\<And>h k. (\<And>x. x \<in> topspace X \<Longrightarrow> h x = k x) \<Longrightarrow> (P h \<longleftrightarrow> P k)"
  shows "homotopic_with P X Y p q \<longleftrightarrow>
           (\<exists>h. continuous_map (prod_topology (subtopology euclideanreal {0..1}) X) Y h \<and>
              (\<forall>x \<in> topspace X. h(0,x) = p x) \<and>
              (\<forall>x \<in> topspace X. h(1,x) = q x) \<and>
              (\<forall>t \<in> {0..1}. P(\<lambda>x. h(t, x))))"
  unfolding homotopic_with_def
  apply (rule iffI, blast, clarify)
  apply (rule_tac x="\<lambda>(u,v). if v \<in> topspace X then h(u,v) else if u = 0 then p v else q v" in exI)
  apply auto
  using continuous_map_eq apply fastforce
  apply (drule_tac x=t in bspec, force)
  apply (subst assms; simp)
  done

lemma homotopic_with_mono:
  assumes hom: "homotopic_with P X Y f g"
    and Q: "\<And>h. \<lbrakk>continuous_map X Y h; P h\<rbrakk> \<Longrightarrow> Q h"
  shows "homotopic_with Q X Y f g"
  using hom unfolding homotopic_with_def
  by (force simp: o_def dest: continuous_map_o_Pair intro: Q)

lemma homotopic_with_imp_continuous_maps:
    assumes "homotopic_with P X Y f g"
    shows "continuous_map X Y f \<and> continuous_map X Y g"
proof -
  obtain h :: "real \<times> 'a \<Rightarrow> 'b"
    where conth: "continuous_map (prod_topology (top_of_set {0..1}) X) Y h"
      and h: "\<forall>x. h (0, x) = f x" "\<forall>x. h (1, x) = g x"
    using assms by (auto simp: homotopic_with_def)
  have *: "t \<in> {0..1} \<Longrightarrow> continuous_map X Y (h \<circ> (\<lambda>x. (t,x)))" for t
    by (rule continuous_map_compose [OF _ conth]) (simp add: o_def continuous_map_pairwise)
  show ?thesis
    using h *[of 0] *[of 1] by (simp add: continuous_map_eq)
qed

lemma homotopic_with_imp_continuous:
    assumes "homotopic_with_canon P X Y f g"
    shows "continuous_on X f \<and> continuous_on X g"
  by (meson assms continuous_map_subtopology_eu homotopic_with_imp_continuous_maps)

lemma homotopic_with_imp_property:
  assumes "homotopic_with P X Y f g"
  shows "P f \<and> P g"
proof
  obtain h where h: "\<And>x. h(0, x) = f x" "\<And>x. h(1, x) = g x" and P: "\<And>t. t \<in> {0..1::real} \<Longrightarrow> P(\<lambda>x. h(t,x))"
    using assms by (force simp: homotopic_with_def)
  show "P f" "P g"
    using P [of 0] P [of 1] by (force simp: h)+
qed

lemma homotopic_with_equal:
  assumes "P f" "P g" and contf: "continuous_map X Y f" and fg: "\<And>x. x \<in> topspace X \<Longrightarrow> f x = g x"
  shows "homotopic_with P X Y f g"
  unfolding homotopic_with_def
proof (intro exI conjI allI ballI)
  let ?h = "\<lambda>(t::real,x). if t = 1 then g x else f x"
  show "continuous_map (prod_topology (top_of_set {0..1}) X) Y ?h"
  proof (rule continuous_map_eq)
    show "continuous_map (prod_topology (top_of_set {0..1}) X) Y (f \<circ> snd)"
      by (simp add: contf continuous_map_of_snd)
  qed (auto simp: fg)
  show "P (\<lambda>x. ?h (t, x))" if "t \<in> {0..1}" for t
    by (cases "t = 1") (simp_all add: assms)
qed auto

lemma homotopic_with_imp_subset1:
     "homotopic_with_canon P X Y f g \<Longrightarrow> f ` X \<subseteq> Y"
  by (simp add: homotopic_with_def image_subset_iff) (metis atLeastAtMost_iff order_refl zero_le_one)

lemma homotopic_with_imp_subset2:
     "homotopic_with_canon P X Y f g \<Longrightarrow> g ` X \<subseteq> Y"
  by (simp add: homotopic_with_def image_subset_iff) (metis atLeastAtMost_iff order_refl zero_le_one)

lemma homotopic_with_subset_left:
     "\<lbrakk>homotopic_with_canon P X Y f g; Z \<subseteq> X\<rbrakk> \<Longrightarrow> homotopic_with_canon P Z Y f g"
  unfolding homotopic_with_def by (auto elim!: continuous_on_subset ex_forward)

lemma homotopic_with_subset_right:
     "\<lbrakk>homotopic_with_canon P X Y f g; Y \<subseteq> Z\<rbrakk> \<Longrightarrow> homotopic_with_canon P X Z f g"
  unfolding homotopic_with_def by (auto elim!: continuous_on_subset ex_forward)

subsection\<open>Homotopy with P is an equivalence relation\<close>

text \<open>(on continuous functions mapping X into Y that satisfy P, though this only affects reflexivity)\<close>

lemma homotopic_with_refl [simp]: "homotopic_with P X Y f f \<longleftrightarrow> continuous_map X Y f \<and> P f"
  by (auto simp: homotopic_with_imp_continuous_maps intro: homotopic_with_equal dest: homotopic_with_imp_property)

lemma homotopic_with_symD:
    assumes "homotopic_with P X Y f g"
      shows "homotopic_with P X Y g f"
proof -
  let ?I01 = "subtopology euclideanreal {0..1}"
  let ?j = "\<lambda>y. (1 - fst y, snd y)"
  have 1: "continuous_map (prod_topology ?I01 X) (prod_topology euclideanreal X) ?j"
    by (intro continuous_intros; simp add: continuous_map_subtopology_fst prod_topology_subtopology)
  have *: "continuous_map (prod_topology ?I01 X) (prod_topology ?I01 X) ?j"
  proof -
    have "continuous_map (prod_topology ?I01 X) (subtopology (prod_topology euclideanreal X) ({0..1} \<times> topspace X)) ?j"
      by (simp add: continuous_map_into_subtopology [OF 1] image_subset_iff)
    then show ?thesis
      by (simp add: prod_topology_subtopology(1))
  qed
  show ?thesis
    using assms
    apply (clarsimp simp add: homotopic_with_def)
    subgoal for h
      by (rule_tac x="h \<circ> (\<lambda>y. (1 - fst y, snd y))" in exI) (simp add: continuous_map_compose [OF *])
    done
qed

lemma homotopic_with_sym:
   "homotopic_with P X Y f g \<longleftrightarrow> homotopic_with P X Y g f"
  by (metis homotopic_with_symD)

proposition homotopic_with_trans:
    assumes "homotopic_with P X Y f g"  "homotopic_with P X Y g h"
    shows "homotopic_with P X Y f h"
proof -
  let ?X01 = "prod_topology (subtopology euclideanreal {0..1}) X"
  obtain k1 k2
    where contk1: "continuous_map ?X01 Y k1" and contk2: "continuous_map ?X01 Y k2"
      and k12: "\<forall>x. k1 (1, x) = g x" "\<forall>x. k2 (0, x) = g x"
      "\<forall>x. k1 (0, x) = f x" "\<forall>x. k2 (1, x) = h x"
      and P:   "\<forall>t\<in>{0..1}. P (\<lambda>x. k1 (t, x))" "\<forall>t\<in>{0..1}. P (\<lambda>x. k2 (t, x))"
    using assms by (auto simp: homotopic_with_def)
  define k where "k \<equiv> \<lambda>y. if fst y \<le> 1/2
                             then (k1 \<circ> (\<lambda>x. (2 *\<^sub>R fst x, snd x))) y
                             else (k2 \<circ> (\<lambda>x. (2 *\<^sub>R fst x -1, snd x))) y"
  have keq: "k1 (2 * u, v) = k2 (2 * u -1, v)" if "u = 1/2"  for u v
    by (simp add: k12 that)
  show ?thesis
    unfolding homotopic_with_def
  proof (intro exI conjI)
    show "continuous_map ?X01 Y k"
      unfolding k_def
    proof (rule continuous_map_cases_le)
      show fst: "continuous_map ?X01 euclideanreal fst"
        using continuous_map_fst continuous_map_in_subtopology by blast
      show "continuous_map ?X01 euclideanreal (\<lambda>x. 1/2)"
        by simp
      show "continuous_map (subtopology ?X01 {y \<in> topspace ?X01. fst y \<le> 1/2}) Y
               (k1 \<circ> (\<lambda>x. (2 *\<^sub>R fst x, snd x)))"
        apply (intro fst continuous_map_compose [OF _ contk1] continuous_intros continuous_map_into_subtopology continuous_map_from_subtopology | simp)+
        by (force simp: prod_topology_subtopology)
      show "continuous_map (subtopology ?X01 {y \<in> topspace ?X01. 1/2 \<le> fst y}) Y
               (k2 \<circ> (\<lambda>x. (2 *\<^sub>R fst x -1, snd x)))"
        apply (intro fst continuous_map_compose [OF _ contk2] continuous_intros continuous_map_into_subtopology continuous_map_from_subtopology | simp)+
        by (force simp: prod_topology_subtopology)
      show "(k1 \<circ> (\<lambda>x. (2 *\<^sub>R fst x, snd x))) y = (k2 \<circ> (\<lambda>x. (2 *\<^sub>R fst x -1, snd x))) y"
        if "y \<in> topspace ?X01" and "fst y = 1/2" for y
        using that by (simp add: keq)
    qed
    show "\<forall>x. k (0, x) = f x"
      by (simp add: k12 k_def)
    show "\<forall>x. k (1, x) = h x"
      by (simp add: k12 k_def)
    show "\<forall>t\<in>{0..1}. P (\<lambda>x. k (t, x))"
    proof 
      fix t show "t\<in>{0..1} \<Longrightarrow> P (\<lambda>x. k (t, x))"
        by (cases "t \<le> 1/2") (auto simp add: k_def P)
    qed
  qed
qed

lemma homotopic_with_id2: 
  "(\<And>x. x \<in> topspace X \<Longrightarrow> g (f x) = x) \<Longrightarrow> homotopic_with (\<lambda>x. True) X X (g \<circ> f) id"
  by (metis comp_apply continuous_map_id eq_id_iff homotopic_with_equal homotopic_with_symD)

subsection\<open>Continuity lemmas\<close>

lemma homotopic_with_compose_continuous_map_left:
  "\<lbrakk>homotopic_with p X1 X2 f g; continuous_map X2 X3 h; \<And>j. p j \<Longrightarrow> q(h \<circ> j)\<rbrakk>
   \<Longrightarrow> homotopic_with q X1 X3 (h \<circ> f) (h \<circ> g)"
  unfolding homotopic_with_def
  apply clarify
  subgoal for k
    by (rule_tac x="h \<circ> k" in exI) (rule conjI continuous_map_compose | simp add: o_def)+
  done

lemma homotopic_with_compose_continuous_map_right:
  assumes hom: "homotopic_with p X2 X3 f g" and conth: "continuous_map X1 X2 h"
    and q: "\<And>j. p j \<Longrightarrow> q(j \<circ> h)"
  shows "homotopic_with q X1 X3 (f \<circ> h) (g \<circ> h)"
proof -
  obtain k
    where contk: "continuous_map (prod_topology (subtopology euclideanreal {0..1}) X2) X3 k"
      and k: "\<forall>x. k (0, x) = f x" "\<forall>x. k (1, x) = g x" and p: "\<And>t. t\<in>{0..1} \<Longrightarrow> p (\<lambda>x. k (t, x))"
    using hom unfolding homotopic_with_def by blast
  have hsnd: "continuous_map (prod_topology (subtopology euclideanreal {0..1}) X1) X2 (h \<circ> snd)"
    by (rule continuous_map_compose [OF continuous_map_snd conth])
  let ?h = "k \<circ> (\<lambda>(t,x). (t,h x))"
  show ?thesis
    unfolding homotopic_with_def
  proof (intro exI conjI allI ballI)
    have "continuous_map (prod_topology (top_of_set {0..1}) X1)
     (prod_topology (top_of_set {0..1::real}) X2) (\<lambda>(t, x). (t, h x))"
      by (metis (mono_tags, lifting) case_prod_beta' comp_def continuous_map_eq continuous_map_fst continuous_map_pairedI hsnd)
    then show "continuous_map (prod_topology (subtopology euclideanreal {0..1}) X1) X3 ?h"
      by (intro conjI continuous_map_compose [OF _ contk])
    show "q (\<lambda>x. ?h (t, x))" if "t \<in> {0..1}" for t
      using q [OF p [OF that]] by (simp add: o_def)
  qed (auto simp: k)
qed

corollary homotopic_compose:
  assumes "homotopic_with (\<lambda>x. True) X Y f f'" "homotopic_with (\<lambda>x. True) Y Z g g'"
  shows "homotopic_with (\<lambda>x. True) X Z (g \<circ> f) (g' \<circ> f')"
proof (rule homotopic_with_trans [where g = "g \<circ> f'"])
  show "homotopic_with (\<lambda>x. True) X Z (g \<circ> f) (g \<circ> f')"
    using assms by (simp add: homotopic_with_compose_continuous_map_left homotopic_with_imp_continuous_maps)
  show "homotopic_with (\<lambda>x. True) X Z (g \<circ> f') (g' \<circ> f')"
    using assms by (simp add: homotopic_with_compose_continuous_map_right homotopic_with_imp_continuous_maps)
qed

proposition homotopic_with_compose_continuous_right:
    "\<lbrakk>homotopic_with_canon (\<lambda>f. p (f \<circ> h)) X Y f g; continuous_on W h; h ` W \<subseteq> X\<rbrakk>
     \<Longrightarrow> homotopic_with_canon p W Y (f \<circ> h) (g \<circ> h)"
  apply (clarsimp simp add: homotopic_with_def)
  subgoal for k
    apply (rule_tac x="k \<circ> (\<lambda>y. (fst y, h (snd y)))" in exI)
    by (intro conjI continuous_intros continuous_on_compose2 [where f=snd and g=h]; fastforce simp: o_def elim: continuous_on_subset)
  done

proposition homotopic_with_compose_continuous_left:
     "\<lbrakk>homotopic_with_canon (\<lambda>f. p (h \<circ> f)) X Y f g; continuous_on Y h; h ` Y \<subseteq> Z\<rbrakk>
      \<Longrightarrow> homotopic_with_canon p X Z (h \<circ> f) (h \<circ> g)"
  apply (clarsimp simp add: homotopic_with_def)
  subgoal for k
  apply (rule_tac x="h \<circ> k" in exI)
    by (intro conjI continuous_intros continuous_on_compose [where f=snd and g=h, unfolded o_def]; fastforce simp: o_def elim: continuous_on_subset)
  done

lemma homotopic_from_subtopology:
   "homotopic_with P X X' f g \<Longrightarrow> homotopic_with P (subtopology X s) X' f g"
  unfolding homotopic_with_def
  by (force simp add: continuous_map_from_subtopology prod_topology_subtopology(2) elim!: ex_forward)

lemma homotopic_on_emptyI:
    assumes "topspace X = {}" "P f" "P g"
    shows "homotopic_with P X X' f g"
  unfolding homotopic_with_def
proof (intro exI conjI ballI)
  show "P (\<lambda>x. (\<lambda>(t,x). if t = 0 then f x else g x) (t, x))" if "t \<in> {0..1}" for t::real
    by (cases "t = 0", auto simp: assms)
qed (auto simp: continuous_map_atin assms)

lemma homotopic_on_empty:
   "topspace X = {} \<Longrightarrow> (homotopic_with P X X' f g \<longleftrightarrow> P f \<and> P g)"
  using homotopic_on_emptyI homotopic_with_imp_property by metis

lemma homotopic_with_canon_on_empty [simp]: "homotopic_with_canon (\<lambda>x. True) {} t f g"
  by (auto intro: homotopic_with_equal)

lemma homotopic_constant_maps:
   "homotopic_with (\<lambda>x. True) X X' (\<lambda>x. a) (\<lambda>x. b) \<longleftrightarrow>
    topspace X = {} \<or> path_component_of X' a b" (is "?lhs = ?rhs")
proof (cases "topspace X = {}")
  case False
  then obtain c where c: "c \<in> topspace X"
    by blast
  have "\<exists>g. continuous_map (top_of_set {0..1::real}) X' g \<and> g 0 = a \<and> g 1 = b"
    if "x \<in> topspace X" and hom: "homotopic_with (\<lambda>x. True) X X' (\<lambda>x. a) (\<lambda>x. b)" for x
  proof -
    obtain h :: "real \<times> 'a \<Rightarrow> 'b"
      where conth: "continuous_map (prod_topology (top_of_set {0..1}) X) X' h"
        and h: "\<And>x. h (0, x) = a" "\<And>x. h (1, x) = b"
      using hom by (auto simp: homotopic_with_def)
    have cont: "continuous_map (top_of_set {0..1}) X' (h \<circ> (\<lambda>t. (t, c)))"
      by (rule continuous_map_compose [OF _ conth] continuous_intros c | simp)+
    then show ?thesis
      by (force simp: h)
  qed
  moreover have "homotopic_with (\<lambda>x. True) X X' (\<lambda>x. g 0) (\<lambda>x. g 1)"
    if "x \<in> topspace X" "a = g 0" "b = g 1" "continuous_map (top_of_set {0..1}) X' g"
    for x and g :: "real \<Rightarrow> 'b"
    unfolding homotopic_with_def
    by (force intro!: continuous_map_compose continuous_intros c that)
  ultimately show ?thesis
    using False by (auto simp: path_component_of_def pathin_def)
qed (simp add: homotopic_on_empty)

proposition homotopic_with_eq:
   assumes h: "homotopic_with P X Y f g"
       and f': "\<And>x. x \<in> topspace X \<Longrightarrow> f' x = f x"
       and g': "\<And>x. x \<in> topspace X \<Longrightarrow> g' x = g x"
       and P:  "(\<And>h k. (\<And>x. x \<in> topspace X \<Longrightarrow> h x = k x) \<Longrightarrow> P h \<longleftrightarrow> P k)"
   shows "homotopic_with P X Y f' g'"
  using h unfolding homotopic_with_def
  apply clarify
  subgoal for h
    apply (rule_tac x="\<lambda>(u,v). if v \<in> topspace X then h(u,v) else if u = 0 then f' v else g' v" in exI)
    apply (simp add: f' g', safe)
     apply (fastforce intro: continuous_map_eq)
    apply (subst P; fastforce)
    done
  done

lemma homotopic_with_prod_topology:
  assumes "homotopic_with p X1 Y1 f f'" and "homotopic_with q X2 Y2 g g'"
    and r: "\<And>i j. \<lbrakk>p i; q j\<rbrakk> \<Longrightarrow> r(\<lambda>(x,y). (i x, j y))"
  shows "homotopic_with r (prod_topology X1 X2) (prod_topology Y1 Y2)
                          (\<lambda>z. (f(fst z),g(snd z))) (\<lambda>z. (f'(fst z), g'(snd z)))"
proof -
  obtain h
    where h: "continuous_map (prod_topology (subtopology euclideanreal {0..1}) X1) Y1 h"
      and h0: "\<And>x. h (0, x) = f x"
      and h1: "\<And>x. h (1, x) = f' x"
      and p: "\<And>t. \<lbrakk>0 \<le> t; t \<le> 1\<rbrakk> \<Longrightarrow> p (\<lambda>x. h (t,x))"
    using assms unfolding homotopic_with_def by auto
  obtain k
    where k: "continuous_map (prod_topology (subtopology euclideanreal {0..1}) X2) Y2 k"
      and k0: "\<And>x. k (0, x) = g x"
      and k1: "\<And>x. k (1, x) = g' x"
      and q: "\<And>t. \<lbrakk>0 \<le> t; t \<le> 1\<rbrakk> \<Longrightarrow> q (\<lambda>x. k (t,x))"
    using assms unfolding homotopic_with_def by auto
  let ?hk = "\<lambda>(t,x,y). (h(t,x), k(t,y))"
  show ?thesis
    unfolding homotopic_with_def
  proof (intro conjI allI exI)
    show "continuous_map (prod_topology (subtopology euclideanreal {0..1}) (prod_topology X1 X2))
                         (prod_topology Y1 Y2) ?hk"
      unfolding continuous_map_pairwise case_prod_unfold
      by (rule conjI continuous_map_pairedI continuous_intros continuous_map_id [unfolded id_def]
          continuous_map_fst_of [unfolded o_def] continuous_map_snd_of [unfolded o_def]
          continuous_map_compose [OF _ h, unfolded o_def]
          continuous_map_compose [OF _ k, unfolded o_def])+
  next
    fix x
    show "?hk (0, x) = (f (fst x), g (snd x))" "?hk (1, x) = (f' (fst x), g' (snd x))"
      by (auto simp: case_prod_beta h0 k0 h1 k1)
  qed (auto simp: p q r)
qed


lemma homotopic_with_product_topology:
  assumes ht: "\<And>i. i \<in> I \<Longrightarrow> homotopic_with (p i) (X i) (Y i) (f i) (g i)"
    and pq: "\<And>h. (\<And>i. i \<in> I \<Longrightarrow> p i (h i)) \<Longrightarrow> q(\<lambda>x. (\<lambda>i\<in>I. h i (x i)))"
  shows "homotopic_with q (product_topology X I) (product_topology Y I)
                          (\<lambda>z. (\<lambda>i\<in>I. (f i) (z i))) (\<lambda>z. (\<lambda>i\<in>I. (g i) (z i)))"
proof -
  obtain h
    where h: "\<And>i. i \<in> I \<Longrightarrow> continuous_map (prod_topology (subtopology euclideanreal {0..1}) (X i)) (Y i) (h i)"
      and h0: "\<And>i x. i \<in> I \<Longrightarrow> h i (0, x) = f i x"
      and h1: "\<And>i x. i \<in> I \<Longrightarrow> h i (1, x) = g i x"
      and p: "\<And>i t. \<lbrakk>i \<in> I; t \<in> {0..1}\<rbrakk> \<Longrightarrow> p i (\<lambda>x. h i (t,x))"
    using ht unfolding homotopic_with_def by metis
  show ?thesis
    unfolding homotopic_with_def
  proof (intro conjI allI exI)
    let ?h = "\<lambda>(t,z). \<lambda>i\<in>I. h i (t,z i)"
    have "continuous_map (prod_topology (subtopology euclideanreal {0..1}) (product_topology X I))
                         (Y i) (\<lambda>x. h i (fst x, snd x i))" if "i \<in> I" for i
    proof -
      have \<section>: "continuous_map (prod_topology (top_of_set {0..1}) (product_topology X I)) (X i) (\<lambda>x. snd x i)"
        using continuous_map_componentwise continuous_map_snd that by fastforce
      show ?thesis
        unfolding continuous_map_pairwise case_prod_unfold
        by (intro conjI that \<section> continuous_intros continuous_map_compose [OF _ h, unfolded o_def])
    qed
    then show "continuous_map (prod_topology (subtopology euclideanreal {0..1}) (product_topology X I))
         (product_topology Y I) ?h"
      by (auto simp: continuous_map_componentwise case_prod_beta)
    show "?h (0, x) = (\<lambda>i\<in>I. f i (x i))" "?h (1, x) = (\<lambda>i\<in>I. g i (x i))" for x
      by (auto simp: case_prod_beta h0 h1)
    show "\<forall>t\<in>{0..1}. q (\<lambda>x. ?h (t, x))"
      by (force intro: p pq)
  qed
qed

text\<open>Homotopic triviality implicitly incorporates path-connectedness.\<close>
lemma homotopic_triviality:
  shows  "(\<forall>f g. continuous_on S f \<and> f ` S \<subseteq> T \<and>
                 continuous_on S g \<and> g ` S \<subseteq> T
                 \<longrightarrow> homotopic_with_canon (\<lambda>x. True) S T f g) \<longleftrightarrow>
          (S = {} \<or> path_connected T) \<and>
          (\<forall>f. continuous_on S f \<and> f ` S \<subseteq> T \<longrightarrow> (\<exists>c. homotopic_with_canon (\<lambda>x. True) S T f (\<lambda>x. c)))"
          (is "?lhs = ?rhs")
proof (cases "S = {} \<or> T = {}")
  case True then show ?thesis
    by (auto simp: homotopic_on_emptyI)
next
  case False show ?thesis
  proof
    assume LHS [rule_format]: ?lhs
    have pab: "path_component T a b" if "a \<in> T" "b \<in> T" for a b
    proof -
      have "homotopic_with_canon (\<lambda>x. True) S T (\<lambda>x. a) (\<lambda>x. b)"
        by (simp add: LHS image_subset_iff that)
      then show ?thesis
        using False homotopic_constant_maps [of "top_of_set S" "top_of_set T" a b] by auto
    qed
    moreover
    have "\<exists>c. homotopic_with_canon (\<lambda>x. True) S T f (\<lambda>x. c)" if "continuous_on S f" "f ` S \<subseteq> T" for f
      using False LHS continuous_on_const that by blast
    ultimately show ?rhs
      by (simp add: path_connected_component)
  next
    assume RHS: ?rhs
    with False have T: "path_connected T"
      by blast
    show ?lhs
    proof clarify
      fix f g
      assume "continuous_on S f" "f ` S \<subseteq> T" "continuous_on S g" "g ` S \<subseteq> T"
      obtain c d where c: "homotopic_with_canon (\<lambda>x. True) S T f (\<lambda>x. c)" and d: "homotopic_with_canon (\<lambda>x. True) S T g (\<lambda>x. d)"
        using False \<open>continuous_on S f\<close> \<open>f ` S \<subseteq> T\<close>  RHS \<open>continuous_on S g\<close> \<open>g ` S \<subseteq> T\<close> by blast
      then have "c \<in> T" "d \<in> T"
        using False homotopic_with_imp_continuous_maps by fastforce+
      with T have "path_component T c d"
        using path_connected_component by blast
      then have "homotopic_with_canon (\<lambda>x. True) S T (\<lambda>x. c) (\<lambda>x. d)"
        by (simp add: homotopic_constant_maps)
      with c d show "homotopic_with_canon (\<lambda>x. True) S T f g"
        by (meson homotopic_with_symD homotopic_with_trans)
    qed
  qed
qed


subsection\<open>Homotopy of paths, maintaining the same endpoints\<close>


definition\<^marker>\<open>tag important\<close> homotopic_paths :: "['a set, real \<Rightarrow> 'a, real \<Rightarrow> 'a::topological_space] \<Rightarrow> bool"
  where
     "homotopic_paths s p q \<equiv>
       homotopic_with_canon (\<lambda>r. pathstart r = pathstart p \<and> pathfinish r = pathfinish p) {0..1} s p q"

lemma homotopic_paths:
   "homotopic_paths s p q \<longleftrightarrow>
      (\<exists>h. continuous_on ({0..1} \<times> {0..1}) h \<and>
          h ` ({0..1} \<times> {0..1}) \<subseteq> s \<and>
          (\<forall>x \<in> {0..1}. h(0,x) = p x) \<and>
          (\<forall>x \<in> {0..1}. h(1,x) = q x) \<and>
          (\<forall>t \<in> {0..1::real}. pathstart(h \<circ> Pair t) = pathstart p \<and>
                        pathfinish(h \<circ> Pair t) = pathfinish p))"
  by (auto simp: homotopic_paths_def homotopic_with pathstart_def pathfinish_def)

proposition homotopic_paths_imp_pathstart:
     "homotopic_paths s p q \<Longrightarrow> pathstart p = pathstart q"
  by (metis (mono_tags, lifting) homotopic_paths_def homotopic_with_imp_property)

proposition homotopic_paths_imp_pathfinish:
     "homotopic_paths s p q \<Longrightarrow> pathfinish p = pathfinish q"
  by (metis (mono_tags, lifting) homotopic_paths_def homotopic_with_imp_property)

lemma homotopic_paths_imp_path:
     "homotopic_paths s p q \<Longrightarrow> path p \<and> path q"
  using homotopic_paths_def homotopic_with_imp_continuous_maps path_def continuous_map_subtopology_eu by blast

lemma homotopic_paths_imp_subset:
     "homotopic_paths s p q \<Longrightarrow> path_image p \<subseteq> s \<and> path_image q \<subseteq> s"
  by (metis (mono_tags) continuous_map_subtopology_eu homotopic_paths_def homotopic_with_imp_continuous_maps path_image_def)

proposition homotopic_paths_refl [simp]: "homotopic_paths s p p \<longleftrightarrow> path p \<and> path_image p \<subseteq> s"
  by (simp add: homotopic_paths_def path_def path_image_def)

proposition homotopic_paths_sym: "homotopic_paths s p q \<Longrightarrow> homotopic_paths s q p"
  by (metis (mono_tags) homotopic_paths_def homotopic_paths_imp_pathfinish homotopic_paths_imp_pathstart homotopic_with_symD)

proposition homotopic_paths_sym_eq: "homotopic_paths s p q \<longleftrightarrow> homotopic_paths s q p"
  by (metis homotopic_paths_sym)

proposition homotopic_paths_trans [trans]:
  assumes "homotopic_paths s p q" "homotopic_paths s q r"
  shows "homotopic_paths s p r"
proof -
  have "pathstart q = pathstart p" "pathfinish q = pathfinish p"
    using assms by (simp_all add: homotopic_paths_imp_pathstart homotopic_paths_imp_pathfinish)
  then have "homotopic_with_canon (\<lambda>f. pathstart f = pathstart p \<and> pathfinish f = pathfinish p) {0..1} s q r"
    using \<open>homotopic_paths s q r\<close> homotopic_paths_def by force
  then show ?thesis
    using assms homotopic_paths_def homotopic_with_trans by blast
qed

proposition homotopic_paths_eq:
     "\<lbrakk>path p; path_image p \<subseteq> s; \<And>t. t \<in> {0..1} \<Longrightarrow> p t = q t\<rbrakk> \<Longrightarrow> homotopic_paths s p q"
  unfolding homotopic_paths_def
  by (rule homotopic_with_eq)
     (auto simp: path_def pathstart_def pathfinish_def path_image_def elim: continuous_on_eq)

proposition homotopic_paths_reparametrize:
  assumes "path p"
      and pips: "path_image p \<subseteq> s"
      and contf: "continuous_on {0..1} f"
      and f01:"f ` {0..1} \<subseteq> {0..1}"
      and [simp]: "f(0) = 0" "f(1) = 1"
      and q: "\<And>t. t \<in> {0..1} \<Longrightarrow> q(t) = p(f t)"
    shows "homotopic_paths s p q"
proof -
  have contp: "continuous_on {0..1} p"
    by (metis \<open>path p\<close> path_def)
  then have "continuous_on {0..1} (p \<circ> f)"
    using contf continuous_on_compose continuous_on_subset f01 by blast
  then have "path q"
    by (simp add: path_def) (metis q continuous_on_cong)
  have piqs: "path_image q \<subseteq> s"
    by (metis (no_types, hide_lams) pips f01 image_subset_iff path_image_def q)
  have fb0: "\<And>a b. \<lbrakk>0 \<le> a; a \<le> 1; 0 \<le> b; b \<le> 1\<rbrakk> \<Longrightarrow> 0 \<le> (1 - a) * f b + a * b"
    using f01 by force
  have fb1: "\<lbrakk>0 \<le> a; a \<le> 1; 0 \<le> b; b \<le> 1\<rbrakk> \<Longrightarrow> (1 - a) * f b + a * b \<le> 1" for a b
    using f01 [THEN subsetD, of "f b"] by (simp add: convex_bound_le)
  have "homotopic_paths s q p"
  proof (rule homotopic_paths_trans)
    show "homotopic_paths s q (p \<circ> f)"
      using q by (force intro: homotopic_paths_eq [OF  \<open>path q\<close> piqs])
  next
    show "homotopic_paths s (p \<circ> f) p"
      using pips [unfolded path_image_def]
      apply (simp add: homotopic_paths_def homotopic_with_def)
      apply (rule_tac x="p \<circ> (\<lambda>y. (1 - (fst y)) *\<^sub>R ((f \<circ> snd) y) + (fst y) *\<^sub>R snd y)"  in exI)
      apply (rule conjI contf continuous_intros continuous_on_subset [OF contp] | simp)+
      by (auto simp: fb0 fb1 pathstart_def pathfinish_def)
  qed
  then show ?thesis
    by (simp add: homotopic_paths_sym)
qed

lemma homotopic_paths_subset: "\<lbrakk>homotopic_paths s p q; s \<subseteq> t\<rbrakk> \<Longrightarrow> homotopic_paths t p q"
  unfolding homotopic_paths by fast


text\<open> A slightly ad-hoc but useful lemma in constructing homotopies.\<close>
lemma continuous_on_homotopic_join_lemma:
  fixes q :: "[real,real] \<Rightarrow> 'a::topological_space"
  assumes p: "continuous_on ({0..1} \<times> {0..1}) (\<lambda>y. p (fst y) (snd y))" (is "continuous_on ?A ?p")
      and q: "continuous_on ({0..1} \<times> {0..1}) (\<lambda>y. q (fst y) (snd y))" (is "continuous_on ?A ?q")
      and pf: "\<And>t. t \<in> {0..1} \<Longrightarrow> pathfinish(p t) = pathstart(q t)"
    shows "continuous_on ({0..1} \<times> {0..1}) (\<lambda>y. (p(fst y) +++ q(fst y)) (snd y))"
proof -
  have \<section>: "(\<lambda>t. p (fst t) (2 * snd t)) = ?p \<circ> (\<lambda>y. (fst y, 2 * snd y))"
          "(\<lambda>t. q (fst t) (2 * snd t - 1)) = ?q \<circ> (\<lambda>y. (fst y, 2 * snd y - 1))"
    by force+
  show ?thesis
    unfolding joinpaths_def
  proof (rule continuous_on_cases_le)
    show "continuous_on {y \<in> ?A. snd y \<le> 1/2} (\<lambda>t. p (fst t) (2 * snd t))" 
         "continuous_on {y \<in> ?A. 1/2 \<le> snd y} (\<lambda>t. q (fst t) (2 * snd t - 1))"
         "continuous_on ?A snd"
      unfolding \<section>
      by (rule continuous_intros continuous_on_subset [OF p] continuous_on_subset [OF q] | force)+
  qed (use pf in \<open>auto simp: mult.commute pathstart_def pathfinish_def\<close>)
qed

text\<open> Congruence properties of homotopy w.r.t. path-combining operations.\<close>

lemma homotopic_paths_reversepath_D:
      assumes "homotopic_paths s p q"
      shows   "homotopic_paths s (reversepath p) (reversepath q)"
  using assms
  apply (simp add: homotopic_paths_def homotopic_with_def, clarify)
  apply (rule_tac x="h \<circ> (\<lambda>x. (fst x, 1 - snd x))" in exI)
  apply (rule conjI continuous_intros)+
  apply (auto simp: reversepath_def pathstart_def pathfinish_def elim!: continuous_on_subset)
  done

proposition homotopic_paths_reversepath:
     "homotopic_paths s (reversepath p) (reversepath q) \<longleftrightarrow> homotopic_paths s p q"
  using homotopic_paths_reversepath_D by force


proposition homotopic_paths_join:
    "\<lbrakk>homotopic_paths s p p'; homotopic_paths s q q'; pathfinish p = pathstart q\<rbrakk> \<Longrightarrow> homotopic_paths s (p +++ q) (p' +++ q')"
  apply (clarsimp simp add: homotopic_paths_def homotopic_with_def)
  apply (rename_tac k1 k2)
  apply (rule_tac x="(\<lambda>y. ((k1 \<circ> Pair (fst y)) +++ (k2 \<circ> Pair (fst y))) (snd y))" in exI)
  apply (intro conjI continuous_intros continuous_on_homotopic_join_lemma; force simp: joinpaths_def pathstart_def pathfinish_def path_image_def)
  done

proposition homotopic_paths_continuous_image:
    "\<lbrakk>homotopic_paths s f g; continuous_on s h; h ` s \<subseteq> t\<rbrakk> \<Longrightarrow> homotopic_paths t (h \<circ> f) (h \<circ> g)"
  unfolding homotopic_paths_def
  by (simp add: homotopic_with_compose_continuous_map_left pathfinish_compose pathstart_compose)


subsection\<open>Group properties for homotopy of paths\<close>

text\<^marker>\<open>tag important\<close>\<open>So taking equivalence classes under homotopy would give the fundamental group\<close>

proposition homotopic_paths_rid:
  assumes "path p" "path_image p \<subseteq> s"
  shows "homotopic_paths s (p +++ linepath (pathfinish p) (pathfinish p)) p"
proof -
  have \<section>: "continuous_on {0..1} (\<lambda>t::real. if t \<le> 1/2 then 2 *\<^sub>R t else 1)"
    unfolding split_01
    by (rule continuous_on_cases continuous_intros | force simp: pathfinish_def joinpaths_def)+
  show ?thesis
    apply (rule homotopic_paths_sym)
    using assms unfolding pathfinish_def joinpaths_def
    by (intro \<section> continuous_on_cases continuous_intros homotopic_paths_reparametrize [where f = "\<lambda>t. if t \<le> 1/2 then 2 *\<^sub>R t else 1"]; force)
qed

proposition homotopic_paths_lid:
   "\<lbrakk>path p; path_image p \<subseteq> s\<rbrakk> \<Longrightarrow> homotopic_paths s (linepath (pathstart p) (pathstart p) +++ p) p"
  using homotopic_paths_rid [of "reversepath p" s]
  by (metis homotopic_paths_reversepath path_image_reversepath path_reversepath pathfinish_linepath
        pathfinish_reversepath reversepath_joinpaths reversepath_linepath)

proposition homotopic_paths_assoc:
   "\<lbrakk>path p; path_image p \<subseteq> s; path q; path_image q \<subseteq> s; path r; path_image r \<subseteq> s; pathfinish p = pathstart q;
     pathfinish q = pathstart r\<rbrakk>
    \<Longrightarrow> homotopic_paths s (p +++ (q +++ r)) ((p +++ q) +++ r)"
  apply (subst homotopic_paths_sym)
  apply (rule homotopic_paths_reparametrize
           [where f = "\<lambda>t. if  t \<le> 1/2 then inverse 2 *\<^sub>R t
                           else if  t \<le> 3 / 4 then t - (1 / 4)
                           else 2 *\<^sub>R t - 1"])
  apply (simp_all del: le_divide_eq_numeral1 add: subset_path_image_join)
  apply (rule continuous_on_cases_1 continuous_intros | auto simp: joinpaths_def)+
  done

proposition homotopic_paths_rinv:
  assumes "path p" "path_image p \<subseteq> s"
    shows "homotopic_paths s (p +++ reversepath p) (linepath (pathstart p) (pathstart p))"
proof -
  have p: "continuous_on {0..1} p" 
    using assms by (auto simp: path_def)
  let ?A = "{0..1} \<times> {0..1}"
  have "continuous_on ?A (\<lambda>x. (subpath 0 (fst x) p +++ reversepath (subpath 0 (fst x) p)) (snd x))"
    unfolding joinpaths_def subpath_def reversepath_def path_def add_0_right diff_0_right
  proof (rule continuous_on_cases_le)
    show "continuous_on {x \<in> ?A. snd x \<le> 1/2} (\<lambda>t. p (fst t * (2 * snd t)))"
         "continuous_on {x \<in> ?A. 1/2 \<le> snd x} (\<lambda>t. p (fst t * (1 - (2 * snd t - 1))))"
         "continuous_on ?A snd"
      by (intro continuous_on_compose2 [OF p] continuous_intros; auto simp add: mult_le_one)+
  qed (auto simp add: algebra_simps)
  then show ?thesis
    using assms
    apply (subst homotopic_paths_sym_eq)
    unfolding homotopic_paths_def homotopic_with_def
    apply (rule_tac x="(\<lambda>y. (subpath 0 (fst y) p +++ reversepath(subpath 0 (fst y) p)) (snd y))" in exI)
    apply (force simp: mult_le_one path_defs joinpaths_def subpath_def reversepath_def)
    done
qed

proposition homotopic_paths_linv:
  assumes "path p" "path_image p \<subseteq> s"
    shows "homotopic_paths s (reversepath p +++ p) (linepath (pathfinish p) (pathfinish p))"
  using homotopic_paths_rinv [of "reversepath p" s] assms by simp


subsection\<open>Homotopy of loops without requiring preservation of endpoints\<close>

definition\<^marker>\<open>tag important\<close> homotopic_loops :: "'a::topological_space set \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> bool"  where
 "homotopic_loops s p q \<equiv>
     homotopic_with_canon (\<lambda>r. pathfinish r = pathstart r) {0..1} s p q"

lemma homotopic_loops:
   "homotopic_loops s p q \<longleftrightarrow>
      (\<exists>h. continuous_on ({0..1::real} \<times> {0..1}) h \<and>
          image h ({0..1} \<times> {0..1}) \<subseteq> s \<and>
          (\<forall>x \<in> {0..1}. h(0,x) = p x) \<and>
          (\<forall>x \<in> {0..1}. h(1,x) = q x) \<and>
          (\<forall>t \<in> {0..1}. pathfinish(h \<circ> Pair t) = pathstart(h \<circ> Pair t)))"
  by (simp add: homotopic_loops_def pathstart_def pathfinish_def homotopic_with)

proposition homotopic_loops_imp_loop:
     "homotopic_loops s p q \<Longrightarrow> pathfinish p = pathstart p \<and> pathfinish q = pathstart q"
using homotopic_with_imp_property homotopic_loops_def by blast

proposition homotopic_loops_imp_path:
     "homotopic_loops s p q \<Longrightarrow> path p \<and> path q"
  unfolding homotopic_loops_def path_def
  using homotopic_with_imp_continuous_maps continuous_map_subtopology_eu by blast

proposition homotopic_loops_imp_subset:
     "homotopic_loops s p q \<Longrightarrow> path_image p \<subseteq> s \<and> path_image q \<subseteq> s"
  unfolding homotopic_loops_def path_image_def
  by (meson continuous_map_subtopology_eu homotopic_with_imp_continuous_maps)

proposition homotopic_loops_refl:
     "homotopic_loops s p p \<longleftrightarrow>
      path p \<and> path_image p \<subseteq> s \<and> pathfinish p = pathstart p"
  by (simp add: homotopic_loops_def path_image_def path_def)

proposition homotopic_loops_sym: "homotopic_loops s p q \<Longrightarrow> homotopic_loops s q p"
  by (simp add: homotopic_loops_def homotopic_with_sym)

proposition homotopic_loops_sym_eq: "homotopic_loops s p q \<longleftrightarrow> homotopic_loops s q p"
  by (metis homotopic_loops_sym)

proposition homotopic_loops_trans:
   "\<lbrakk>homotopic_loops s p q; homotopic_loops s q r\<rbrakk> \<Longrightarrow> homotopic_loops s p r"
  unfolding homotopic_loops_def by (blast intro: homotopic_with_trans)

proposition homotopic_loops_subset:
   "\<lbrakk>homotopic_loops s p q; s \<subseteq> t\<rbrakk> \<Longrightarrow> homotopic_loops t p q"
  by (fastforce simp add: homotopic_loops)

proposition homotopic_loops_eq:
   "\<lbrakk>path p; path_image p \<subseteq> s; pathfinish p = pathstart p; \<And>t. t \<in> {0..1} \<Longrightarrow> p(t) = q(t)\<rbrakk>
          \<Longrightarrow> homotopic_loops s p q"
  unfolding homotopic_loops_def path_image_def path_def pathstart_def pathfinish_def
  by (auto intro: homotopic_with_eq [OF homotopic_with_refl [where f = p, THEN iffD2]])

proposition homotopic_loops_continuous_image:
   "\<lbrakk>homotopic_loops s f g; continuous_on s h; h ` s \<subseteq> t\<rbrakk> \<Longrightarrow> homotopic_loops t (h \<circ> f) (h \<circ> g)"
  unfolding homotopic_loops_def
  by (simp add: homotopic_with_compose_continuous_map_left pathfinish_def pathstart_def)


subsection\<open>Relations between the two variants of homotopy\<close>

proposition homotopic_paths_imp_homotopic_loops:
    "\<lbrakk>homotopic_paths s p q; pathfinish p = pathstart p; pathfinish q = pathstart p\<rbrakk> \<Longrightarrow> homotopic_loops s p q"
  by (auto simp: homotopic_with_def homotopic_paths_def homotopic_loops_def)

proposition homotopic_loops_imp_homotopic_paths_null:
  assumes "homotopic_loops s p (linepath a a)"
    shows "homotopic_paths s p (linepath (pathstart p) (pathstart p))"
proof -
  have "path p" by (metis assms homotopic_loops_imp_path)
  have ploop: "pathfinish p = pathstart p" by (metis assms homotopic_loops_imp_loop)
  have pip: "path_image p \<subseteq> s" by (metis assms homotopic_loops_imp_subset)
  let ?A = "{0..1::real} \<times> {0..1::real}"
  obtain h where conth: "continuous_on ?A h"
             and hs: "h ` ?A \<subseteq> s"
             and [simp]: "\<And>x. x \<in> {0..1} \<Longrightarrow> h(0,x) = p x"
             and [simp]: "\<And>x. x \<in> {0..1} \<Longrightarrow> h(1,x) = a"
             and ends: "\<And>t. t \<in> {0..1} \<Longrightarrow> pathfinish (h \<circ> Pair t) = pathstart (h \<circ> Pair t)"
    using assms by (auto simp: homotopic_loops homotopic_with)
  have conth0: "path (\<lambda>u. h (u, 0))"
    unfolding path_def
  proof (rule continuous_on_compose [of _ _ h, unfolded o_def])
    show "continuous_on ((\<lambda>x. (x, 0)) ` {0..1}) h"
      by (force intro: continuous_on_subset [OF conth])
  qed (force intro: continuous_intros)
  have pih0: "path_image (\<lambda>u. h (u, 0)) \<subseteq> s"
    using hs by (force simp: path_image_def)
  have c1: "continuous_on ?A (\<lambda>x. h (fst x * snd x, 0))"
  proof (rule continuous_on_compose [of _ _ h, unfolded o_def])
    show "continuous_on ((\<lambda>x. (fst x * snd x, 0)) ` ?A) h"
      by (force simp: mult_le_one intro: continuous_on_subset [OF conth])
  qed (force intro: continuous_intros)+
  have c2: "continuous_on ?A (\<lambda>x. h (fst x - fst x * snd x, 0))"
  proof (rule continuous_on_compose [of _ _ h, unfolded o_def])
    show "continuous_on ((\<lambda>x. (fst x - fst x * snd x, 0)) ` ?A) h"
      by (auto simp: algebra_simps add_increasing2 mult_left_le intro: continuous_on_subset [OF conth])
  qed (force intro: continuous_intros)
  have [simp]: "\<And>t. \<lbrakk>0 \<le> t \<and> t \<le> 1\<rbrakk> \<Longrightarrow> h (t, 1) = h (t, 0)"
    using ends by (simp add: pathfinish_def pathstart_def)
  have adhoc_le: "c * 4 \<le> 1 + c * (d * 4)" if "\<not> d * 4 \<le> 3" "0 \<le> c" "c \<le> 1" for c d::real
  proof -
    have "c * 3 \<le> c * (d * 4)" using that less_eq_real_def by auto
    with \<open>c \<le> 1\<close> show ?thesis by fastforce
  qed
  have *: "\<And>p x. \<lbrakk>path p \<and> path(reversepath p);
                  path_image p \<subseteq> s \<and> path_image(reversepath p) \<subseteq> s;
                  pathfinish p = pathstart(linepath a a +++ reversepath p) \<and>
                   pathstart(reversepath p) = a \<and> pathstart p = x\<rbrakk>
                  \<Longrightarrow> homotopic_paths s (p +++ linepath a a +++ reversepath p) (linepath x x)"
    by (metis homotopic_paths_lid homotopic_paths_join
              homotopic_paths_trans homotopic_paths_sym homotopic_paths_rinv)
  have 1: "homotopic_paths s p (p +++ linepath (pathfinish p) (pathfinish p))"
    using \<open>path p\<close> homotopic_paths_rid homotopic_paths_sym pip by blast
  moreover have "homotopic_paths s (p +++ linepath (pathfinish p) (pathfinish p))
                                   (linepath (pathstart p) (pathstart p) +++ p +++ linepath (pathfinish p) (pathfinish p))"
    apply (rule homotopic_paths_sym)
    using homotopic_paths_lid [of "p +++ linepath (pathfinish p) (pathfinish p)" s]
    by (metis 1 homotopic_paths_imp_path homotopic_paths_imp_pathstart homotopic_paths_imp_subset)
  moreover 
  have "homotopic_paths s (linepath (pathstart p) (pathstart p) +++ p +++ linepath (pathfinish p) (pathfinish p))
                                   ((\<lambda>u. h (u, 0)) +++ linepath a a +++ reversepath (\<lambda>u. h (u, 0)))"
    unfolding homotopic_paths_def homotopic_with_def
  proof (intro exI strip conjI)
    let ?h = "\<lambda>y. (subpath 0 (fst y) (\<lambda>u. h (u, 0)) +++ (\<lambda>u. h (Pair (fst y) u)) 
               +++ subpath (fst y) 0 (\<lambda>u. h (u, 0))) (snd y)" 
    have "continuous_on ?A ?h"
      by (intro continuous_on_homotopic_join_lemma; simp add: path_defs joinpaths_def subpath_def conth c1 c2)
    moreover have "?h ` ?A \<subseteq> s"
      unfolding joinpaths_def subpath_def
      by (force simp: algebra_simps mult_le_one mult_left_le intro: hs [THEN subsetD] adhoc_le)
  ultimately show "continuous_map (prod_topology (top_of_set {0..1}) (top_of_set {0..1}))
                         (top_of_set s) ?h"
    by (simp add: subpath_reversepath)
  qed (use ploop in \<open>simp_all add: reversepath_def path_defs joinpaths_def o_def subpath_def conth c1 c2\<close>)
  moreover have "homotopic_paths s ((\<lambda>u. h (u, 0)) +++ linepath a a +++ reversepath (\<lambda>u. h (u, 0)))
                                   (linepath (pathstart p) (pathstart p))"
  proof (rule *; simp add: pih0 pathstart_def pathfinish_def conth0)
    show "a = (linepath a a +++ reversepath (\<lambda>u. h (u, 0))) 0 \<and> reversepath (\<lambda>u. h (u, 0)) 0 = a"
      by (simp_all add: reversepath_def joinpaths_def)
  qed
  ultimately show ?thesis
    by (blast intro: homotopic_paths_trans)
qed

proposition homotopic_loops_conjugate:
  fixes s :: "'a::real_normed_vector set"
  assumes "path p" "path q" and pip: "path_image p \<subseteq> s" and piq: "path_image q \<subseteq> s"
      and pq: "pathfinish p = pathstart q" and qloop: "pathfinish q = pathstart q"
    shows "homotopic_loops s (p +++ q +++ reversepath p) q"
proof -
  have contp: "continuous_on {0..1} p"  using \<open>path p\<close> [unfolded path_def] by blast
  have contq: "continuous_on {0..1} q"  using \<open>path q\<close> [unfolded path_def] by blast
  let ?A = "{0..1::real} \<times> {0..1::real}"
  have c1: "continuous_on ?A (\<lambda>x. p ((1 - fst x) * snd x + fst x))"
  proof (rule continuous_on_compose [of _ _ p, unfolded o_def])
    show "continuous_on ((\<lambda>x. (1 - fst x) * snd x + fst x) ` ?A) p"
      by (auto intro: continuous_on_subset [OF contp] simp: algebra_simps add_increasing2 mult_right_le_one_le sum_le_prod1)
  qed (force intro: continuous_intros)
  have c2: "continuous_on ?A (\<lambda>x. p ((fst x - 1) * snd x + 1))"
  proof (rule continuous_on_compose [of _ _ p, unfolded o_def])
    show "continuous_on ((\<lambda>x. (fst x - 1) * snd x + 1) ` ?A) p"
      by (auto intro: continuous_on_subset [OF contp] simp: algebra_simps add_increasing2 mult_left_le_one_le)
  qed (force intro: continuous_intros)

  have ps1: "\<And>a b. \<lbrakk>b * 2 \<le> 1; 0 \<le> b; 0 \<le> a; a \<le> 1\<rbrakk> \<Longrightarrow> p ((1 - a) * (2 * b) + a) \<in> s"
    using sum_le_prod1
    by (force simp: algebra_simps add_increasing2 mult_left_le intro: pip [unfolded path_image_def, THEN subsetD])
  have ps2: "\<And>a b. \<lbrakk>\<not> 4 * b \<le> 3; b \<le> 1; 0 \<le> a; a \<le> 1\<rbrakk> \<Longrightarrow> p ((a - 1) * (4 * b - 3) + 1) \<in> s"
    apply (rule pip [unfolded path_image_def, THEN subsetD])
    apply (rule image_eqI, blast)
    apply (simp add: algebra_simps)
    by (metis add_mono_thms_linordered_semiring(1) affine_ineq linear mult.commute mult.left_neutral mult_right_mono
              add.commute zero_le_numeral)
  have qs: "\<And>a b. \<lbrakk>4 * b \<le> 3; \<not> b * 2 \<le> 1\<rbrakk> \<Longrightarrow> q (4 * b - 2) \<in> s"
    using path_image_def piq by fastforce
  have "homotopic_loops s (p +++ q +++ reversepath p)
                          (linepath (pathstart q) (pathstart q) +++ q +++ linepath (pathstart q) (pathstart q))"
    unfolding homotopic_loops_def homotopic_with_def
  proof (intro exI strip conjI)
    let ?h = "(\<lambda>y. (subpath (fst y) 1 p +++ q +++ subpath 1 (fst y) p) (snd y))" 
    have "continuous_on ?A (\<lambda>y. q (snd y))"
      by (force simp: contq intro: continuous_on_compose [of _ _ q, unfolded o_def] continuous_on_id continuous_on_snd)
    then have "continuous_on ?A ?h"
      using pq qloop
      by (intro continuous_on_homotopic_join_lemma) (auto simp: path_defs joinpaths_def subpath_def c1 c2)
    then show "continuous_map (prod_topology (top_of_set {0..1}) (top_of_set {0..1})) (top_of_set s) ?h"
      by (auto simp: joinpaths_def subpath_def  ps1 ps2 qs)
    show "?h (1,x) = (linepath (pathstart q) (pathstart q) +++ q +++ linepath (pathstart q) (pathstart q)) x"  for x
      using pq by (simp add: pathfinish_def subpath_refl)
  qed (auto simp: subpath_reversepath)
  moreover have "homotopic_loops s (linepath (pathstart q) (pathstart q) +++ q +++ linepath (pathstart q) (pathstart q)) q"
  proof -
    have "homotopic_paths s (linepath (pathfinish q) (pathfinish q) +++ q) q"
      using \<open>path q\<close> homotopic_paths_lid qloop piq by auto
    hence 1: "\<And>f. homotopic_paths s f q \<or> \<not> homotopic_paths s f (linepath (pathfinish q) (pathfinish q) +++ q)"
      using homotopic_paths_trans by blast
    hence "homotopic_paths s (linepath (pathfinish q) (pathfinish q) +++ q +++ linepath (pathfinish q) (pathfinish q)) q"
    proof -
      have "homotopic_paths s (q +++ linepath (pathfinish q) (pathfinish q)) q"
        by (simp add: \<open>path q\<close> homotopic_paths_rid piq)
      thus ?thesis
        by (metis (no_types) 1 \<open>path q\<close> homotopic_paths_join homotopic_paths_rinv homotopic_paths_sym
                  homotopic_paths_trans qloop pathfinish_linepath piq)
    qed
    thus ?thesis
      by (metis (no_types) qloop homotopic_loops_sym homotopic_paths_imp_homotopic_loops homotopic_paths_imp_pathfinish homotopic_paths_sym)
  qed
  ultimately show ?thesis
    by (blast intro: homotopic_loops_trans)
qed

lemma homotopic_paths_loop_parts:
  assumes loops: "homotopic_loops S (p +++ reversepath q) (linepath a a)" and "path q"
  shows "homotopic_paths S p q"
proof -
  have paths: "homotopic_paths S (p +++ reversepath q) (linepath (pathstart p) (pathstart p))"
    using homotopic_loops_imp_homotopic_paths_null [OF loops] by simp
  then have "path p"
    using \<open>path q\<close> homotopic_loops_imp_path loops path_join path_join_path_ends path_reversepath by blast
  show ?thesis
  proof (cases "pathfinish p = pathfinish q")
    case True
    have pipq: "path_image p \<subseteq> S" "path_image q \<subseteq> S"
      by (metis Un_subset_iff paths \<open>path p\<close> \<open>path q\<close> homotopic_loops_imp_subset homotopic_paths_imp_path loops
           path_image_join path_image_reversepath path_imp_reversepath path_join_eq)+
    have "homotopic_paths S p (p +++ (linepath (pathfinish p) (pathfinish p)))"
      using \<open>path p\<close> \<open>path_image p \<subseteq> S\<close> homotopic_paths_rid homotopic_paths_sym by blast
    moreover have "homotopic_paths S (p +++ (linepath (pathfinish p) (pathfinish p))) (p +++ (reversepath q +++ q))"
      by (simp add: True \<open>path p\<close> \<open>path q\<close> pipq homotopic_paths_join homotopic_paths_linv homotopic_paths_sym)
    moreover have "homotopic_paths S (p +++ (reversepath q +++ q)) ((p +++ reversepath q) +++ q)"
      by (simp add: True \<open>path p\<close> \<open>path q\<close> homotopic_paths_assoc pipq)
    moreover have "homotopic_paths S ((p +++ reversepath q) +++ q) (linepath (pathstart p) (pathstart p) +++ q)"
      by (simp add: \<open>path q\<close> homotopic_paths_join paths pipq)
    moreover then have "homotopic_paths S (linepath (pathstart p) (pathstart p) +++ q) q"
      by (metis \<open>path q\<close> homotopic_paths_imp_path homotopic_paths_lid linepath_trivial path_join_path_ends pathfinish_def pipq(2))
    ultimately show ?thesis
      using homotopic_paths_trans by metis
  next
    case False
    then show ?thesis
      using \<open>path q\<close> homotopic_loops_imp_path loops path_join_path_ends by fastforce
  qed
qed


subsection\<^marker>\<open>tag unimportant\<close>\<open>Homotopy of "nearby" function, paths and loops\<close>

lemma homotopic_with_linear:
  fixes f g :: "_ \<Rightarrow> 'b::real_normed_vector"
  assumes contf: "continuous_on S f"
      and contg:"continuous_on S g"
      and sub: "\<And>x. x \<in> S \<Longrightarrow> closed_segment (f x) (g x) \<subseteq> t"
    shows "homotopic_with_canon (\<lambda>z. True) S t f g"
  unfolding homotopic_with_def
  apply (rule_tac x="\<lambda>y. ((1 - (fst y)) *\<^sub>R f(snd y) + (fst y) *\<^sub>R g(snd y))" in exI)
  using sub closed_segment_def
     by (fastforce intro: continuous_intros continuous_on_subset [OF contf] continuous_on_compose2 [where g=f]
            continuous_on_subset [OF contg] continuous_on_compose2 [where g=g])

lemma homotopic_paths_linear:
  fixes g h :: "real \<Rightarrow> 'a::real_normed_vector"
  assumes "path g" "path h" "pathstart h = pathstart g" "pathfinish h = pathfinish g"
          "\<And>t. t \<in> {0..1} \<Longrightarrow> closed_segment (g t) (h t) \<subseteq> S"
    shows "homotopic_paths S g h"
  using assms
  unfolding path_def
  apply (simp add: closed_segment_def pathstart_def pathfinish_def homotopic_paths_def homotopic_with_def)
  apply (rule_tac x="\<lambda>y. ((1 - (fst y)) *\<^sub>R (g \<circ> snd) y + (fst y) *\<^sub>R (h \<circ> snd) y)" in exI)
  apply (intro conjI subsetI continuous_intros; force)
  done

lemma homotopic_loops_linear:
  fixes g h :: "real \<Rightarrow> 'a::real_normed_vector"
  assumes "path g" "path h" "pathfinish g = pathstart g" "pathfinish h = pathstart h"
          "\<And>t x. t \<in> {0..1} \<Longrightarrow> closed_segment (g t) (h t) \<subseteq> S"
    shows "homotopic_loops S g h"
  using assms
  unfolding path_defs homotopic_loops_def homotopic_with_def
  apply (rule_tac x="\<lambda>y. ((1 - (fst y)) *\<^sub>R g(snd y) + (fst y) *\<^sub>R h(snd y))" in exI)
  by (force simp: closed_segment_def intro!: continuous_intros intro: continuous_on_compose2 [where g=g] continuous_on_compose2 [where g=h])

lemma homotopic_paths_nearby_explicit:
  assumes \<section>: "path g" "path h" "pathstart h = pathstart g" "pathfinish h = pathfinish g"
      and no: "\<And>t x. \<lbrakk>t \<in> {0..1}; x \<notin> S\<rbrakk> \<Longrightarrow> norm(h t - g t) < norm(g t - x)"
    shows "homotopic_paths S g h"
proof (rule homotopic_paths_linear [OF \<section>])
  show "\<And>t. t \<in> {0..1} \<Longrightarrow> closed_segment (g t) (h t) \<subseteq> S"
  by (metis no segment_bound(1) subsetI norm_minus_commute not_le)
qed

lemma homotopic_loops_nearby_explicit:
  assumes \<section>: "path g" "path h" "pathfinish g = pathstart g" "pathfinish h = pathstart h"
      and no: "\<And>t x. \<lbrakk>t \<in> {0..1}; x \<notin> S\<rbrakk> \<Longrightarrow> norm(h t - g t) < norm(g t - x)"
    shows "homotopic_loops S g h"
proof (rule homotopic_loops_linear [OF \<section>])
  show "\<And>t. t \<in> {0..1} \<Longrightarrow> closed_segment (g t) (h t) \<subseteq> S"
  by (metis no segment_bound(1) subsetI norm_minus_commute not_le)
qed

lemma homotopic_nearby_paths:
  fixes g h :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "path g" "open S" "path_image g \<subseteq> S"
    shows "\<exists>e. 0 < e \<and>
               (\<forall>h. path h \<and>
                    pathstart h = pathstart g \<and> pathfinish h = pathfinish g \<and>
                    (\<forall>t \<in> {0..1}. norm(h t - g t) < e) \<longrightarrow> homotopic_paths S g h)"
proof -
  obtain e where "e > 0" and e: "\<And>x y. x \<in> path_image g \<Longrightarrow> y \<in> - S \<Longrightarrow> e \<le> dist x y"
    using separate_compact_closed [of "path_image g" "-S"] assms by force
  show ?thesis
    using e [unfolded dist_norm] \<open>e > 0\<close>
    by (fastforce simp: path_image_def intro!: homotopic_paths_nearby_explicit assms exI)
qed

lemma homotopic_nearby_loops:
  fixes g h :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "path g" "open S" "path_image g \<subseteq> S" "pathfinish g = pathstart g"
    shows "\<exists>e. 0 < e \<and>
               (\<forall>h. path h \<and> pathfinish h = pathstart h \<and>
                    (\<forall>t \<in> {0..1}. norm(h t - g t) < e) \<longrightarrow> homotopic_loops S g h)"
proof -
  obtain e where "e > 0" and e: "\<And>x y. x \<in> path_image g \<Longrightarrow> y \<in> - S \<Longrightarrow> e \<le> dist x y"
    using separate_compact_closed [of "path_image g" "-S"] assms by force
  show ?thesis
    using e [unfolded dist_norm] \<open>e > 0\<close>
    by (fastforce simp: path_image_def intro!: homotopic_loops_nearby_explicit assms exI)
qed


subsection\<open> Homotopy and subpaths\<close>

lemma homotopic_join_subpaths1:
  assumes "path g" and pag: "path_image g \<subseteq> s"
      and u: "u \<in> {0..1}" and v: "v \<in> {0..1}" and w: "w \<in> {0..1}" "u \<le> v" "v \<le> w"
    shows "homotopic_paths s (subpath u v g +++ subpath v w g) (subpath u w g)"
proof -
  have 1: "t * 2 \<le> 1 \<Longrightarrow> u + t * (v * 2) \<le> v + t * (u * 2)" for t
    using affine_ineq \<open>u \<le> v\<close> by fastforce
  have 2: "t * 2 > 1 \<Longrightarrow> u + (2*t - 1) * v \<le> v + (2*t - 1) * w" for t
    by (metis add_mono_thms_linordered_semiring(1) diff_gt_0_iff_gt less_eq_real_def mult.commute mult_right_mono \<open>u \<le> v\<close> \<open>v \<le> w\<close>)
  have t2: "\<And>t::real. t*2 = 1 \<Longrightarrow> t = 1/2" by auto
  have "homotopic_paths (path_image g) (subpath u v g +++ subpath v w g) (subpath u w g)"
  proof (cases "w = u")
    case True
    then show ?thesis
      by (metis \<open>path g\<close> homotopic_paths_rinv path_image_subpath_subset path_subpath pathstart_subpath reversepath_subpath subpath_refl u v)
  next
    case False
    let ?f = "\<lambda>t. if  t \<le> 1/2 then inverse((w - u)) *\<^sub>R (2 * (v - u)) *\<^sub>R t
                               else inverse((w - u)) *\<^sub>R ((v - u) + (w - v) *\<^sub>R (2 *\<^sub>R t - 1))"
    show ?thesis
    proof (rule homotopic_paths_sym [OF homotopic_paths_reparametrize [where f = ?f]])
      show "path (subpath u w g)"
        using assms(1) path_subpath u w(1) by blast
      show "path_image (subpath u w g) \<subseteq> path_image g"
        by (meson path_image_subpath_subset u w(1))
      show "continuous_on {0..1} ?f"
        unfolding split_01
        by (rule continuous_on_cases continuous_intros | force simp: pathfinish_def joinpaths_def dest!: t2)+
      show "?f ` {0..1} \<subseteq> {0..1}"
        using False assms
        by (force simp: field_simps not_le mult_left_mono affine_ineq dest!: 1 2)
      show "(subpath u v g +++ subpath v w g) t = subpath u w g (?f t)" if "t \<in> {0..1}" for t 
        using assms
        unfolding joinpaths_def subpath_def by (auto simp add: divide_simps add.commute mult.commute mult.left_commute)
    qed (use False in auto)
  qed
  then show ?thesis
    by (rule homotopic_paths_subset [OF _ pag])
qed

lemma homotopic_join_subpaths2:
  assumes "homotopic_paths s (subpath u v g +++ subpath v w g) (subpath u w g)"
    shows "homotopic_paths s (subpath w v g +++ subpath v u g) (subpath w u g)"
by (metis assms homotopic_paths_reversepath_D pathfinish_subpath pathstart_subpath reversepath_joinpaths reversepath_subpath)

lemma homotopic_join_subpaths3:
  assumes hom: "homotopic_paths s (subpath u v g +++ subpath v w g) (subpath u w g)"
      and "path g" and pag: "path_image g \<subseteq> s"
      and u: "u \<in> {0..1}" and v: "v \<in> {0..1}" and w: "w \<in> {0..1}"
    shows "homotopic_paths s (subpath v w g +++ subpath w u g) (subpath v u g)"
proof -
  have "homotopic_paths s (subpath u w g +++ subpath w v g) ((subpath u v g +++ subpath v w g) +++ subpath w v g)"
  proof (rule homotopic_paths_join)
    show "homotopic_paths s (subpath u w g) (subpath u v g +++ subpath v w g)"
      using hom homotopic_paths_sym_eq by blast
    show "homotopic_paths s (subpath w v g) (subpath w v g)"
      by (metis \<open>path g\<close> homotopic_paths_eq pag path_image_subpath_subset path_subpath subset_trans v w)
  qed auto
  also have "homotopic_paths s ((subpath u v g +++ subpath v w g) +++ subpath w v g) (subpath u v g +++ subpath v w g +++ subpath w v g)"
    by (rule homotopic_paths_sym [OF homotopic_paths_assoc])
       (use assms in \<open>simp_all add: path_image_subpath_subset [THEN order_trans]\<close>)
  also have "homotopic_paths s (subpath u v g +++ subpath v w g +++ subpath w v g)
                               (subpath u v g +++ linepath (pathfinish (subpath u v g)) (pathfinish (subpath u v g)))"
  proof (rule homotopic_paths_join; simp)
    show "path (subpath u v g) \<and> path_image (subpath u v g) \<subseteq> s"
      by (metis \<open>path g\<close> order.trans pag path_image_subpath_subset path_subpath u v)
    show "homotopic_paths s (subpath v w g +++ subpath w v g) (linepath (g v) (g v))"
      by (metis (no_types, lifting) \<open>path g\<close> homotopic_paths_linv order_trans pag path_image_subpath_subset path_subpath pathfinish_subpath reversepath_subpath v w)
  qed 
  also have "homotopic_paths s (subpath u v g +++ linepath (pathfinish (subpath u v g)) (pathfinish (subpath u v g))) (subpath u v g)"
  proof (rule homotopic_paths_rid)
    show "path (subpath u v g)"
      using \<open>path g\<close> path_subpath u v by blast
    show "path_image (subpath u v g) \<subseteq> s"
      by (meson \<open>path g\<close> order.trans pag path_image_subpath_subset u v)
  qed
  finally have "homotopic_paths s (subpath u w g +++ subpath w v g) (subpath u v g)" .
  then show ?thesis
    using homotopic_join_subpaths2 by blast
qed

proposition homotopic_join_subpaths:
   "\<lbrakk>path g; path_image g \<subseteq> s; u \<in> {0..1}; v \<in> {0..1}; w \<in> {0..1}\<rbrakk>
    \<Longrightarrow> homotopic_paths s (subpath u v g +++ subpath v w g) (subpath u w g)"
  using le_cases3 [of u v w] homotopic_join_subpaths1 homotopic_join_subpaths2 homotopic_join_subpaths3 
  by metis

text\<open>Relating homotopy of trivial loops to path-connectedness.\<close>

lemma path_component_imp_homotopic_points:
  assumes "path_component S a b"
  shows "homotopic_loops S (linepath a a) (linepath b b)"
proof -
  obtain g :: "real \<Rightarrow> 'a" where g: "continuous_on {0..1} g" "g ` {0..1} \<subseteq> S" "g 0 = a" "g 1 = b"
    using assms by (auto simp: path_defs)
  then have "continuous_on ({0..1} \<times> {0..1}) (g \<circ> fst)"
    by (fastforce intro!: continuous_intros)+
  with g show ?thesis
    by (auto simp add: homotopic_loops_def homotopic_with_def path_defs image_subset_iff)
qed

lemma homotopic_loops_imp_path_component_value:
   "\<lbrakk>homotopic_loops S p q; 0 \<le> t; t \<le> 1\<rbrakk>
        \<Longrightarrow> path_component S (p t) (q t)"
apply (clarsimp simp add: homotopic_loops_def homotopic_with_def path_defs)
apply (rule_tac x="h \<circ> (\<lambda>u. (u, t))" in exI)
apply (fastforce elim!: continuous_on_subset intro!: continuous_intros)
done

lemma homotopic_points_eq_path_component:
   "homotopic_loops S (linepath a a) (linepath b b) \<longleftrightarrow> path_component S a b"
by (auto simp: path_component_imp_homotopic_points
         dest: homotopic_loops_imp_path_component_value [where t=1])

lemma path_connected_eq_homotopic_points:
    "path_connected S \<longleftrightarrow>
      (\<forall>a b. a \<in> S \<and> b \<in> S \<longrightarrow> homotopic_loops S (linepath a a) (linepath b b))"
by (auto simp: path_connected_def path_component_def homotopic_points_eq_path_component)


subsection\<open>Simply connected sets\<close>

text\<^marker>\<open>tag important\<close>\<open>defined as "all loops are homotopic (as loops)\<close>

definition\<^marker>\<open>tag important\<close> simply_connected where
  "simply_connected S \<equiv>
        \<forall>p q. path p \<and> pathfinish p = pathstart p \<and> path_image p \<subseteq> S \<and>
              path q \<and> pathfinish q = pathstart q \<and> path_image q \<subseteq> S
              \<longrightarrow> homotopic_loops S p q"

lemma simply_connected_empty [iff]: "simply_connected {}"
  by (simp add: simply_connected_def)

lemma simply_connected_imp_path_connected:
  fixes S :: "_::real_normed_vector set"
  shows "simply_connected S \<Longrightarrow> path_connected S"
by (simp add: simply_connected_def path_connected_eq_homotopic_points)

lemma simply_connected_imp_connected:
  fixes S :: "_::real_normed_vector set"
  shows "simply_connected S \<Longrightarrow> connected S"
by (simp add: path_connected_imp_connected simply_connected_imp_path_connected)

lemma simply_connected_eq_contractible_loop_any:
  fixes S :: "_::real_normed_vector set"
  shows "simply_connected S \<longleftrightarrow>
            (\<forall>p a. path p \<and> path_image p \<subseteq> S \<and> pathfinish p = pathstart p \<and> a \<in> S
                  \<longrightarrow> homotopic_loops S p (linepath a a))"
        (is "?lhs = ?rhs")
proof
  assume ?lhs then show ?rhs
    unfolding simply_connected_def by force
next
  assume ?rhs then show ?lhs
    unfolding simply_connected_def
    by (metis pathfinish_in_path_image subsetD  homotopic_loops_trans homotopic_loops_sym)
qed

lemma simply_connected_eq_contractible_loop_some:
  fixes S :: "_::real_normed_vector set"
  shows "simply_connected S \<longleftrightarrow>
                path_connected S \<and>
                (\<forall>p. path p \<and> path_image p \<subseteq> S \<and> pathfinish p = pathstart p
                    \<longrightarrow> (\<exists>a. a \<in> S \<and> homotopic_loops S p (linepath a a)))"
     (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
  using simply_connected_eq_contractible_loop_any by (blast intro: simply_connected_imp_path_connected)
next
  assume r: ?rhs
  note pa = r [THEN conjunct2, rule_format]
  show ?lhs
  proof (clarsimp simp add: simply_connected_eq_contractible_loop_any)
    fix p a
    assume "path p" and "path_image p \<subseteq> S" "pathfinish p = pathstart p"
      and "a \<in> S"
    with pa [of p] show "homotopic_loops S p (linepath a a)"
      using homotopic_loops_trans path_connected_eq_homotopic_points r by blast
  qed
qed

lemma simply_connected_eq_contractible_loop_all:
  fixes S :: "_::real_normed_vector set"
  shows "simply_connected S \<longleftrightarrow>
         S = {} \<or>
         (\<exists>a \<in> S. \<forall>p. path p \<and> path_image p \<subseteq> S \<and> pathfinish p = pathstart p
                \<longrightarrow> homotopic_loops S p (linepath a a))"
        (is "?lhs = ?rhs")
proof (cases "S = {}")
  case True then show ?thesis by force
next
  case False
  then obtain a where "a \<in> S" by blast
  show ?thesis
  proof
    assume "simply_connected S"
    then show ?rhs
      using \<open>a \<in> S\<close> \<open>simply_connected S\<close> simply_connected_eq_contractible_loop_any
      by blast
  next
    assume ?rhs
    then show "simply_connected S"
      unfolding simply_connected_eq_contractible_loop_any 
      by (meson False homotopic_loops_refl homotopic_loops_sym homotopic_loops_trans 
          path_component_imp_homotopic_points path_component_refl)
  qed
qed

lemma simply_connected_eq_contractible_path:
  fixes S :: "_::real_normed_vector set"
  shows "simply_connected S \<longleftrightarrow>
           path_connected S \<and>
           (\<forall>p. path p \<and> path_image p \<subseteq> S \<and> pathfinish p = pathstart p
            \<longrightarrow> homotopic_paths S p (linepath (pathstart p) (pathstart p)))"
     (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    unfolding simply_connected_imp_path_connected
    by (metis simply_connected_eq_contractible_loop_some homotopic_loops_imp_homotopic_paths_null)
next
  assume  ?rhs
  then show ?lhs
    using homotopic_paths_imp_homotopic_loops simply_connected_eq_contractible_loop_some by fastforce
qed

lemma simply_connected_eq_homotopic_paths:
  fixes S :: "_::real_normed_vector set"
  shows "simply_connected S \<longleftrightarrow>
          path_connected S \<and>
          (\<forall>p q. path p \<and> path_image p \<subseteq> S \<and>
                path q \<and> path_image q \<subseteq> S \<and>
                pathstart q = pathstart p \<and> pathfinish q = pathfinish p
                \<longrightarrow> homotopic_paths S p q)"
         (is "?lhs = ?rhs")
proof
  assume ?lhs
  then have pc: "path_connected S"
        and *:  "\<And>p. \<lbrakk>path p; path_image p \<subseteq> S;
                       pathfinish p = pathstart p\<rbrakk>
                      \<Longrightarrow> homotopic_paths S p (linepath (pathstart p) (pathstart p))"
    by (auto simp: simply_connected_eq_contractible_path)
  have "homotopic_paths S p q"
        if "path p" "path_image p \<subseteq> S" "path q"
           "path_image q \<subseteq> S" "pathstart q = pathstart p"
           "pathfinish q = pathfinish p" for p q
  proof -
    have "homotopic_paths S p (p +++ linepath (pathfinish p) (pathfinish p))"
      by (simp add: homotopic_paths_rid homotopic_paths_sym that)
    also have "homotopic_paths S (p +++ linepath (pathfinish p) (pathfinish p))
                                 (p +++ reversepath q +++ q)"
      using that
      by (metis homotopic_paths_join homotopic_paths_linv homotopic_paths_refl homotopic_paths_sym_eq pathstart_linepath)
    also have "homotopic_paths S (p +++ reversepath q +++ q)
                                 ((p +++ reversepath q) +++ q)"
      by (simp add: that homotopic_paths_assoc)
    also have "homotopic_paths S ((p +++ reversepath q) +++ q)
                                 (linepath (pathstart q) (pathstart q) +++ q)"
      using * [of "p +++ reversepath q"] that
      by (simp add: homotopic_paths_join path_image_join)
    also have "homotopic_paths S (linepath (pathstart q) (pathstart q) +++ q) q"
      using that homotopic_paths_lid by blast
    finally show ?thesis .
  qed
  then show ?rhs
    by (blast intro: pc *)
next
  assume ?rhs
  then show ?lhs
    by (force simp: simply_connected_eq_contractible_path)
qed

proposition simply_connected_Times:
  fixes S :: "'a::real_normed_vector set" and T :: "'b::real_normed_vector set"
  assumes S: "simply_connected S" and T: "simply_connected T"
    shows "simply_connected(S \<times> T)"
proof -
  have "homotopic_loops (S \<times> T) p (linepath (a, b) (a, b))"
       if "path p" "path_image p \<subseteq> S \<times> T" "p 1 = p 0" "a \<in> S" "b \<in> T"
       for p a b
  proof -
    have "path (fst \<circ> p)"
      by (simp add: continuous_on_fst Path_Connected.path_continuous_image [OF \<open>path p\<close>])
    moreover have "path_image (fst \<circ> p) \<subseteq> S"
      using that by (force simp add: path_image_def)
    ultimately have p1: "homotopic_loops S (fst \<circ> p) (linepath a a)"
      using S that
      by (simp add: simply_connected_eq_contractible_loop_any pathfinish_def pathstart_def)
    have "path (snd \<circ> p)"
      by (simp add: continuous_on_snd Path_Connected.path_continuous_image [OF \<open>path p\<close>])
    moreover have "path_image (snd \<circ> p) \<subseteq> T"
      using that by (force simp: path_image_def)
    ultimately have p2: "homotopic_loops T (snd \<circ> p) (linepath b b)"
      using T that
      by (simp add: simply_connected_eq_contractible_loop_any pathfinish_def pathstart_def)
    show ?thesis
      using p1 p2 unfolding homotopic_loops
      apply clarify
      subgoal for h k
        by (rule_tac x="\<lambda>z. (h z, k z)" in exI) (force intro: continuous_intros simp: path_defs)
      done
  qed
  with assms show ?thesis
    by (simp add: simply_connected_eq_contractible_loop_any pathfinish_def pathstart_def)
qed


subsection\<open>Contractible sets\<close>

definition\<^marker>\<open>tag important\<close> contractible where
 "contractible S \<equiv> \<exists>a. homotopic_with_canon (\<lambda>x. True) S S id (\<lambda>x. a)"

proposition contractible_imp_simply_connected:
  fixes S :: "_::real_normed_vector set"
  assumes "contractible S" shows "simply_connected S"
proof (cases "S = {}")
  case True then show ?thesis by force
next
  case False
  obtain a where a: "homotopic_with_canon (\<lambda>x. True) S S id (\<lambda>x. a)"
    using assms by (force simp: contractible_def)
  then have "a \<in> S"
    by (metis False homotopic_constant_maps homotopic_with_symD homotopic_with_trans path_component_in_topspace topspace_euclidean_subtopology)
  have "\<forall>p. path p \<and>
            path_image p \<subseteq> S \<and> pathfinish p = pathstart p \<longrightarrow>
            homotopic_loops S p (linepath a a)"
    using a apply (clarsimp simp add: homotopic_loops_def homotopic_with_def path_defs)
    apply (rule_tac x="(h \<circ> (\<lambda>y. (fst y, (p \<circ> snd) y)))" in exI)
    apply (intro conjI continuous_on_compose continuous_intros; force elim: continuous_on_subset)
    done
  with \<open>a \<in> S\<close> show ?thesis
    by (auto simp add: simply_connected_eq_contractible_loop_all False)
qed

corollary contractible_imp_connected:
  fixes S :: "_::real_normed_vector set"
  shows "contractible S \<Longrightarrow> connected S"
by (simp add: contractible_imp_simply_connected simply_connected_imp_connected)

lemma contractible_imp_path_connected:
  fixes S :: "_::real_normed_vector set"
  shows "contractible S \<Longrightarrow> path_connected S"
by (simp add: contractible_imp_simply_connected simply_connected_imp_path_connected)

lemma nullhomotopic_through_contractible:
  fixes S :: "_::topological_space set"
  assumes f: "continuous_on S f" "f ` S \<subseteq> T"
      and g: "continuous_on T g" "g ` T \<subseteq> U"
      and T: "contractible T"
    obtains c where "homotopic_with_canon (\<lambda>h. True) S U (g \<circ> f) (\<lambda>x. c)"
proof -
  obtain b where b: "homotopic_with_canon (\<lambda>x. True) T T id (\<lambda>x. b)"
    using assms by (force simp: contractible_def)
  have "homotopic_with_canon (\<lambda>f. True) T U (g \<circ> id) (g \<circ> (\<lambda>x. b))"
    by (metis Abstract_Topology.continuous_map_subtopology_eu b g homotopic_with_compose_continuous_map_left)
  then have "homotopic_with_canon (\<lambda>f. True) S U (g \<circ> id \<circ> f) (g \<circ> (\<lambda>x. b) \<circ> f)"
    by (simp add: f homotopic_with_compose_continuous_map_right)
  then show ?thesis
    by (simp add: comp_def that)
qed

lemma nullhomotopic_into_contractible:
  assumes f: "continuous_on S f" "f ` S \<subseteq> T"
      and T: "contractible T"
    obtains c where "homotopic_with_canon (\<lambda>h. True) S T f (\<lambda>x. c)"
  by (rule nullhomotopic_through_contractible [OF f, of id T]) (use assms in auto)

lemma nullhomotopic_from_contractible:
  assumes f: "continuous_on S f" "f ` S \<subseteq> T"
      and S: "contractible S"
    obtains c where "homotopic_with_canon (\<lambda>h. True) S T f (\<lambda>x. c)"
  by (auto simp: comp_def intro: nullhomotopic_through_contractible [OF continuous_on_id _ f S])

lemma homotopic_through_contractible:
  fixes S :: "_::real_normed_vector set"
  assumes "continuous_on S f1" "f1 ` S \<subseteq> T"
          "continuous_on T g1" "g1 ` T \<subseteq> U"
          "continuous_on S f2" "f2 ` S \<subseteq> T"
          "continuous_on T g2" "g2 ` T \<subseteq> U"
          "contractible T" "path_connected U"
   shows "homotopic_with_canon (\<lambda>h. True) S U (g1 \<circ> f1) (g2 \<circ> f2)"
proof -
  obtain c1 where c1: "homotopic_with_canon (\<lambda>h. True) S U (g1 \<circ> f1) (\<lambda>x. c1)"
    by (rule nullhomotopic_through_contractible [of S f1 T g1 U]) (use assms in auto)
  obtain c2 where c2: "homotopic_with_canon (\<lambda>h. True) S U (g2 \<circ> f2) (\<lambda>x. c2)"
    by (rule nullhomotopic_through_contractible [of S f2 T g2 U]) (use assms in auto)
  have "S = {} \<or> (\<exists>t. path_connected t \<and> t \<subseteq> U \<and> c2 \<in> t \<and> c1 \<in> t)"
  proof (cases "S = {}")
    case True then show ?thesis by force
  next
    case False
    with c1 c2 have "c1 \<in> U" "c2 \<in> U"
      using homotopic_with_imp_continuous_maps by fastforce+
    with \<open>path_connected U\<close> show ?thesis by blast
  qed
  then have "homotopic_with_canon (\<lambda>h. True) S U (\<lambda>x. c2) (\<lambda>x. c1)"
    by (simp add: path_component homotopic_constant_maps)
  then show ?thesis
    using c1 c2 homotopic_with_symD homotopic_with_trans by blast
qed

lemma homotopic_into_contractible:
  fixes S :: "'a::real_normed_vector set" and T:: "'b::real_normed_vector set"
  assumes f: "continuous_on S f" "f ` S \<subseteq> T"
      and g: "continuous_on S g" "g ` S \<subseteq> T"
      and T: "contractible T"
    shows "homotopic_with_canon (\<lambda>h. True) S T f g"
using homotopic_through_contractible [of S f T id T g id]
by (simp add: assms contractible_imp_path_connected)

lemma homotopic_from_contractible:
  fixes S :: "'a::real_normed_vector set" and T:: "'b::real_normed_vector set"
  assumes f: "continuous_on S f" "f ` S \<subseteq> T"
      and g: "continuous_on S g" "g ` S \<subseteq> T"
      and "contractible S" "path_connected T"
    shows "homotopic_with_canon (\<lambda>h. True) S T f g"
using homotopic_through_contractible [of S id S f T id g]
by (simp add: assms contractible_imp_path_connected)

subsection\<open>Starlike sets\<close>

definition\<^marker>\<open>tag important\<close> "starlike S \<longleftrightarrow> (\<exists>a\<in>S. \<forall>x\<in>S. closed_segment a x \<subseteq> S)"

lemma starlike_UNIV [simp]: "starlike UNIV"
  by (simp add: starlike_def)

lemma convex_imp_starlike:
  "convex S \<Longrightarrow> S \<noteq> {} \<Longrightarrow> starlike S"
  unfolding convex_contains_segment starlike_def by auto

lemma starlike_convex_tweak_boundary_points:
  fixes S :: "'a::euclidean_space set"
  assumes "convex S" "S \<noteq> {}" and ST: "rel_interior S \<subseteq> T" and TS: "T \<subseteq> closure S"
  shows "starlike T"
proof -
  have "rel_interior S \<noteq> {}"
    by (simp add: assms rel_interior_eq_empty)
  then obtain a where a: "a \<in> rel_interior S"  by blast
  with ST have "a \<in> T"  by blast
  have "\<And>x. x \<in> T \<Longrightarrow> open_segment a x \<subseteq> rel_interior S"
    by (rule rel_interior_closure_convex_segment [OF \<open>convex S\<close> a]) (use assms in auto)
  then have "\<forall>x\<in>T. a \<in> T \<and> open_segment a x \<subseteq> T"
    using ST by (blast intro: a \<open>a \<in> T\<close> rel_interior_closure_convex_segment [OF \<open>convex S\<close> a])
  then show ?thesis
    unfolding starlike_def using bexI [OF _ \<open>a \<in> T\<close>]
    by (simp add: closed_segment_eq_open)
qed

lemma starlike_imp_contractible_gen:
  fixes S :: "'a::real_normed_vector set"
  assumes S: "starlike S"
      and P: "\<And>a T. \<lbrakk>a \<in> S; 0 \<le> T; T \<le> 1\<rbrakk> \<Longrightarrow> P(\<lambda>x. (1 - T) *\<^sub>R x + T *\<^sub>R a)"
    obtains a where "homotopic_with_canon P S S (\<lambda>x. x) (\<lambda>x. a)"
proof -
  obtain a where "a \<in> S" and a: "\<And>x. x \<in> S \<Longrightarrow> closed_segment a x \<subseteq> S"
    using S by (auto simp: starlike_def)
  have "\<And>t b. 0 \<le> t \<and> t \<le> 1 \<Longrightarrow>
              \<exists>u. (1 - t) *\<^sub>R b + t *\<^sub>R a = (1 - u) *\<^sub>R a + u *\<^sub>R b \<and> 0 \<le> u \<and> u \<le> 1"
    by (metis add_diff_cancel_right' diff_ge_0_iff_ge le_add_diff_inverse pth_c(1))
  then have "(\<lambda>y. (1 - fst y) *\<^sub>R snd y + fst y *\<^sub>R a) ` ({0..1} \<times> S) \<subseteq> S"
    using a [unfolded closed_segment_def] by force
  then have "homotopic_with_canon P S S (\<lambda>x. x) (\<lambda>x. a)"
    using \<open>a \<in> S\<close>
    unfolding homotopic_with_def
    apply (rule_tac x="\<lambda>y. (1 - (fst y)) *\<^sub>R snd y + (fst y) *\<^sub>R a" in exI)
    apply (force simp add: P intro: continuous_intros)
    done
  then show ?thesis
    using that by blast
qed

lemma starlike_imp_contractible:
  fixes S :: "'a::real_normed_vector set"
  shows "starlike S \<Longrightarrow> contractible S"
using starlike_imp_contractible_gen contractible_def by (fastforce simp: id_def)

lemma contractible_UNIV [simp]: "contractible (UNIV :: 'a::real_normed_vector set)"
  by (simp add: starlike_imp_contractible)

lemma starlike_imp_simply_connected:
  fixes S :: "'a::real_normed_vector set"
  shows "starlike S \<Longrightarrow> simply_connected S"
by (simp add: contractible_imp_simply_connected starlike_imp_contractible)

lemma convex_imp_simply_connected:
  fixes S :: "'a::real_normed_vector set"
  shows "convex S \<Longrightarrow> simply_connected S"
using convex_imp_starlike starlike_imp_simply_connected by blast

lemma starlike_imp_path_connected:
  fixes S :: "'a::real_normed_vector set"
  shows "starlike S \<Longrightarrow> path_connected S"
by (simp add: simply_connected_imp_path_connected starlike_imp_simply_connected)

lemma starlike_imp_connected:
  fixes S :: "'a::real_normed_vector set"
  shows "starlike S \<Longrightarrow> connected S"
by (simp add: path_connected_imp_connected starlike_imp_path_connected)

lemma is_interval_simply_connected_1:
  fixes S :: "real set"
  shows "is_interval S \<longleftrightarrow> simply_connected S"
using convex_imp_simply_connected is_interval_convex_1 is_interval_path_connected_1 simply_connected_imp_path_connected by auto

lemma contractible_empty [simp]: "contractible {}"
  by (simp add: contractible_def homotopic_on_emptyI)

lemma contractible_convex_tweak_boundary_points:
  fixes S :: "'a::euclidean_space set"
  assumes "convex S" and TS: "rel_interior S \<subseteq> T" "T \<subseteq> closure S"
  shows "contractible T"
proof (cases "S = {}")
  case True
  with assms show ?thesis
    by (simp add: subsetCE)
next
  case False
  show ?thesis
    by (meson False assms starlike_convex_tweak_boundary_points starlike_imp_contractible)
qed

lemma convex_imp_contractible:
  fixes S :: "'a::real_normed_vector set"
  shows "convex S \<Longrightarrow> contractible S"
  using contractible_empty convex_imp_starlike starlike_imp_contractible by blast

lemma contractible_sing [simp]:
  fixes a :: "'a::real_normed_vector"
  shows "contractible {a}"
by (rule convex_imp_contractible [OF convex_singleton])

lemma is_interval_contractible_1:
  fixes S :: "real set"
  shows  "is_interval S \<longleftrightarrow> contractible S"
using contractible_imp_simply_connected convex_imp_contractible is_interval_convex_1
      is_interval_simply_connected_1 by auto

lemma contractible_Times:
  fixes S :: "'a::euclidean_space set" and T :: "'b::euclidean_space set"
  assumes S: "contractible S" and T: "contractible T"
  shows "contractible (S \<times> T)"
proof -
  obtain a h where conth: "continuous_on ({0..1} \<times> S) h"
             and hsub: "h ` ({0..1} \<times> S) \<subseteq> S"
             and [simp]: "\<And>x. x \<in> S \<Longrightarrow> h (0, x) = x"
             and [simp]: "\<And>x. x \<in> S \<Longrightarrow>  h (1::real, x) = a"
    using S by (auto simp: contractible_def homotopic_with)
  obtain b k where contk: "continuous_on ({0..1} \<times> T) k"
             and ksub: "k ` ({0..1} \<times> T) \<subseteq> T"
             and [simp]: "\<And>x. x \<in> T \<Longrightarrow> k (0, x) = x"
             and [simp]: "\<And>x. x \<in> T \<Longrightarrow>  k (1::real, x) = b"
    using T by (auto simp: contractible_def homotopic_with)
  show ?thesis
    apply (simp add: contractible_def homotopic_with)
    apply (rule exI [where x=a])
    apply (rule exI [where x=b])
    apply (rule exI [where x = "\<lambda>z. (h (fst z, fst(snd z)), k (fst z, snd(snd z)))"])
    using hsub ksub
    apply (fastforce intro!: continuous_intros continuous_on_compose2 [OF conth] continuous_on_compose2 [OF contk])
    done
qed


subsection\<open>Local versions of topological properties in general\<close>

definition\<^marker>\<open>tag important\<close> locally :: "('a::topological_space set \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool"
where
 "locally P S \<equiv>
        \<forall>w x. openin (top_of_set S) w \<and> x \<in> w
              \<longrightarrow> (\<exists>u v. openin (top_of_set S) u \<and> P v \<and> x \<in> u \<and> u \<subseteq> v \<and> v \<subseteq> w)"

lemma locallyI:
  assumes "\<And>w x. \<lbrakk>openin (top_of_set S) w; x \<in> w\<rbrakk>
                  \<Longrightarrow> \<exists>u v. openin (top_of_set S) u \<and> P v \<and> x \<in> u \<and> u \<subseteq> v \<and> v \<subseteq> w"
    shows "locally P S"
using assms by (force simp: locally_def)

lemma locallyE:
  assumes "locally P S" "openin (top_of_set S) w" "x \<in> w"
  obtains u v where "openin (top_of_set S) u"
                    "P v" "x \<in> u" "u \<subseteq> v" "v \<subseteq> w"
  using assms unfolding locally_def by meson

lemma locally_mono:
  assumes "locally P S" "\<And>T. P T \<Longrightarrow> Q T"
    shows "locally Q S"
by (metis assms locally_def)

lemma locally_open_subset:
  assumes "locally P S" "openin (top_of_set S) t"
    shows "locally P t"
  using assms
  unfolding locally_def
  by (elim all_forward) (meson dual_order.trans openin_imp_subset openin_subset_trans openin_trans)

lemma locally_diff_closed:
    "\<lbrakk>locally P S; closedin (top_of_set S) t\<rbrakk> \<Longrightarrow> locally P (S - t)"
  using locally_open_subset closedin_def by fastforce

lemma locally_empty [iff]: "locally P {}"
  by (simp add: locally_def openin_subtopology)

lemma locally_singleton [iff]:
  fixes a :: "'a::metric_space"
  shows "locally P {a} \<longleftrightarrow> P {a}"
proof -
  have "\<forall>x::real. \<not> 0 < x \<Longrightarrow> P {a}"
    using zero_less_one by blast
  then show ?thesis
    unfolding locally_def
    by (auto simp add: openin_euclidean_subtopology_iff subset_singleton_iff conj_disj_distribR)
qed

lemma locally_iff:
    "locally P S \<longleftrightarrow>
     (\<forall>T x. open T \<and> x \<in> S \<inter> T \<longrightarrow> (\<exists>U. open U \<and> (\<exists>V. P V \<and> x \<in> S \<inter> U \<and> S \<inter> U \<subseteq> V \<and> V \<subseteq> S \<inter> T)))"
  apply (simp add: le_inf_iff locally_def openin_open, safe)
   apply (metis IntE IntI le_inf_iff)
  apply (metis IntI Int_subset_iff)
  done

lemma locally_Int:
  assumes S: "locally P S" and T: "locally P T"
      and P: "\<And>S T. P S \<and> P T \<Longrightarrow> P(S \<inter> T)"
  shows "locally P (S \<inter> T)"
  unfolding locally_iff
proof clarify
  fix A x
  assume "open A" "x \<in> A" "x \<in> S" "x \<in> T"
  then obtain U1 V1 U2 V2 
    where "open U1" "P V1" "x \<in> S \<inter> U1" "S \<inter> U1 \<subseteq> V1 \<and> V1 \<subseteq> S \<inter> A" 
          "open U2" "P V2" "x \<in> T \<inter> U2" "T \<inter> U2 \<subseteq> V2 \<and> V2 \<subseteq> T \<inter> A"
    using S T unfolding locally_iff by (meson IntI)
  then have "S \<inter> T \<inter> (U1 \<inter> U2) \<subseteq> V1 \<inter> V2" "V1 \<inter> V2 \<subseteq> S \<inter> T \<inter> A" "x \<in> S \<inter> T \<inter> (U1 \<inter> U2)"
    by blast+
  moreover have "P (V1 \<inter> V2)"
    by (simp add: P \<open>P V1\<close> \<open>P V2\<close>)
  ultimately show "\<exists>U. open U \<and> (\<exists>V. P V \<and> x \<in> S \<inter> T \<inter> U \<and> S \<inter> T \<inter> U \<subseteq> V \<and> V \<subseteq> S \<inter> T \<inter> A)"
    using \<open>open U1\<close> \<open>open U2\<close> by blast
qed


lemma locally_Times:
  fixes S :: "('a::metric_space) set" and T :: "('b::metric_space) set"
  assumes PS: "locally P S" and QT: "locally Q T" and R: "\<And>S T. P S \<and> Q T \<Longrightarrow> R(S \<times> T)"
  shows "locally R (S \<times> T)"
    unfolding locally_def
proof (clarify)
  fix W x y
  assume W: "openin (top_of_set (S \<times> T)) W" and xy: "(x, y) \<in> W"
  then obtain U V where "openin (top_of_set S) U" "x \<in> U"
                        "openin (top_of_set T) V" "y \<in> V" "U \<times> V \<subseteq> W"
    using Times_in_interior_subtopology by metis
  then obtain U1 U2 V1 V2
         where opeS: "openin (top_of_set S) U1 \<and> P U2 \<and> x \<in> U1 \<and> U1 \<subseteq> U2 \<and> U2 \<subseteq> U"
           and opeT: "openin (top_of_set T) V1 \<and> Q V2 \<and> y \<in> V1 \<and> V1 \<subseteq> V2 \<and> V2 \<subseteq> V"
    by (meson PS QT locallyE)
  then have "openin (top_of_set (S \<times> T)) (U1 \<times> V1)"
    by (simp add: openin_Times)
  moreover have "R (U2 \<times> V2)"
    by (simp add: R opeS opeT)
  moreover have "U1 \<times> V1 \<subseteq> U2 \<times> V2 \<and> U2 \<times> V2 \<subseteq> W"
    using opeS opeT \<open>U \<times> V \<subseteq> W\<close> by auto 
  ultimately show "\<exists>U V. openin (top_of_set (S \<times> T)) U \<and> R V \<and> (x,y) \<in> U \<and> U \<subseteq> V \<and> V \<subseteq> W"
    using opeS opeT by auto 
qed


proposition homeomorphism_locally_imp:
  fixes S :: "'a::metric_space set" and T :: "'b::t2_space set"
  assumes S: "locally P S" and hom: "homeomorphism S T f g"
      and Q: "\<And>S S'. \<lbrakk>P S; homeomorphism S S' f g\<rbrakk> \<Longrightarrow> Q S'"
    shows "locally Q T"
proof (clarsimp simp: locally_def)
  fix W y
  assume "y \<in> W" and "openin (top_of_set T) W"
  then obtain A where T: "open A" "W = T \<inter> A"
    by (force simp: openin_open)
  then have "W \<subseteq> T" by auto
  have f: "\<And>x. x \<in> S \<Longrightarrow> g(f x) = x" "f ` S = T" "continuous_on S f"
   and g: "\<And>y. y \<in> T \<Longrightarrow> f(g y) = y" "g ` T = S" "continuous_on T g"
    using hom by (auto simp: homeomorphism_def)
  have gw: "g ` W = S \<inter> f -` W"
    using \<open>W \<subseteq> T\<close> g by force
  have \<circ>: "openin (top_of_set S) (g ` W)"
  proof -
    have "continuous_on S f"
      using f(3) by blast
    then show "openin (top_of_set S) (g ` W)"
      by (simp add: gw Collect_conj_eq \<open>openin (top_of_set T) W\<close> continuous_on_open f(2))
  qed
  then obtain U V
    where osu: "openin (top_of_set S) U" and uv: "P V" "g y \<in> U" "U \<subseteq> V" "V \<subseteq> g ` W"
    using S [unfolded locally_def, rule_format, of "g ` W" "g y"] \<open>y \<in> W\<close> by force
  have "V \<subseteq> S" using uv by (simp add: gw)
  have fv: "f ` V = T \<inter> {x. g x \<in> V}"
    using \<open>f ` S = T\<close> f \<open>V \<subseteq> S\<close> by auto
  have "f ` V \<subseteq> W"
    using uv using Int_lower2 gw image_subsetI mem_Collect_eq subset_iff by auto
  have contvf: "continuous_on V f"
    using \<open>V \<subseteq> S\<close> continuous_on_subset f(3) by blast
  have contvg: "continuous_on (f ` V) g"
    using \<open>f ` V \<subseteq> W\<close> \<open>W \<subseteq> T\<close> continuous_on_subset [OF g(3)] by blast
  have "V \<subseteq> g ` f ` V"
    by (metis \<open>V \<subseteq> S\<close> hom homeomorphism_def homeomorphism_of_subsets order_refl)
  then have homv: "homeomorphism V (f ` V) f g"
    using \<open>V \<subseteq> S\<close> f by (auto simp add: homeomorphism_def contvf contvg)
  have "openin (top_of_set (g ` T)) U"
    using \<open>g ` T = S\<close> by (simp add: osu)
  then have 1: "openin (top_of_set T) (T \<inter> g -` U)"
    using \<open>continuous_on T g\<close> continuous_on_open [THEN iffD1] by blast
  have 2: "\<exists>V. Q V \<and> y \<in> (T \<inter> g -` U) \<and> (T \<inter> g -` U) \<subseteq> V \<and> V \<subseteq> W"
  proof (intro exI conjI)
    show "Q (f ` V)"
      using Q homv \<open>P V\<close> by blast
    show "y \<in> T \<inter> g -` U"
      using T(2) \<open>y \<in> W\<close> \<open>g y \<in> U\<close> by blast
    show "T \<inter> g -` U \<subseteq> f ` V"
      using g(1) image_iff uv(3) by fastforce
    show "f ` V \<subseteq> W"
      using \<open>f ` V \<subseteq> W\<close> by blast
  qed
  show "\<exists>U. openin (top_of_set T) U \<and> (\<exists>v. Q v \<and> y \<in> U \<and> U \<subseteq> v \<and> v \<subseteq> W)"
    by (meson 1 2)
qed

lemma homeomorphism_locally:
  fixes f:: "'a::metric_space \<Rightarrow> 'b::metric_space"
  assumes hom: "homeomorphism S T f g"
      and eq: "\<And>S T. homeomorphism S T f g \<Longrightarrow> (P S \<longleftrightarrow> Q T)"
    shows "locally P S \<longleftrightarrow> locally Q T"
     (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    using eq hom homeomorphism_locally_imp by blast
next
  assume ?rhs
  then show ?lhs
    using eq homeomorphism_sym homeomorphism_symD [OF hom] 
    by (blast intro: homeomorphism_locally_imp) 
qed

lemma homeomorphic_locally:
  fixes S:: "'a::metric_space set" and T:: "'b::metric_space set"
  assumes hom: "S homeomorphic T"
          and iff: "\<And>X Y. X homeomorphic Y \<Longrightarrow> (P X \<longleftrightarrow> Q Y)"
    shows "locally P S \<longleftrightarrow> locally Q T"
proof -
  obtain f g where hom: "homeomorphism S T f g"
    using assms by (force simp: homeomorphic_def)
  then show ?thesis
    using homeomorphic_def local.iff
    by (blast intro!: homeomorphism_locally)
qed

lemma homeomorphic_local_compactness:
  fixes S:: "'a::metric_space set" and T:: "'b::metric_space set"
  shows "S homeomorphic T \<Longrightarrow> locally compact S \<longleftrightarrow> locally compact T"
by (simp add: homeomorphic_compactness homeomorphic_locally)

lemma locally_translation:
  fixes P :: "'a :: real_normed_vector set \<Rightarrow> bool"
  shows "(\<And>S. P ((+) a ` S) = P S) \<Longrightarrow> locally P ((+) a ` S) = locally P S"
  using homeomorphism_locally [OF homeomorphism_translation]
  by (metis (full_types) homeomorphism_image2)

lemma locally_injective_linear_image:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes f: "linear f" "inj f" and iff: "\<And>S. P (f ` S) \<longleftrightarrow> Q S"
  shows "locally P (f ` S) \<longleftrightarrow> locally Q S"
  using homeomorphism_locally [of "f`S" _ _ f] linear_homeomorphism_image [OF f]
  by (metis (no_types, lifting) homeomorphism_image2 iff)

lemma locally_open_map_image:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes P: "locally P S"
      and f: "continuous_on S f"
      and oo: "\<And>T. openin (top_of_set S) T \<Longrightarrow> openin (top_of_set (f ` S)) (f ` T)"
      and Q: "\<And>T. \<lbrakk>T \<subseteq> S; P T\<rbrakk> \<Longrightarrow> Q(f ` T)"
    shows "locally Q (f ` S)"
proof (clarsimp simp add: locally_def)
  fix W y
  assume oiw: "openin (top_of_set (f ` S)) W" and "y \<in> W"
  then have "W \<subseteq> f ` S" by (simp add: openin_euclidean_subtopology_iff)
  have oivf: "openin (top_of_set S) (S \<inter> f -` W)"
    by (rule continuous_on_open [THEN iffD1, rule_format, OF f oiw])
  then obtain x where "x \<in> S" "f x = y"
    using \<open>W \<subseteq> f ` S\<close> \<open>y \<in> W\<close> by blast
  then obtain U V
    where "openin (top_of_set S) U" "P V" "x \<in> U" "U \<subseteq> V" "V \<subseteq> S \<inter> f -` W"
    using P [unfolded locally_def, rule_format, of "(S \<inter> f -` W)" x] oivf \<open>y \<in> W\<close>
    by auto
  then have "openin (top_of_set (f ` S)) (f ` U)"
    by (simp add: oo)
  then show "\<exists>X. openin (top_of_set (f ` S)) X \<and> (\<exists>Y. Q Y \<and> y \<in> X \<and> X \<subseteq> Y \<and> Y \<subseteq> W)"
    using Q \<open>P V\<close> \<open>U \<subseteq> V\<close> \<open>V \<subseteq> S \<inter> f -` W\<close> \<open>f x = y\<close> \<open>x \<in> U\<close> by blast
qed


subsection\<open>An induction principle for connected sets\<close>

proposition connected_induction:
  assumes "connected S"
      and opD: "\<And>T a. \<lbrakk>openin (top_of_set S) T; a \<in> T\<rbrakk> \<Longrightarrow> \<exists>z. z \<in> T \<and> P z"
      and opI: "\<And>a. a \<in> S
             \<Longrightarrow> \<exists>T. openin (top_of_set S) T \<and> a \<in> T \<and>
                     (\<forall>x \<in> T. \<forall>y \<in> T. P x \<and> P y \<and> Q x \<longrightarrow> Q y)"
      and etc: "a \<in> S" "b \<in> S" "P a" "P b" "Q a"
    shows "Q b"
proof -
  let ?A = "{b. \<exists>T. openin (top_of_set S) T \<and> b \<in> T \<and> (\<forall>x\<in>T. P x \<longrightarrow> Q x)}"
  let ?B = "{b. \<exists>T. openin (top_of_set S) T \<and> b \<in> T \<and> (\<forall>x\<in>T. P x \<longrightarrow> \<not> Q x)}"
  have 1: "openin (top_of_set S) ?A"
    by (subst openin_subopen, blast)
  have 2: "openin (top_of_set S) ?B"
    by (subst openin_subopen, blast)
  have \<section>: "?A \<inter> ?B = {}"
    by (clarsimp simp: set_eq_iff) (metis (no_types, hide_lams) Int_iff opD openin_Int)
  have *: "S \<subseteq> ?A \<union> ?B"
    by clarsimp (meson opI)
  have "?A = {} \<or> ?B = {}"
    using \<open>connected S\<close> [unfolded connected_openin, simplified, rule_format, OF 1 \<section> * 2] 
    by blast
  then show ?thesis
    by clarsimp (meson opI etc)
qed

lemma connected_equivalence_relation_gen:
  assumes "connected S"
      and etc: "a \<in> S" "b \<in> S" "P a" "P b"
      and trans: "\<And>x y z. \<lbrakk>R x y; R y z\<rbrakk> \<Longrightarrow> R x z"
      and opD: "\<And>T a. \<lbrakk>openin (top_of_set S) T; a \<in> T\<rbrakk> \<Longrightarrow> \<exists>z. z \<in> T \<and> P z"
      and opI: "\<And>a. a \<in> S
             \<Longrightarrow> \<exists>T. openin (top_of_set S) T \<and> a \<in> T \<and>
                     (\<forall>x \<in> T. \<forall>y \<in> T. P x \<and> P y \<longrightarrow> R x y)"
    shows "R a b"
proof -
  have "\<And>a b c. \<lbrakk>a \<in> S; P a; b \<in> S; c \<in> S; P b; P c; R a b\<rbrakk> \<Longrightarrow> R a c"
    apply (rule connected_induction [OF \<open>connected S\<close> opD], simp_all)
    by (meson trans opI)
  then show ?thesis by (metis etc opI)
qed

lemma connected_induction_simple:
  assumes "connected S"
      and etc: "a \<in> S" "b \<in> S" "P a"
      and opI: "\<And>a. a \<in> S
             \<Longrightarrow> \<exists>T. openin (top_of_set S) T \<and> a \<in> T \<and>
                     (\<forall>x \<in> T. \<forall>y \<in> T. P x \<longrightarrow> P y)"
    shows "P b"
  by (rule connected_induction [OF \<open>connected S\<close> _, where P = "\<lambda>x. True"])
     (use opI etc in auto)

lemma connected_equivalence_relation:
  assumes "connected S"
      and etc: "a \<in> S" "b \<in> S"
      and sym: "\<And>x y. \<lbrakk>R x y; x \<in> S; y \<in> S\<rbrakk> \<Longrightarrow> R y x"
      and trans: "\<And>x y z. \<lbrakk>R x y; R y z; x \<in> S; y \<in> S; z \<in> S\<rbrakk> \<Longrightarrow> R x z"
      and opI: "\<And>a. a \<in> S \<Longrightarrow> \<exists>T. openin (top_of_set S) T \<and> a \<in> T \<and> (\<forall>x \<in> T. R a x)"
    shows "R a b"
proof -
  have "\<And>a b c. \<lbrakk>a \<in> S; b \<in> S; c \<in> S; R a b\<rbrakk> \<Longrightarrow> R a c"
    apply (rule connected_induction_simple [OF \<open>connected S\<close>], simp_all)
    by (meson local.sym local.trans opI openin_imp_subset subsetCE)
  then show ?thesis by (metis etc opI)
qed

lemma locally_constant_imp_constant:
  assumes "connected S"
      and opI: "\<And>a. a \<in> S
             \<Longrightarrow> \<exists>T. openin (top_of_set S) T \<and> a \<in> T \<and> (\<forall>x \<in> T. f x = f a)"
    shows "f constant_on S"
proof -
  have "\<And>x y. x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> f x = f y"
    apply (rule connected_equivalence_relation [OF \<open>connected S\<close>], simp_all)
    by (metis opI)
  then show ?thesis
    by (metis constant_on_def)
qed

lemma locally_constant:
  assumes "connected S"
  shows "locally (\<lambda>U. f constant_on U) S \<longleftrightarrow> f constant_on S" (is "?lhs = ?rhs")
proof
  assume ?lhs
  then have "\<And>a. a \<in> S \<Longrightarrow> \<exists>T. openin (top_of_set S) T \<and> a \<in> T \<and> (\<forall>x\<in>T. f x = f a)"
    unfolding locally_def
    by (metis (mono_tags, hide_lams) constant_on_def constant_on_subset openin_subtopology_self)
  then show ?rhs
    using assms
    by (simp add: locally_constant_imp_constant)
next
  assume ?rhs then show ?lhs
    using assms by (metis constant_on_subset locallyI openin_imp_subset order_refl)
qed


subsection\<open>Basic properties of local compactness\<close>

proposition locally_compact:
  fixes s :: "'a :: metric_space set"
  shows
    "locally compact s \<longleftrightarrow>
     (\<forall>x \<in> s. \<exists>u v. x \<in> u \<and> u \<subseteq> v \<and> v \<subseteq> s \<and>
                    openin (top_of_set s) u \<and> compact v)"
     (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    by (meson locallyE openin_subtopology_self)
next
  assume r [rule_format]: ?rhs
  have *: "\<exists>u v.
              openin (top_of_set s) u \<and>
              compact v \<and> x \<in> u \<and> u \<subseteq> v \<and> v \<subseteq> s \<inter> T"
          if "open T" "x \<in> s" "x \<in> T" for x T
  proof -
    obtain u v where uv: "x \<in> u" "u \<subseteq> v" "v \<subseteq> s" "compact v" "openin (top_of_set s) u"
      using r [OF \<open>x \<in> s\<close>] by auto
    obtain e where "e>0" and e: "cball x e \<subseteq> T"
      using open_contains_cball \<open>open T\<close> \<open>x \<in> T\<close> by blast
    show ?thesis
      apply (rule_tac x="(s \<inter> ball x e) \<inter> u" in exI)
      apply (rule_tac x="cball x e \<inter> v" in exI)
      using that \<open>e > 0\<close> e uv
      apply auto
      done
  qed
  show ?lhs
    by (rule locallyI) (metis "*" Int_iff openin_open)
qed

lemma locally_compactE:
  fixes S :: "'a :: metric_space set"
  assumes "locally compact S"
  obtains u v where "\<And>x. x \<in> S \<Longrightarrow> x \<in> u x \<and> u x \<subseteq> v x \<and> v x \<subseteq> S \<and>
                             openin (top_of_set S) (u x) \<and> compact (v x)"
  using assms unfolding locally_compact by metis

lemma locally_compact_alt:
  fixes S :: "'a :: heine_borel set"
  shows "locally compact S \<longleftrightarrow>
         (\<forall>x \<in> S. \<exists>U. x \<in> U \<and>
                    openin (top_of_set S) U \<and> compact(closure U) \<and> closure U \<subseteq> S)"
        (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    by (meson bounded_subset closure_minimal compact_closure compact_imp_bounded 
              compact_imp_closed dual_order.trans locally_compactE)
next
  assume ?rhs then show ?lhs
    by (meson closure_subset locally_compact)
qed

lemma locally_compact_Int_cball:
  fixes S :: "'a :: heine_borel set"
  shows "locally compact S \<longleftrightarrow> (\<forall>x \<in> S. \<exists>e. 0 < e \<and> closed(cball x e \<inter> S))"
        (is "?lhs = ?rhs")
proof
  assume L: ?lhs
  then have "\<And>x U V e. \<lbrakk>U \<subseteq> V; V \<subseteq> S; compact V; 0 < e; cball x e \<inter> S \<subseteq> U\<rbrakk>
       \<Longrightarrow> closed (cball x e \<inter> S)"
    by (metis compact_Int compact_cball compact_imp_closed inf.absorb_iff2 inf.assoc inf.orderE)
  with L show ?rhs
    by (meson locally_compactE openin_contains_cball)
next
  assume R: ?rhs
  show ?lhs unfolding locally_compact 
  proof
    fix x
    assume "x \<in> S"
    then obtain e where "e>0" and e: "closed (cball x e \<inter> S)"
      using R by blast
    then have "compact (cball x e \<inter> S)"
      by (simp add: bounded_Int compact_eq_bounded_closed)
    moreover have "\<forall>y\<in>ball x e \<inter> S. \<exists>\<epsilon>>0. cball y \<epsilon> \<inter> S \<subseteq> ball x e"
      by (meson Elementary_Metric_Spaces.open_ball IntD1 le_infI1 open_contains_cball_eq)
    moreover have "openin (top_of_set S) (ball x e \<inter> S)"
      by (simp add: inf_commute openin_open_Int)
    ultimately show "\<exists>U V. x \<in> U \<and> U \<subseteq> V \<and> V \<subseteq> S \<and> openin (top_of_set S) U \<and> compact V"
      by (metis Int_iff \<open>0 < e\<close> \<open>x \<in> S\<close> ball_subset_cball centre_in_ball inf_commute inf_le1 inf_mono order_refl)
  qed
qed

lemma locally_compact_compact:
  fixes S :: "'a :: heine_borel set"
  shows "locally compact S \<longleftrightarrow>
         (\<forall>K. K \<subseteq> S \<and> compact K
              \<longrightarrow> (\<exists>U V. K \<subseteq> U \<and> U \<subseteq> V \<and> V \<subseteq> S \<and>
                         openin (top_of_set S) U \<and> compact V))"
        (is "?lhs = ?rhs")
proof
  assume ?lhs
  then obtain u v where
    uv: "\<And>x. x \<in> S \<Longrightarrow> x \<in> u x \<and> u x \<subseteq> v x \<and> v x \<subseteq> S \<and>
                             openin (top_of_set S) (u x) \<and> compact (v x)"
    by (metis locally_compactE)
  have *: "\<exists>U V. K \<subseteq> U \<and> U \<subseteq> V \<and> V \<subseteq> S \<and> openin (top_of_set S) U \<and> compact V"
          if "K \<subseteq> S" "compact K" for K
  proof -
    have "\<And>C. (\<forall>c\<in>C. openin (top_of_set K) c) \<and> K \<subseteq> \<Union>C \<Longrightarrow>
                    \<exists>D\<subseteq>C. finite D \<and> K \<subseteq> \<Union>D"
      using that by (simp add: compact_eq_openin_cover)
    moreover have "\<forall>c \<in> (\<lambda>x. K \<inter> u x) ` K. openin (top_of_set K) c"
      using that by clarify (metis subsetD inf.absorb_iff2 openin_subset openin_subtopology_Int_subset topspace_euclidean_subtopology uv)
    moreover have "K \<subseteq> \<Union>((\<lambda>x. K \<inter> u x) ` K)"
      using that by clarsimp (meson subsetCE uv)
    ultimately obtain D where "D \<subseteq> (\<lambda>x. K \<inter> u x) ` K" "finite D" "K \<subseteq> \<Union>D"
      by metis
    then obtain T where T: "T \<subseteq> K" "finite T" "K \<subseteq> \<Union>((\<lambda>x. K \<inter> u x) ` T)"
      by (metis finite_subset_image)
    have Tuv: "\<Union>(u ` T) \<subseteq> \<Union>(v ` T)"
      using T that by (force dest!: uv)
    moreover
    have "openin (top_of_set S) (\<Union> (u ` T))"
      using T that uv by fastforce
    moreover
    have "compact (\<Union> (v ` T))"
      by (meson T compact_UN subset_eq that(1) uv)
    moreover have "\<Union> (v ` T) \<subseteq> S"
      by (metis SUP_least T(1) subset_eq that(1) uv)
    ultimately show ?thesis
      using T by auto 
  qed
  show ?rhs
    by (blast intro: *)
next
  assume ?rhs
  then show ?lhs
    apply (clarsimp simp add: locally_compact)
    apply (drule_tac x="{x}" in spec, simp)
    done
qed

lemma open_imp_locally_compact:
  fixes S :: "'a :: heine_borel set"
  assumes "open S"
    shows "locally compact S"
proof -
  have *: "\<exists>U V. x \<in> U \<and> U \<subseteq> V \<and> V \<subseteq> S \<and> openin (top_of_set S) U \<and> compact V"
          if "x \<in> S" for x
  proof -
    obtain e where "e>0" and e: "cball x e \<subseteq> S"
      using open_contains_cball assms \<open>x \<in> S\<close> by blast
    have ope: "openin (top_of_set S) (ball x e)"
      by (meson e open_ball ball_subset_cball dual_order.trans open_subset)
    show ?thesis
    proof (intro exI conjI)
      let ?U = "ball x e"
      let ?V = "cball x e"
      show "x \<in> ?U" "?U \<subseteq> ?V" "?V \<subseteq> S" "compact ?V"
        using \<open>e > 0\<close> e by auto
      show "openin (top_of_set S) ?U"
        using ope by blast
    qed
  qed
  show ?thesis
    unfolding locally_compact by (blast intro: *)
qed

lemma closed_imp_locally_compact:
  fixes S :: "'a :: heine_borel set"
  assumes "closed S"
    shows "locally compact S"
proof -
  have *: "\<exists>U V. x \<in> U \<and> U \<subseteq> V \<and> V \<subseteq> S \<and> openin (top_of_set S) U \<and> compact V"
          if "x \<in> S" for x
    apply (rule_tac x = "S \<inter> ball x 1" in exI, rule_tac x = "S \<inter> cball x 1" in exI)
    using \<open>x \<in> S\<close> assms by auto
  show ?thesis
    unfolding locally_compact by (blast intro: *)
qed

lemma locally_compact_UNIV: "locally compact (UNIV :: 'a :: heine_borel set)"
  by (simp add: closed_imp_locally_compact)

lemma locally_compact_Int:
  fixes S :: "'a :: t2_space set"
  shows "\<lbrakk>locally compact S; locally compact t\<rbrakk> \<Longrightarrow> locally compact (S \<inter> t)"
by (simp add: compact_Int locally_Int)

lemma locally_compact_closedin:
  fixes S :: "'a :: heine_borel set"
  shows "\<lbrakk>closedin (top_of_set S) t; locally compact S\<rbrakk>
        \<Longrightarrow> locally compact t"
  unfolding closedin_closed
  using closed_imp_locally_compact locally_compact_Int by blast

lemma locally_compact_delete:
     fixes S :: "'a :: t1_space set"
     shows "locally compact S \<Longrightarrow> locally compact (S - {a})"
  by (auto simp: openin_delete locally_open_subset)

lemma locally_closed:
  fixes S :: "'a :: heine_borel set"
  shows "locally closed S \<longleftrightarrow> locally compact S"
        (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    unfolding locally_def
    apply (elim all_forward imp_forward asm_rl exE)
    apply (rule_tac x = "u \<inter> ball x 1" in exI)
    apply (rule_tac x = "v \<inter> cball x 1" in exI)
    apply (force intro: openin_trans)
    done
next
  assume ?rhs then show ?lhs
    using compact_eq_bounded_closed locally_mono by blast
qed

lemma locally_compact_openin_Un:
  fixes S :: "'a::euclidean_space set"
  assumes LCS: "locally compact S" and LCT:"locally compact T"
      and opS: "openin (top_of_set (S \<union> T)) S"
      and opT: "openin (top_of_set (S \<union> T)) T"
    shows "locally compact (S \<union> T)"
proof -
  have "\<exists>e>0. closed (cball x e \<inter> (S \<union> T))" if "x \<in> S" for x
  proof -
    obtain e1 where "e1 > 0" and e1: "closed (cball x e1 \<inter> S)"
      using LCS \<open>x \<in> S\<close> unfolding locally_compact_Int_cball by blast
    moreover obtain e2 where "e2 > 0" and e2: "cball x e2 \<inter> (S \<union> T) \<subseteq> S"
      by (meson \<open>x \<in> S\<close> opS openin_contains_cball)
    then have "cball x e2 \<inter> (S \<union> T) = cball x e2 \<inter> S"
      by force
    ultimately have "closed (cball x (min e1 e2) \<inter> (S \<union> T))"
      by (metis (no_types, lifting) cball_min_Int closed_Int closed_cball inf_assoc inf_commute)
    then show ?thesis
      by (metis \<open>0 < e1\<close> \<open>0 < e2\<close> min_def)
  qed
  moreover have "\<exists>e>0. closed (cball x e \<inter> (S \<union> T))" if "x \<in> T" for x
  proof -
    obtain e1 where "e1 > 0" and e1: "closed (cball x e1 \<inter> T)"
      using LCT \<open>x \<in> T\<close> unfolding locally_compact_Int_cball by blast
    moreover obtain e2 where "e2 > 0" and e2: "cball x e2 \<inter> (S \<union> T) \<subseteq> T"
      by (meson \<open>x \<in> T\<close> opT openin_contains_cball)
    then have "cball x e2 \<inter> (S \<union> T) = cball x e2 \<inter> T"
      by force
    moreover have "closed (cball x e1 \<inter> (cball x e2 \<inter> T))"
      by (metis closed_Int closed_cball e1 inf_left_commute)
    ultimately show ?thesis
      by (rule_tac x="min e1 e2" in exI) (simp add: \<open>0 < e2\<close> cball_min_Int inf_assoc)
  qed
  ultimately show ?thesis
    by (force simp: locally_compact_Int_cball)
qed

lemma locally_compact_closedin_Un:
  fixes S :: "'a::euclidean_space set"
  assumes LCS: "locally compact S" and LCT:"locally compact T"
      and clS: "closedin (top_of_set (S \<union> T)) S"
      and clT: "closedin (top_of_set (S \<union> T)) T"
    shows "locally compact (S \<union> T)"
proof -
  have "\<exists>e>0. closed (cball x e \<inter> (S \<union> T))" if "x \<in> S" "x \<in> T" for x
  proof -
    obtain e1 where "e1 > 0" and e1: "closed (cball x e1 \<inter> S)"
      using LCS \<open>x \<in> S\<close> unfolding locally_compact_Int_cball by blast
    moreover
    obtain e2 where "e2 > 0" and e2: "closed (cball x e2 \<inter> T)"
      using LCT \<open>x \<in> T\<close> unfolding locally_compact_Int_cball by blast
    moreover have "closed (cball x (min e1 e2) \<inter> (S \<union> T))"
    proof -
      have "closed (cball x e1 \<inter> (cball x e2 \<inter> S))"
        by (metis closed_Int closed_cball e1 inf_left_commute)
      then show ?thesis
        by (simp add: Int_Un_distrib cball_min_Int closed_Int closed_Un e2 inf_assoc)
    qed
    ultimately show ?thesis
      by (rule_tac x="min e1 e2" in exI) linarith
  qed
  moreover
  have "\<exists>e>0. closed (cball x e \<inter> (S \<union> T))" if x: "x \<in> S" "x \<notin> T" for x
  proof -
    obtain e1 where "e1 > 0" and e1: "closed (cball x e1 \<inter> S)"
      using LCS \<open>x \<in> S\<close> unfolding locally_compact_Int_cball by blast
    moreover
    obtain e2 where "e2>0" and "cball x e2 \<inter> (S \<union> T) \<subseteq> S - T"
      using clT x by (fastforce simp: openin_contains_cball closedin_def)
    then have "closed (cball x e2 \<inter> T)"
    proof -
      have "{} = T - (T - cball x e2)"
        using Diff_subset Int_Diff \<open>cball x e2 \<inter> (S \<union> T) \<subseteq> S - T\<close> by auto
      then show ?thesis
        by (simp add: Diff_Diff_Int inf_commute)
    qed
    with e1 have "closed ((cball x e1 \<inter> cball x e2) \<inter> (S \<union> T))"
      apply (simp add: inf_commute inf_sup_distrib2)
      by (metis closed_Int closed_Un closed_cball inf_assoc inf_left_commute)
    then have "closed (cball x (min e1 e2) \<inter> (S \<union> T))"
      by (simp add: cball_min_Int inf_commute)
    ultimately show ?thesis
      using \<open>0 < e2\<close> by (rule_tac x="min e1 e2" in exI) linarith 
  qed
  moreover
  have "\<exists>e>0. closed (cball x e \<inter> (S \<union> T))" if x: "x \<notin> S" "x \<in> T" for x
  proof -
    obtain e1 where "e1 > 0" and e1: "closed (cball x e1 \<inter> T)"
      using LCT \<open>x \<in> T\<close> unfolding locally_compact_Int_cball by blast
    moreover
    obtain e2 where "e2>0" and "cball x e2 \<inter> (S \<union> T) \<subseteq> S \<union> T - S"
      using clS x by (fastforce simp: openin_contains_cball closedin_def)
    then have "closed (cball x e2 \<inter> S)"
      by (metis Diff_disjoint Int_empty_right closed_empty inf.left_commute inf.orderE inf_sup_absorb)
    with e1 have "closed ((cball x e1 \<inter> cball x e2) \<inter> (S \<union> T))"
      apply (simp add: inf_commute inf_sup_distrib2)
      by (metis closed_Int closed_Un closed_cball inf_assoc inf_left_commute)
    then have "closed (cball x (min e1 e2) \<inter> (S \<union> T))"
      by (auto simp: cball_min_Int)
    ultimately show ?thesis
      using \<open>0 < e2\<close> by (rule_tac x="min e1 e2" in exI) linarith
  qed
  ultimately show ?thesis
    by (auto simp: locally_compact_Int_cball)
qed

lemma locally_compact_Times:
  fixes S :: "'a::euclidean_space set" and T :: "'b::euclidean_space set"
  shows "\<lbrakk>locally compact S; locally compact T\<rbrakk> \<Longrightarrow> locally compact (S \<times> T)"
  by (auto simp: compact_Times locally_Times)

lemma locally_compact_compact_subopen:
  fixes S :: "'a :: heine_borel set"
  shows
   "locally compact S \<longleftrightarrow>
    (\<forall>K T. K \<subseteq> S \<and> compact K \<and> open T \<and> K \<subseteq> T
          \<longrightarrow> (\<exists>U V. K \<subseteq> U \<and> U \<subseteq> V \<and> U \<subseteq> T \<and> V \<subseteq> S \<and>
                     openin (top_of_set S) U \<and> compact V))"
   (is "?lhs = ?rhs")
proof
  assume L: ?lhs
  show ?rhs
  proof clarify
    fix K :: "'a set" and T :: "'a set"
    assume "K \<subseteq> S" and "compact K" and "open T" and "K \<subseteq> T"
    obtain U V where "K \<subseteq> U" "U \<subseteq> V" "V \<subseteq> S" "compact V"
                 and ope: "openin (top_of_set S) U"
      using L unfolding locally_compact_compact by (meson \<open>K \<subseteq> S\<close> \<open>compact K\<close>)
    show "\<exists>U V. K \<subseteq> U \<and> U \<subseteq> V \<and> U \<subseteq> T \<and> V \<subseteq> S \<and>
                openin (top_of_set S) U \<and> compact V"
    proof (intro exI conjI)
      show "K \<subseteq> U \<inter> T"
        by (simp add: \<open>K \<subseteq> T\<close> \<open>K \<subseteq> U\<close>)
      show "U \<inter> T \<subseteq> closure(U \<inter> T)"
        by (rule closure_subset)
      show "closure (U \<inter> T) \<subseteq> S"
        by (metis \<open>U \<subseteq> V\<close> \<open>V \<subseteq> S\<close> \<open>compact V\<close> closure_closed closure_mono compact_imp_closed inf.cobounded1 subset_trans)
      show "openin (top_of_set S) (U \<inter> T)"
        by (simp add: \<open>open T\<close> ope openin_Int_open)
      show "compact (closure (U \<inter> T))"
        by (meson Int_lower1 \<open>U \<subseteq> V\<close> \<open>compact V\<close> bounded_subset compact_closure compact_eq_bounded_closed)
    qed auto
  qed
next
  assume ?rhs then show ?lhs
    unfolding locally_compact_compact
    by (metis open_openin openin_topspace subtopology_superset top.extremum topspace_euclidean_subtopology)
qed


subsection\<open>Sura-Bura's results about compact components of sets\<close>

proposition Sura_Bura_compact:
  fixes S :: "'a::euclidean_space set"
  assumes "compact S" and C: "C \<in> components S"
  shows "C = \<Inter>{T. C \<subseteq> T \<and> openin (top_of_set S) T \<and>
                           closedin (top_of_set S) T}"
         (is "C = \<Inter>?\<T>")
proof
  obtain x where x: "C = connected_component_set S x" and "x \<in> S"
    using C by (auto simp: components_def)
  have "C \<subseteq> S"
    by (simp add: C in_components_subset)
  have "\<Inter>?\<T> \<subseteq> connected_component_set S x"
  proof (rule connected_component_maximal)
    have "x \<in> C"
      by (simp add: \<open>x \<in> S\<close> x)
    then show "x \<in> \<Inter>?\<T>"
      by blast
    have clo: "closed (\<Inter>?\<T>)"
      by (simp add: \<open>compact S\<close> closed_Inter closedin_compact_eq compact_imp_closed)
    have False
      if K1: "closedin (top_of_set (\<Inter>?\<T>)) K1" and
         K2: "closedin (top_of_set (\<Inter>?\<T>)) K2" and
         K12_Int: "K1 \<inter> K2 = {}" and K12_Un: "K1 \<union> K2 = \<Inter>?\<T>" and "K1 \<noteq> {}" "K2 \<noteq> {}"
       for K1 K2
    proof -
      have "closed K1" "closed K2"
        using closedin_closed_trans clo K1 K2 by blast+
      then obtain V1 V2 where "open V1" "open V2" "K1 \<subseteq> V1" "K2 \<subseteq> V2" and V12: "V1 \<inter> V2 = {}"
        using separation_normal \<open>K1 \<inter> K2 = {}\<close> by metis
      have SV12_ne: "(S - (V1 \<union> V2)) \<inter> (\<Inter>?\<T>) \<noteq> {}"
      proof (rule compact_imp_fip)
        show "compact (S - (V1 \<union> V2))"
          by (simp add: \<open>open V1\<close> \<open>open V2\<close> \<open>compact S\<close> compact_diff open_Un)
        show clo\<T>: "closed T" if "T \<in> ?\<T>" for T
          using that \<open>compact S\<close>
          by (force intro: closedin_closed_trans simp add: compact_imp_closed)
        show "(S - (V1 \<union> V2)) \<inter> \<Inter>\<F> \<noteq> {}" if "finite \<F>" and \<F>: "\<F> \<subseteq> ?\<T>" for \<F>
        proof
          assume djo: "(S - (V1 \<union> V2)) \<inter> \<Inter>\<F> = {}"
          obtain D where opeD: "openin (top_of_set S) D"
                   and cloD: "closedin (top_of_set S) D"
                   and "C \<subseteq> D" and DV12: "D \<subseteq> V1 \<union> V2"
          proof (cases "\<F> = {}")
            case True
            with \<open>C \<subseteq> S\<close> djo that show ?thesis
              by force
          next
            case False show ?thesis
            proof
              show ope: "openin (top_of_set S) (\<Inter>\<F>)"
                using openin_Inter \<open>finite \<F>\<close> False \<F> by blast
              then show "closedin (top_of_set S) (\<Inter>\<F>)"
                by (meson clo\<T> \<F> closed_Inter closed_subset openin_imp_subset subset_eq)
              show "C \<subseteq> \<Inter>\<F>"
                using \<F> by auto
              show "\<Inter>\<F> \<subseteq> V1 \<union> V2"
                using ope djo openin_imp_subset by fastforce
            qed
          qed
          have "connected C"
            by (simp add: x)
          have "closed D"
            using \<open>compact S\<close> cloD closedin_closed_trans compact_imp_closed by blast
          have cloV1: "closedin (top_of_set D) (D \<inter> closure V1)"
            and cloV2: "closedin (top_of_set D) (D \<inter> closure V2)"
            by (simp_all add: closedin_closed_Int)
          moreover have "D \<inter> closure V1 = D \<inter> V1" "D \<inter> closure V2 = D \<inter> V2"
            using \<open>D \<subseteq> V1 \<union> V2\<close> \<open>open V1\<close> \<open>open V2\<close> V12
            by (auto simp add: closure_subset [THEN subsetD] closure_iff_nhds_not_empty, blast+)
          ultimately have cloDV1: "closedin (top_of_set D) (D \<inter> V1)"
                      and cloDV2:  "closedin (top_of_set D) (D \<inter> V2)"
            by metis+
          then obtain U1 U2 where "closed U1" "closed U2"
               and D1: "D \<inter> V1 = D \<inter> U1" and D2: "D \<inter> V2 = D \<inter> U2"
            by (auto simp: closedin_closed)
          have "D \<inter> U1 \<inter> C \<noteq> {}"
          proof
            assume "D \<inter> U1 \<inter> C = {}"
            then have *: "C \<subseteq> D \<inter> V2"
              using D1 DV12 \<open>C \<subseteq> D\<close> by auto
            have 1: "openin (top_of_set S) (D \<inter> V2)"
              by (simp add: \<open>open V2\<close> opeD openin_Int_open)
            have 2: "closedin (top_of_set S) (D \<inter> V2)"
              using cloD cloDV2 closedin_trans by blast
            have "\<Inter> ?\<T> \<subseteq> D \<inter> V2"
              by (rule Inter_lower) (use * 1 2 in simp)
            then show False
              using K1 V12 \<open>K1 \<noteq> {}\<close> \<open>K1 \<subseteq> V1\<close> closedin_imp_subset by blast
          qed
          moreover have "D \<inter> U2 \<inter> C \<noteq> {}"
          proof
            assume "D \<inter> U2 \<inter> C = {}"
            then have *: "C \<subseteq> D \<inter> V1"
              using D2 DV12 \<open>C \<subseteq> D\<close> by auto
            have 1: "openin (top_of_set S) (D \<inter> V1)"
              by (simp add: \<open>open V1\<close> opeD openin_Int_open)
            have 2: "closedin (top_of_set S) (D \<inter> V1)"
              using cloD cloDV1 closedin_trans by blast
            have "\<Inter>?\<T> \<subseteq> D \<inter> V1"
              by (rule Inter_lower) (use * 1 2 in simp)
            then show False
              using K2 V12 \<open>K2 \<noteq> {}\<close> \<open>K2 \<subseteq> V2\<close> closedin_imp_subset by blast
          qed
          ultimately show False
            using \<open>connected C\<close> [unfolded connected_closed, simplified, rule_format, of concl: "D \<inter> U1" "D \<inter> U2"]
            using \<open>C \<subseteq> D\<close> D1 D2 V12 DV12 \<open>closed U1\<close> \<open>closed U2\<close> \<open>closed D\<close>
            by blast
        qed
      qed
      show False
        by (metis (full_types) DiffE UnE Un_upper2 SV12_ne \<open>K1 \<subseteq> V1\<close> \<open>K2 \<subseteq> V2\<close> disjoint_iff_not_equal subsetCE sup_ge1 K12_Un)
    qed
    then show "connected (\<Inter>?\<T>)"
      by (auto simp: connected_closedin_eq)
    show "\<Inter>?\<T> \<subseteq> S"
      by (fastforce simp: C in_components_subset)
  qed
  with x show "\<Inter>?\<T> \<subseteq> C" by simp
qed auto


corollary Sura_Bura_clopen_subset:
  fixes S :: "'a::euclidean_space set"
  assumes S: "locally compact S" and C: "C \<in> components S" and "compact C"
      and U: "open U" "C \<subseteq> U"
  obtains K where "openin (top_of_set S) K" "compact K" "C \<subseteq> K" "K \<subseteq> U"
proof (rule ccontr)
  assume "\<not> thesis"
  with that have neg: "\<nexists>K. openin (top_of_set S) K \<and> compact K \<and> C \<subseteq> K \<and> K \<subseteq> U"
    by metis
  obtain V K where "C \<subseteq> V" "V \<subseteq> U" "V \<subseteq> K" "K \<subseteq> S" "compact K"
               and opeSV: "openin (top_of_set S) V"
    using S U \<open>compact C\<close> by (meson C in_components_subset locally_compact_compact_subopen)
  let ?\<T> = "{T. C \<subseteq> T \<and> openin (top_of_set K) T \<and> compact T \<and> T \<subseteq> K}"
  have CK: "C \<in> components K"
    by (meson C \<open>C \<subseteq> V\<close> \<open>K \<subseteq> S\<close> \<open>V \<subseteq> K\<close> components_intermediate_subset subset_trans)
  with \<open>compact K\<close>
  have "C = \<Inter>{T. C \<subseteq> T \<and> openin (top_of_set K) T \<and> closedin (top_of_set K) T}"
    by (simp add: Sura_Bura_compact)
  then have Ceq: "C = \<Inter>?\<T>"
    by (simp add: closedin_compact_eq \<open>compact K\<close>)
  obtain W where "open W" and W: "V = S \<inter> W"
    using opeSV by (auto simp: openin_open)
  have "-(U \<inter> W) \<inter> \<Inter>?\<T> \<noteq> {}"
  proof (rule closed_imp_fip_compact)
    show "- (U \<inter> W) \<inter> \<Inter>\<F> \<noteq> {}"
      if "finite \<F>" and \<F>: "\<F> \<subseteq> ?\<T>" for \<F>
    proof (cases "\<F> = {}")
      case True
      have False if "U = UNIV" "W = UNIV"
      proof -
        have "V = S"
          by (simp add: W \<open>W = UNIV\<close>)
        with neg show False
          using \<open>C \<subseteq> V\<close> \<open>K \<subseteq> S\<close> \<open>V \<subseteq> K\<close> \<open>V \<subseteq> U\<close> \<open>compact K\<close> by auto
      qed
      with True show ?thesis
        by auto
    next
      case False
      show ?thesis
      proof
        assume "- (U \<inter> W) \<inter> \<Inter>\<F> = {}"
        then have FUW: "\<Inter>\<F> \<subseteq> U \<inter> W"
          by blast
        have "C \<subseteq> \<Inter>\<F>"
          using \<F> by auto
        moreover have "compact (\<Inter>\<F>)"
          by (metis (no_types, lifting) compact_Inter False mem_Collect_eq subsetCE \<F>)
        moreover have "\<Inter>\<F> \<subseteq> K"
          using False that(2) by fastforce
        moreover have opeKF: "openin (top_of_set K) (\<Inter>\<F>)"
          using False \<F> \<open>finite \<F>\<close> by blast
        then have opeVF: "openin (top_of_set V) (\<Inter>\<F>)"
          using W \<open>K \<subseteq> S\<close> \<open>V \<subseteq> K\<close> opeKF \<open>\<Inter>\<F> \<subseteq> K\<close> FUW openin_subset_trans by fastforce
        then have "openin (top_of_set S) (\<Inter>\<F>)"
          by (metis opeSV openin_trans)
        moreover have "\<Inter>\<F> \<subseteq> U"
          by (meson \<open>V \<subseteq> U\<close> opeVF dual_order.trans openin_imp_subset)
        ultimately show False
          using neg by blast
      qed
    qed
  qed (use \<open>open W\<close> \<open>open U\<close> in auto)
  with W Ceq \<open>C \<subseteq> V\<close> \<open>C \<subseteq> U\<close> show False
    by auto
qed


corollary Sura_Bura_clopen_subset_alt:
  fixes S :: "'a::euclidean_space set"
  assumes S: "locally compact S" and C: "C \<in> components S" and "compact C"
      and opeSU: "openin (top_of_set S) U" and "C \<subseteq> U"
  obtains K where "openin (top_of_set S) K" "compact K" "C \<subseteq> K" "K \<subseteq> U"
proof -
  obtain V where "open V" "U = S \<inter> V"
    using opeSU by (auto simp: openin_open)
  with \<open>C \<subseteq> U\<close> have "C \<subseteq> V"
    by auto
  then show ?thesis
    using Sura_Bura_clopen_subset [OF S C \<open>compact C\<close> \<open>open V\<close>]
    by (metis \<open>U = S \<inter> V\<close> inf.bounded_iff openin_imp_subset that)
qed

corollary Sura_Bura:
  fixes S :: "'a::euclidean_space set"
  assumes "locally compact S" "C \<in> components S" "compact C"
  shows "C = \<Inter> {K. C \<subseteq> K \<and> compact K \<and> openin (top_of_set S) K}"
         (is "C = ?rhs")
proof
  show "?rhs \<subseteq> C"
  proof (clarsimp, rule ccontr)
    fix x
    assume *: "\<forall>X. C \<subseteq> X \<and> compact X \<and> openin (top_of_set S) X \<longrightarrow> x \<in> X"
      and "x \<notin> C"
    obtain U V where "open U" "open V" "{x} \<subseteq> U" "C \<subseteq> V" "U \<inter> V = {}"
      using separation_normal [of "{x}" C]
      by (metis Int_empty_left \<open>x \<notin> C\<close> \<open>compact C\<close> closed_empty closed_insert compact_imp_closed insert_disjoint(1))
    have "x \<notin> V"
      using \<open>U \<inter> V = {}\<close> \<open>{x} \<subseteq> U\<close> by blast
    then show False
      by (meson "*" Sura_Bura_clopen_subset \<open>C \<subseteq> V\<close> \<open>open V\<close> assms(1) assms(2) assms(3) subsetCE)
  qed
qed blast


subsection\<open>Special cases of local connectedness and path connectedness\<close>

lemma locally_connected_1:
  assumes
    "\<And>V x. \<lbrakk>openin (top_of_set S) V; x \<in> V\<rbrakk> \<Longrightarrow> \<exists>U. openin (top_of_set S) U \<and> connected U \<and> x \<in> U \<and> U \<subseteq> V"
   shows "locally connected S"
  by (metis assms locally_def)

lemma locally_connected_2:
  assumes "locally connected S"
          "openin (top_of_set S) t"
          "x \<in> t"
   shows "openin (top_of_set S) (connected_component_set t x)"
proof -
  { fix y :: 'a
    let ?SS = "top_of_set S"
    assume 1: "openin ?SS t"
              "\<forall>w x. openin ?SS w \<and> x \<in> w \<longrightarrow> (\<exists>u. openin ?SS u \<and> (\<exists>v. connected v \<and> x \<in> u \<and> u \<subseteq> v \<and> v \<subseteq> w))"
    and "connected_component t x y"
    then have "y \<in> t" and y: "y \<in> connected_component_set t x"
      using connected_component_subset by blast+
    obtain F where
      "\<forall>x y. (\<exists>w. openin ?SS w \<and> (\<exists>u. connected u \<and> x \<in> w \<and> w \<subseteq> u \<and> u \<subseteq> y)) = (openin ?SS (F x y) \<and> (\<exists>u. connected u \<and> x \<in> F x y \<and> F x y \<subseteq> u \<and> u \<subseteq> y))"
      by moura
    then obtain G where
       "\<forall>a A. (\<exists>U. openin ?SS U \<and> (\<exists>V. connected V \<and> a \<in> U \<and> U \<subseteq> V \<and> V \<subseteq> A)) = (openin ?SS (F a A) \<and> connected (G a A) \<and> a \<in> F a A \<and> F a A \<subseteq> G a A \<and> G a A \<subseteq> A)"
      by moura
    then have *: "openin ?SS (F y t) \<and> connected (G y t) \<and> y \<in> F y t \<and> F y t \<subseteq> G y t \<and> G y t \<subseteq> t"
      using 1 \<open>y \<in> t\<close> by presburger
    have "G y t \<subseteq> connected_component_set t y"
      by (metis (no_types) * connected_component_eq_self connected_component_mono contra_subsetD)
    then have "\<exists>A. openin ?SS A \<and> y \<in> A \<and> A \<subseteq> connected_component_set t x"
      by (metis (no_types) * connected_component_eq dual_order.trans y)
  }
  then show ?thesis
    using assms openin_subopen by (force simp: locally_def)
qed

lemma locally_connected_3:
  assumes "\<And>t x. \<lbrakk>openin (top_of_set S) t; x \<in> t\<rbrakk>
              \<Longrightarrow> openin (top_of_set S)
                          (connected_component_set t x)"
          "openin (top_of_set S) v" "x \<in> v"
   shows  "\<exists>u. openin (top_of_set S) u \<and> connected u \<and> x \<in> u \<and> u \<subseteq> v"
using assms connected_component_subset by fastforce

lemma locally_connected:
  "locally connected S \<longleftrightarrow>
   (\<forall>v x. openin (top_of_set S) v \<and> x \<in> v
          \<longrightarrow> (\<exists>u. openin (top_of_set S) u \<and> connected u \<and> x \<in> u \<and> u \<subseteq> v))"
by (metis locally_connected_1 locally_connected_2 locally_connected_3)

lemma locally_connected_open_connected_component:
  "locally connected S \<longleftrightarrow>
   (\<forall>t x. openin (top_of_set S) t \<and> x \<in> t
          \<longrightarrow> openin (top_of_set S) (connected_component_set t x))"
by (metis locally_connected_1 locally_connected_2 locally_connected_3)

lemma locally_path_connected_1:
  assumes
    "\<And>v x. \<lbrakk>openin (top_of_set S) v; x \<in> v\<rbrakk>
              \<Longrightarrow> \<exists>u. openin (top_of_set S) u \<and> path_connected u \<and> x \<in> u \<and> u \<subseteq> v"
   shows "locally path_connected S"
  by (force simp add: locally_def dest: assms)

lemma locally_path_connected_2:
  assumes "locally path_connected S"
          "openin (top_of_set S) t"
          "x \<in> t"
   shows "openin (top_of_set S) (path_component_set t x)"
proof -
  { fix y :: 'a
    let ?SS = "top_of_set S"
    assume 1: "openin ?SS t"
              "\<forall>w x. openin ?SS w \<and> x \<in> w \<longrightarrow> (\<exists>u. openin ?SS u \<and> (\<exists>v. path_connected v \<and> x \<in> u \<and> u \<subseteq> v \<and> v \<subseteq> w))"
    and "path_component t x y"
    then have "y \<in> t" and y: "y \<in> path_component_set t x"
      using path_component_mem(2) by blast+
    obtain F where
      "\<forall>x y. (\<exists>w. openin ?SS w \<and> (\<exists>u. path_connected u \<and> x \<in> w \<and> w \<subseteq> u \<and> u \<subseteq> y)) = (openin ?SS (F x y) \<and> (\<exists>u. path_connected u \<and> x \<in> F x y \<and> F x y \<subseteq> u \<and> u \<subseteq> y))"
      by moura
    then obtain G where
       "\<forall>a A. (\<exists>U. openin ?SS U \<and> (\<exists>V. path_connected V \<and> a \<in> U \<and> U \<subseteq> V \<and> V \<subseteq> A)) = (openin ?SS (F a A) \<and> path_connected (G a A) \<and> a \<in> F a A \<and> F a A \<subseteq> G a A \<and> G a A \<subseteq> A)"
      by moura
    then have *: "openin ?SS (F y t) \<and> path_connected (G y t) \<and> y \<in> F y t \<and> F y t \<subseteq> G y t \<and> G y t \<subseteq> t"
      using 1 \<open>y \<in> t\<close> by presburger
    have "G y t \<subseteq> path_component_set t y"
      using * path_component_maximal rev_subsetD by blast
    then have "\<exists>A. openin ?SS A \<and> y \<in> A \<and> A \<subseteq> path_component_set t x"
      by (metis "*" \<open>G y t \<subseteq> path_component_set t y\<close> dual_order.trans path_component_eq y)
  }
  then show ?thesis
    using assms openin_subopen by (force simp: locally_def)
qed

lemma locally_path_connected_3:
  assumes "\<And>t x. \<lbrakk>openin (top_of_set S) t; x \<in> t\<rbrakk>
              \<Longrightarrow> openin (top_of_set S) (path_component_set t x)"
          "openin (top_of_set S) v" "x \<in> v"
   shows  "\<exists>u. openin (top_of_set S) u \<and> path_connected u \<and> x \<in> u \<and> u \<subseteq> v"
proof -
  have "path_component v x x"
    by (meson assms(3) path_component_refl)
  then show ?thesis
    by (metis assms mem_Collect_eq path_component_subset path_connected_path_component)
qed

proposition locally_path_connected:
  "locally path_connected S \<longleftrightarrow>
   (\<forall>V x. openin (top_of_set S) V \<and> x \<in> V
          \<longrightarrow> (\<exists>U. openin (top_of_set S) U \<and> path_connected U \<and> x \<in> U \<and> U \<subseteq> V))"
  by (metis locally_path_connected_1 locally_path_connected_2 locally_path_connected_3)

proposition locally_path_connected_open_path_component:
  "locally path_connected S \<longleftrightarrow>
   (\<forall>t x. openin (top_of_set S) t \<and> x \<in> t
          \<longrightarrow> openin (top_of_set S) (path_component_set t x))"
  by (metis locally_path_connected_1 locally_path_connected_2 locally_path_connected_3)

lemma locally_connected_open_component:
  "locally connected S \<longleftrightarrow>
   (\<forall>t c. openin (top_of_set S) t \<and> c \<in> components t
          \<longrightarrow> openin (top_of_set S) c)"
by (metis components_iff locally_connected_open_connected_component)

proposition locally_connected_im_kleinen:
  "locally connected S \<longleftrightarrow>
   (\<forall>v x. openin (top_of_set S) v \<and> x \<in> v
       \<longrightarrow> (\<exists>u. openin (top_of_set S) u \<and>
                x \<in> u \<and> u \<subseteq> v \<and>
                (\<forall>y. y \<in> u \<longrightarrow> (\<exists>c. connected c \<and> c \<subseteq> v \<and> x \<in> c \<and> y \<in> c))))"
   (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    by (fastforce simp add: locally_connected)
next
  assume ?rhs
  have *: "\<exists>T. openin (top_of_set S) T \<and> x \<in> T \<and> T \<subseteq> c"
       if "openin (top_of_set S) t" and c: "c \<in> components t" and "x \<in> c" for t c x
  proof -
    from that \<open>?rhs\<close> [rule_format, of t x]
    obtain u where u:
      "openin (top_of_set S) u \<and> x \<in> u \<and> u \<subseteq> t \<and>
       (\<forall>y. y \<in> u \<longrightarrow> (\<exists>c. connected c \<and> c \<subseteq> t \<and> x \<in> c \<and> y \<in> c))"
      using in_components_subset by auto
    obtain F :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a" where
      "\<forall>x y. (\<exists>z. z \<in> x \<and> y = connected_component_set x z) = (F x y \<in> x \<and> y = connected_component_set x (F x y))"
      by moura
    then have F: "F t c \<in> t \<and> c = connected_component_set t (F t c)"
      by (meson components_iff c)
    obtain G :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a" where
        G: "\<forall>x y. (\<exists>z. z \<in> y \<and> z \<notin> x) = (G x y \<in> y \<and> G x y \<notin> x)"
      by moura
     have "G c u \<notin> u \<or> G c u \<in> c"
      using F by (metis (full_types) u connected_componentI connected_component_eq mem_Collect_eq that(3))
    then show ?thesis
      using G u by auto
  qed
  show ?lhs
    unfolding locally_connected_open_component by (meson "*" openin_subopen)
qed

proposition locally_path_connected_im_kleinen:
  "locally path_connected S \<longleftrightarrow>
   (\<forall>v x. openin (top_of_set S) v \<and> x \<in> v
       \<longrightarrow> (\<exists>u. openin (top_of_set S) u \<and>
                x \<in> u \<and> u \<subseteq> v \<and>
                (\<forall>y. y \<in> u \<longrightarrow> (\<exists>p. path p \<and> path_image p \<subseteq> v \<and>
                                pathstart p = x \<and> pathfinish p = y))))"
   (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    apply (simp add: locally_path_connected path_connected_def)
    apply (erule all_forward ex_forward imp_forward conjE | simp)+
    by (meson dual_order.trans)
next
  assume ?rhs
  have *: "\<exists>T. openin (top_of_set S) T \<and>
               x \<in> T \<and> T \<subseteq> path_component_set u z"
       if "openin (top_of_set S) u" and "z \<in> u" and c: "path_component u z x" for u z x
  proof -
    have "x \<in> u"
      by (meson c path_component_mem(2))
    with that \<open>?rhs\<close> [rule_format, of u x]
    obtain U where U:
      "openin (top_of_set S) U \<and> x \<in> U \<and> U \<subseteq> u \<and>
       (\<forall>y. y \<in> U \<longrightarrow> (\<exists>p. path p \<and> path_image p \<subseteq> u \<and> pathstart p = x \<and> pathfinish p = y))"
       by blast
    show ?thesis
      by (metis U c mem_Collect_eq path_component_def path_component_eq subsetI)
  qed
  show ?lhs
    unfolding locally_path_connected_open_path_component
    using "*" openin_subopen by fastforce
qed

lemma locally_path_connected_imp_locally_connected:
  "locally path_connected S \<Longrightarrow> locally connected S"
using locally_mono path_connected_imp_connected by blast

lemma locally_connected_components:
  "\<lbrakk>locally connected S; c \<in> components S\<rbrakk> \<Longrightarrow> locally connected c"
by (meson locally_connected_open_component locally_open_subset openin_subtopology_self)

lemma locally_path_connected_components:
  "\<lbrakk>locally path_connected S; c \<in> components S\<rbrakk> \<Longrightarrow> locally path_connected c"
by (meson locally_connected_open_component locally_open_subset locally_path_connected_imp_locally_connected openin_subtopology_self)

lemma locally_path_connected_connected_component:
  "locally path_connected S \<Longrightarrow> locally path_connected (connected_component_set S x)"
by (metis components_iff connected_component_eq_empty locally_empty locally_path_connected_components)

lemma open_imp_locally_path_connected:
  fixes S :: "'a :: real_normed_vector set"
  assumes "open S"
  shows "locally path_connected S"
proof (rule locally_mono)
  show "locally convex S"
    using assms unfolding locally_def
    by (meson open_ball centre_in_ball convex_ball openE open_subset openin_imp_subset openin_open_trans subset_trans)
  show "\<And>T::'a set. convex T \<Longrightarrow> path_connected T"
    using convex_imp_path_connected by blast
qed

lemma open_imp_locally_connected:
  fixes S :: "'a :: real_normed_vector set"
  shows "open S \<Longrightarrow> locally connected S"
by (simp add: locally_path_connected_imp_locally_connected open_imp_locally_path_connected)

lemma locally_path_connected_UNIV: "locally path_connected (UNIV::'a :: real_normed_vector set)"
  by (simp add: open_imp_locally_path_connected)

lemma locally_connected_UNIV: "locally connected (UNIV::'a :: real_normed_vector set)"
  by (simp add: open_imp_locally_connected)

lemma openin_connected_component_locally_connected:
    "locally connected S
     \<Longrightarrow> openin (top_of_set S) (connected_component_set S x)"
  by (metis connected_component_eq_empty locally_connected_2 openin_empty openin_subtopology_self)

lemma openin_components_locally_connected:
    "\<lbrakk>locally connected S; c \<in> components S\<rbrakk> \<Longrightarrow> openin (top_of_set S) c"
  using locally_connected_open_component openin_subtopology_self by blast

lemma openin_path_component_locally_path_connected:
  "locally path_connected S
        \<Longrightarrow> openin (top_of_set S) (path_component_set S x)"
by (metis (no_types) empty_iff locally_path_connected_2 openin_subopen openin_subtopology_self path_component_eq_empty)

lemma closedin_path_component_locally_path_connected:
  assumes "locally path_connected S"
  shows "closedin (top_of_set S) (path_component_set S x)"
proof -
  have "openin (top_of_set S) (\<Union> ({path_component_set S y |y. y \<in> S} - {path_component_set S x}))"
    using locally_path_connected_2 assms by fastforce
  then show ?thesis
    by  (simp add: closedin_def path_component_subset complement_path_component_Union)
qed

lemma convex_imp_locally_path_connected:
  fixes S :: "'a:: real_normed_vector set"
  assumes "convex S"
  shows "locally path_connected S"
proof (clarsimp simp add: locally_path_connected)
  fix V x
  assume "openin (top_of_set S) V" and "x \<in> V"
  then obtain T e where  "V = S \<inter> T" "x \<in> S" "0 < e" "ball x e \<subseteq> T"
    by (metis Int_iff openE openin_open)
  then have "openin (top_of_set S) (S \<inter> ball x e)" "path_connected (S \<inter> ball x e)"
    by (simp_all add: assms convex_Int convex_imp_path_connected openin_open_Int)
  then show "\<exists>U. openin (top_of_set S) U \<and> path_connected U \<and> x \<in> U \<and> U \<subseteq> V"
    using \<open>0 < e\<close> \<open>V = S \<inter> T\<close> \<open>ball x e \<subseteq> T\<close> \<open>x \<in> S\<close> by auto
qed

lemma convex_imp_locally_connected:
  fixes S :: "'a:: real_normed_vector set"
  shows "convex S \<Longrightarrow> locally connected S"
  by (simp add: locally_path_connected_imp_locally_connected convex_imp_locally_path_connected)


subsection\<open>Relations between components and path components\<close>

lemma path_component_eq_connected_component:
  assumes "locally path_connected S"
    shows "(path_component S x = connected_component S x)"
proof (cases "x \<in> S")
  case True
  have "openin (top_of_set (connected_component_set S x)) (path_component_set S x)"
  proof (rule openin_subset_trans)
    show "openin (top_of_set S) (path_component_set S x)"
      by (simp add: True assms locally_path_connected_2)
    show "connected_component_set S x \<subseteq> S"
      by (simp add: connected_component_subset)
  qed (simp add: path_component_subset_connected_component)
  moreover have "closedin (top_of_set (connected_component_set S x)) (path_component_set S x)"
    proof (rule closedin_subset_trans [of S])
  show "closedin (top_of_set S) (path_component_set S x)"
    by (simp add: assms closedin_path_component_locally_path_connected)
  show "connected_component_set S x \<subseteq> S"
    by (simp add: connected_component_subset)
  qed (simp add: path_component_subset_connected_component)
  ultimately have *: "path_component_set S x = connected_component_set S x"
    by (metis connected_connected_component connected_clopen True path_component_eq_empty)
  then show ?thesis
    by blast
next
  case False then show ?thesis
    by (metis Collect_empty_eq_bot connected_component_eq_empty path_component_eq_empty)
qed

lemma path_component_eq_connected_component_set:
     "locally path_connected S \<Longrightarrow> (path_component_set S x = connected_component_set S x)"
by (simp add: path_component_eq_connected_component)

lemma locally_path_connected_path_component:
     "locally path_connected S \<Longrightarrow> locally path_connected (path_component_set S x)"
using locally_path_connected_connected_component path_component_eq_connected_component by fastforce

lemma open_path_connected_component:
  fixes S :: "'a :: real_normed_vector set"
  shows "open S \<Longrightarrow> path_component S x = connected_component S x"
by (simp add: path_component_eq_connected_component open_imp_locally_path_connected)

lemma open_path_connected_component_set:
  fixes S :: "'a :: real_normed_vector set"
  shows "open S \<Longrightarrow> path_component_set S x = connected_component_set S x"
by (simp add: open_path_connected_component)

proposition locally_connected_quotient_image:
  assumes lcS: "locally connected S"
      and oo: "\<And>T. T \<subseteq> f ` S
                \<Longrightarrow> openin (top_of_set S) (S \<inter> f -` T) \<longleftrightarrow>
                    openin (top_of_set (f ` S)) T"
    shows "locally connected (f ` S)"
proof (clarsimp simp: locally_connected_open_component)
  fix U C
  assume opefSU: "openin (top_of_set (f ` S)) U" and "C \<in> components U"
  then have "C \<subseteq> U" "U \<subseteq> f ` S"
    by (meson in_components_subset openin_imp_subset)+
  then have "openin (top_of_set (f ` S)) C \<longleftrightarrow>
             openin (top_of_set S) (S \<inter> f -` C)"
    by (auto simp: oo)
  moreover have "openin (top_of_set S) (S \<inter> f -` C)"
  proof (subst openin_subopen, clarify)
    fix x
    assume "x \<in> S" "f x \<in> C"
    show "\<exists>T. openin (top_of_set S) T \<and> x \<in> T \<and> T \<subseteq> (S \<inter> f -` C)"
    proof (intro conjI exI)
      show "openin (top_of_set S) (connected_component_set (S \<inter> f -` U) x)"
      proof (rule ccontr)
        assume **: "\<not> openin (top_of_set S) (connected_component_set (S \<inter> f -` U) x)"
        then have "x \<notin> (S \<inter> f -` U)"
          using \<open>U \<subseteq> f ` S\<close> opefSU lcS locally_connected_2 oo by blast
        with ** show False
          by (metis (no_types) connected_component_eq_empty empty_iff openin_subopen)
      qed
    next
      show "x \<in> connected_component_set (S \<inter> f -` U) x"
        using \<open>C \<subseteq> U\<close> \<open>f x \<in> C\<close> \<open>x \<in> S\<close> by auto
    next
      have contf: "continuous_on S f"
        by (simp add: continuous_on_open oo openin_imp_subset)
      then have "continuous_on (connected_component_set (S \<inter> f -` U) x) f"
        by (meson connected_component_subset continuous_on_subset inf.boundedE)
      then have "connected (f ` connected_component_set (S \<inter> f -` U) x)"
        by (rule connected_continuous_image [OF _ connected_connected_component])
      moreover have "f ` connected_component_set (S \<inter> f -` U) x \<subseteq> U"
        using connected_component_in by blast
      moreover have "C \<inter> f ` connected_component_set (S \<inter> f -` U) x \<noteq> {}"
        using \<open>C \<subseteq> U\<close> \<open>f x \<in> C\<close> \<open>x \<in> S\<close> by fastforce
      ultimately have fC: "f ` (connected_component_set (S \<inter> f -` U) x) \<subseteq> C"
        by (rule components_maximal [OF \<open>C \<in> components U\<close>])
      have cUC: "connected_component_set (S \<inter> f -` U) x \<subseteq> (S \<inter> f -` C)"
        using connected_component_subset fC by blast
      have "connected_component_set (S \<inter> f -` U) x \<subseteq> connected_component_set (S \<inter> f -` C) x"
      proof -
        { assume "x \<in> connected_component_set (S \<inter> f -` U) x"
          then have ?thesis
            using cUC connected_component_idemp connected_component_mono by blast }
        then show ?thesis
          using connected_component_eq_empty by auto
      qed
      also have "\<dots> \<subseteq> (S \<inter> f -` C)"
        by (rule connected_component_subset)
      finally show "connected_component_set (S \<inter> f -` U) x \<subseteq> (S \<inter> f -` C)" .
    qed
  qed
  ultimately show "openin (top_of_set (f ` S)) C"
    by metis
qed

text\<open>The proof resembles that above but is not identical!\<close>
proposition locally_path_connected_quotient_image:
  assumes lcS: "locally path_connected S"
      and oo: "\<And>T. T \<subseteq> f ` S
                \<Longrightarrow> openin (top_of_set S) (S \<inter> f -` T) \<longleftrightarrow> openin (top_of_set (f ` S)) T"
    shows "locally path_connected (f ` S)"
proof (clarsimp simp: locally_path_connected_open_path_component)
  fix U y
  assume opefSU: "openin (top_of_set (f ` S)) U" and "y \<in> U"
  then have "path_component_set U y \<subseteq> U" "U \<subseteq> f ` S"
    by (meson path_component_subset openin_imp_subset)+
  then have "openin (top_of_set (f ` S)) (path_component_set U y) \<longleftrightarrow>
             openin (top_of_set S) (S \<inter> f -` path_component_set U y)"
  proof -
    have "path_component_set U y \<subseteq> f ` S"
      using \<open>U \<subseteq> f ` S\<close> \<open>path_component_set U y \<subseteq> U\<close> by blast
    then show ?thesis
      using oo by blast
  qed
  moreover have "openin (top_of_set S) (S \<inter> f -` path_component_set U y)"
  proof (subst openin_subopen, clarify)
    fix x
    assume "x \<in> S" and Uyfx: "path_component U y (f x)"
    then have "f x \<in> U"
      using path_component_mem by blast
    show "\<exists>T. openin (top_of_set S) T \<and> x \<in> T \<and> T \<subseteq> (S \<inter> f -` path_component_set U y)"
    proof (intro conjI exI)
      show "openin (top_of_set S) (path_component_set (S \<inter> f -` U) x)"
      proof (rule ccontr)
        assume **: "\<not> openin (top_of_set S) (path_component_set (S \<inter> f -` U) x)"
        then have "x \<notin> (S \<inter> f -` U)"
          by (metis (no_types, lifting) \<open>U \<subseteq> f ` S\<close> opefSU lcS oo locally_path_connected_open_path_component)
        then show False
          using ** \<open>path_component_set U y \<subseteq> U\<close>  \<open>x \<in> S\<close> \<open>path_component U y (f x)\<close> by blast
      qed
    next
      show "x \<in> path_component_set (S \<inter> f -` U) x"
        by (simp add: \<open>f x \<in> U\<close> \<open>x \<in> S\<close> path_component_refl)
    next
      have contf: "continuous_on S f"
        by (simp add: continuous_on_open oo openin_imp_subset)
      then have "continuous_on (path_component_set (S \<inter> f -` U) x) f"
        by (meson Int_lower1 continuous_on_subset path_component_subset)
      then have "path_connected (f ` path_component_set (S \<inter> f -` U) x)"
        by (simp add: path_connected_continuous_image)
      moreover have "f ` path_component_set (S \<inter> f -` U) x \<subseteq> U"
        using path_component_mem by fastforce
      moreover have "f x \<in> f ` path_component_set (S \<inter> f -` U) x"
        by (force simp: \<open>x \<in> S\<close> \<open>f x \<in> U\<close> path_component_refl_eq)
      ultimately have "f ` (path_component_set (S \<inter> f -` U) x) \<subseteq> path_component_set U (f x)"
        by (meson path_component_maximal)
       also have  "\<dots> \<subseteq> path_component_set U y"
        by (simp add: Uyfx path_component_maximal path_component_subset path_component_sym)
      finally have fC: "f ` (path_component_set (S \<inter> f -` U) x) \<subseteq> path_component_set U y" .
      have cUC: "path_component_set (S \<inter> f -` U) x \<subseteq> (S \<inter> f -` path_component_set U y)"
        using path_component_subset fC by blast
      have "path_component_set (S \<inter> f -` U) x \<subseteq> path_component_set (S \<inter> f -` path_component_set U y) x"
      proof -
        have "\<And>a. path_component_set (path_component_set (S \<inter> f -` U) x) a \<subseteq> path_component_set (S \<inter> f -` path_component_set U y) a"
          using cUC path_component_mono by blast
        then show ?thesis
          using path_component_path_component by blast
      qed
      also have "\<dots> \<subseteq> (S \<inter> f -` path_component_set U y)"
        by (rule path_component_subset)
      finally show "path_component_set (S \<inter> f -` U) x \<subseteq> (S \<inter> f -` path_component_set U y)" .
    qed
  qed
  ultimately show "openin (top_of_set (f ` S)) (path_component_set U y)"
    by metis
qed

subsection\<^marker>\<open>tag unimportant\<close>\<open>Components, continuity, openin, closedin\<close>

lemma continuous_on_components_gen:
 fixes f :: "'a::topological_space \<Rightarrow> 'b::topological_space"
  assumes "\<And>C. C \<in> components S \<Longrightarrow>
              openin (top_of_set S) C \<and> continuous_on C f"
    shows "continuous_on S f"
proof (clarsimp simp: continuous_openin_preimage_eq)
  fix t :: "'b set"
  assume "open t"
  have *: "S \<inter> f -` t = (\<Union>c \<in> components S. c \<inter> f -` t)"
    by auto
  show "openin (top_of_set S) (S \<inter> f -` t)"
    unfolding * using \<open>open t\<close> assms continuous_openin_preimage_gen openin_trans openin_Union by blast
qed

lemma continuous_on_components:
 fixes f :: "'a::topological_space \<Rightarrow> 'b::topological_space"
  assumes "locally connected S " "\<And>C. C \<in> components S \<Longrightarrow> continuous_on C f"
  shows "continuous_on S f"
proof (rule continuous_on_components_gen)
  fix C
  assume "C \<in> components S"
  then show "openin (top_of_set S) C \<and> continuous_on C f"
    by (simp add: assms openin_components_locally_connected)
qed

lemma continuous_on_components_eq:
    "locally connected S
     \<Longrightarrow> (continuous_on S f \<longleftrightarrow> (\<forall>c \<in> components S. continuous_on c f))"
by (meson continuous_on_components continuous_on_subset in_components_subset)

lemma continuous_on_components_open:
 fixes S :: "'a::real_normed_vector set"
  assumes "open S "
          "\<And>c. c \<in> components S \<Longrightarrow> continuous_on c f"
    shows "continuous_on S f"
using continuous_on_components open_imp_locally_connected assms by blast

lemma continuous_on_components_open_eq:
  fixes S :: "'a::real_normed_vector set"
  shows "open S \<Longrightarrow> (continuous_on S f \<longleftrightarrow> (\<forall>c \<in> components S. continuous_on c f))"
using continuous_on_subset in_components_subset
by (blast intro: continuous_on_components_open)

lemma closedin_union_complement_components:
  assumes U: "locally connected U"
      and S: "closedin (top_of_set U) S"
      and cuS: "c \<subseteq> components(U - S)"
    shows "closedin (top_of_set U) (S \<union> \<Union>c)"
proof -
  have di: "(\<And>S T. S \<in> c \<and> T \<in> c' \<Longrightarrow> disjnt S T) \<Longrightarrow> disjnt (\<Union> c) (\<Union> c')" for c'
    by (simp add: disjnt_def) blast
  have "S \<subseteq> U"
    using S closedin_imp_subset by blast
  moreover have "U - S = \<Union>c \<union> \<Union>(components (U - S) - c)"
    by (metis Diff_partition Union_components Union_Un_distrib assms(3))
  moreover have "disjnt (\<Union>c) (\<Union>(components (U - S) - c))"
    apply (rule di)
    by (metis di DiffD1 DiffD2 assms(3) components_nonoverlap disjnt_def subsetCE)
  ultimately have eq: "S \<union> \<Union>c = U - (\<Union>(components(U - S) - c))"
    by (auto simp: disjnt_def)
  have *: "openin (top_of_set U) (\<Union>(components (U - S) - c))"
  proof (rule openin_Union [OF openin_trans [of "U - S"]])
    show "openin (top_of_set (U - S)) T" if "T \<in> components (U - S) - c" for T
      using that by (simp add: U S locally_diff_closed openin_components_locally_connected)
    show "openin (top_of_set U) (U - S)" if "T \<in> components (U - S) - c" for T
      using that by (simp add: openin_diff S)
  qed
  have "closedin (top_of_set U) (U - \<Union> (components (U - S) - c))"
    by (metis closedin_diff closedin_topspace topspace_euclidean_subtopology *)
  then have "openin (top_of_set U) (U - (U - \<Union>(components (U - S) - c)))"
    by (simp add: openin_diff)
  then show ?thesis
    by (force simp: eq closedin_def)
qed

lemma closed_union_complement_components:
  fixes S :: "'a::real_normed_vector set"
  assumes S: "closed S" and c: "c \<subseteq> components(- S)"
    shows "closed(S \<union> \<Union> c)"
proof -
  have "closedin (top_of_set UNIV) (S \<union> \<Union>c)"
    by (metis Compl_eq_Diff_UNIV S c closed_closedin closedin_union_complement_components locally_connected_UNIV subtopology_UNIV)
  then show ?thesis by simp
qed

lemma closedin_Un_complement_component:
  fixes S :: "'a::real_normed_vector set"
  assumes u: "locally connected u"
      and S: "closedin (top_of_set u) S"
      and c: " c \<in> components(u - S)"
    shows "closedin (top_of_set u) (S \<union> c)"
proof -
  have "closedin (top_of_set u) (S \<union> \<Union>{c})"
    using c by (blast intro: closedin_union_complement_components [OF u S])
  then show ?thesis
    by simp
qed

lemma closed_Un_complement_component:
  fixes S :: "'a::real_normed_vector set"
  assumes S: "closed S" and c: " c \<in> components(-S)"
    shows "closed (S \<union> c)"
  by (metis Compl_eq_Diff_UNIV S c closed_closedin closedin_Un_complement_component
      locally_connected_UNIV subtopology_UNIV)


subsection\<open>Existence of isometry between subspaces of same dimension\<close>

lemma isometry_subset_subspace:
  fixes S :: "'a::euclidean_space set"
    and T :: "'b::euclidean_space set"
  assumes S: "subspace S"
      and T: "subspace T"
      and d: "dim S \<le> dim T"
  obtains f where "linear f" "f ` S \<subseteq> T" "\<And>x. x \<in> S \<Longrightarrow> norm(f x) = norm x"
proof -
  obtain B where "B \<subseteq> S" and Borth: "pairwise orthogonal B"
             and B1: "\<And>x. x \<in> B \<Longrightarrow> norm x = 1"
             and "independent B" "finite B" "card B = dim S" "span B = S"
    by (metis orthonormal_basis_subspace [OF S] independent_finite)
  obtain C where "C \<subseteq> T" and Corth: "pairwise orthogonal C"
             and C1:"\<And>x. x \<in> C \<Longrightarrow> norm x = 1"
             and "independent C" "finite C" "card C = dim T" "span C = T"
    by (metis orthonormal_basis_subspace [OF T] independent_finite)
  obtain fb where "fb ` B \<subseteq> C" "inj_on fb B"
    by (metis \<open>card B = dim S\<close> \<open>card C = dim T\<close> \<open>finite B\<close> \<open>finite C\<close> card_le_inj d)
  then have pairwise_orth_fb: "pairwise (\<lambda>v j. orthogonal (fb v) (fb j)) B"
    using Corth unfolding pairwise_def inj_on_def
    by (blast intro: orthogonal_clauses)
  obtain f where "linear f" and ffb: "\<And>x. x \<in> B \<Longrightarrow> f x = fb x"
    using linear_independent_extend \<open>independent B\<close> by fastforce
  have "span (f ` B) \<subseteq> span C"
    by (metis \<open>fb ` B \<subseteq> C\<close> ffb image_cong span_mono)
  then have "f ` S \<subseteq> T"
    unfolding \<open>span B = S\<close> \<open>span C = T\<close> span_linear_image[OF \<open>linear f\<close>] .
  have [simp]: "\<And>x. x \<in> B \<Longrightarrow> norm (fb x) = norm x"
    using B1 C1 \<open>fb ` B \<subseteq> C\<close> by auto
  have "norm (f x) = norm x" if "x \<in> S" for x
  proof -
    interpret linear f by fact
    obtain a where x: "x = (\<Sum>v \<in> B. a v *\<^sub>R v)"
      using \<open>finite B\<close> \<open>span B = S\<close> \<open>x \<in> S\<close> span_finite by fastforce
    have "norm (f x)^2 = norm (\<Sum>v\<in>B. a v *\<^sub>R fb v)^2" by (simp add: sum scale ffb x)
    also have "\<dots> = (\<Sum>v\<in>B. norm ((a v *\<^sub>R fb v))^2)"
    proof (rule norm_sum_Pythagorean [OF \<open>finite B\<close>])
      show "pairwise (\<lambda>v j. orthogonal (a v *\<^sub>R fb v) (a j *\<^sub>R fb j)) B"
        by (rule pairwise_ortho_scaleR [OF pairwise_orth_fb])
    qed
    also have "\<dots> = norm x ^2"
      by (simp add: x pairwise_ortho_scaleR Borth norm_sum_Pythagorean [OF \<open>finite B\<close>])
    finally show ?thesis
      by (simp add: norm_eq_sqrt_inner)
  qed
  then show ?thesis
    by (rule that [OF \<open>linear f\<close> \<open>f ` S \<subseteq> T\<close>])
qed

proposition isometries_subspaces:
  fixes S :: "'a::euclidean_space set"
    and T :: "'b::euclidean_space set"
  assumes S: "subspace S"
      and T: "subspace T"
      and d: "dim S = dim T"
  obtains f g where "linear f" "linear g" "f ` S = T" "g ` T = S"
                    "\<And>x. x \<in> S \<Longrightarrow> norm(f x) = norm x"
                    "\<And>x. x \<in> T \<Longrightarrow> norm(g x) = norm x"
                    "\<And>x. x \<in> S \<Longrightarrow> g(f x) = x"
                    "\<And>x. x \<in> T \<Longrightarrow> f(g x) = x"
proof -
  obtain B where "B \<subseteq> S" and Borth: "pairwise orthogonal B"
             and B1: "\<And>x. x \<in> B \<Longrightarrow> norm x = 1"
             and "independent B" "finite B" "card B = dim S" "span B = S"
    by (metis orthonormal_basis_subspace [OF S] independent_finite)
  obtain C where "C \<subseteq> T" and Corth: "pairwise orthogonal C"
             and C1:"\<And>x. x \<in> C \<Longrightarrow> norm x = 1"
             and "independent C" "finite C" "card C = dim T" "span C = T"
    by (metis orthonormal_basis_subspace [OF T] independent_finite)
  obtain fb where "bij_betw fb B C"
    by (metis \<open>finite B\<close> \<open>finite C\<close> bij_betw_iff_card \<open>card B = dim S\<close> \<open>card C = dim T\<close> d)
  then have pairwise_orth_fb: "pairwise (\<lambda>v j. orthogonal (fb v) (fb j)) B"
    using Corth unfolding pairwise_def inj_on_def bij_betw_def
    by (blast intro: orthogonal_clauses)
  obtain f where "linear f" and ffb: "\<And>x. x \<in> B \<Longrightarrow> f x = fb x"
    using linear_independent_extend \<open>independent B\<close> by fastforce
  interpret f: linear f by fact
  define gb where "gb \<equiv> inv_into B fb"
  then have pairwise_orth_gb: "pairwise (\<lambda>v j. orthogonal (gb v) (gb j)) C"
    using Borth \<open>bij_betw fb B C\<close> unfolding pairwise_def bij_betw_def by force
  obtain g where "linear g" and ggb: "\<And>x. x \<in> C \<Longrightarrow> g x = gb x"
    using linear_independent_extend \<open>independent C\<close> by fastforce
  interpret g: linear g by fact
  have "span (f ` B) \<subseteq> span C"
    by (metis \<open>bij_betw fb B C\<close> bij_betw_imp_surj_on eq_iff ffb image_cong)
  then have "f ` S \<subseteq> T"
    unfolding \<open>span B = S\<close> \<open>span C = T\<close> span_linear_image[OF \<open>linear f\<close>] .
  have [simp]: "\<And>x. x \<in> B \<Longrightarrow> norm (fb x) = norm x"
    using B1 C1 \<open>bij_betw fb B C\<close> bij_betw_imp_surj_on by fastforce
  have f [simp]: "norm (f x) = norm x" "g (f x) = x" if "x \<in> S" for x
  proof -
    obtain a where x: "x = (\<Sum>v \<in> B. a v *\<^sub>R v)"
      using \<open>finite B\<close> \<open>span B = S\<close> \<open>x \<in> S\<close> span_finite by fastforce
    have "f x = (\<Sum>v \<in> B. f (a v *\<^sub>R v))"
      using linear_sum [OF \<open>linear f\<close>] x by auto
    also have "\<dots> = (\<Sum>v \<in> B. a v *\<^sub>R f v)"
      by (simp add: f.sum f.scale)
    also have "\<dots> = (\<Sum>v \<in> B. a v *\<^sub>R fb v)"
      by (simp add: ffb cong: sum.cong)
    finally have *: "f x = (\<Sum>v\<in>B. a v *\<^sub>R fb v)" .
    then have "(norm (f x))\<^sup>2 = (norm (\<Sum>v\<in>B. a v *\<^sub>R fb v))\<^sup>2" by simp
    also have "\<dots> = (\<Sum>v\<in>B. norm ((a v *\<^sub>R fb v))^2)"
    proof (rule norm_sum_Pythagorean [OF \<open>finite B\<close>])
      show "pairwise (\<lambda>v j. orthogonal (a v *\<^sub>R fb v) (a j *\<^sub>R fb j)) B"
        by (rule pairwise_ortho_scaleR [OF pairwise_orth_fb])
    qed
    also have "\<dots> = (norm x)\<^sup>2"
      by (simp add: x pairwise_ortho_scaleR Borth norm_sum_Pythagorean [OF \<open>finite B\<close>])
    finally show "norm (f x) = norm x"
      by (simp add: norm_eq_sqrt_inner)
    have "g (f x) = g (\<Sum>v\<in>B. a v *\<^sub>R fb v)" by (simp add: *)
    also have "\<dots> = (\<Sum>v\<in>B. g (a v *\<^sub>R fb v))"
      by (simp add: g.sum g.scale)
    also have "\<dots> = (\<Sum>v\<in>B. a v *\<^sub>R g (fb v))"
      by (simp add: g.scale)
    also have "\<dots> = (\<Sum>v\<in>B. a v *\<^sub>R v)"
    proof (rule sum.cong [OF refl])
      show "a x *\<^sub>R g (fb x) = a x *\<^sub>R x" if "x \<in> B" for x
        using that \<open>bij_betw fb B C\<close> bij_betwE bij_betw_inv_into_left gb_def ggb by fastforce
    qed
    also have "\<dots> = x"
      using x by blast
    finally show "g (f x) = x" .
  qed
  have [simp]: "\<And>x. x \<in> C \<Longrightarrow> norm (gb x) = norm x"
    by (metis B1 C1 \<open>bij_betw fb B C\<close> bij_betw_imp_surj_on gb_def inv_into_into)
  have g [simp]: "f (g x) = x" if "x \<in> T" for x
  proof -
    obtain a where x: "x = (\<Sum>v \<in> C. a v *\<^sub>R v)"
      using \<open>finite C\<close> \<open>span C = T\<close> \<open>x \<in> T\<close> span_finite by fastforce
    have "g x = (\<Sum>v \<in> C. g (a v *\<^sub>R v))"
      by (simp add: x g.sum)
    also have "\<dots> = (\<Sum>v \<in> C. a v *\<^sub>R g v)"
      by (simp add: g.scale)
    also have "\<dots> = (\<Sum>v \<in> C. a v *\<^sub>R gb v)"
      by (simp add: ggb cong: sum.cong)
    finally have "f (g x) = f (\<Sum>v\<in>C. a v *\<^sub>R gb v)" by simp
    also have "\<dots> = (\<Sum>v\<in>C. f (a v *\<^sub>R gb v))"
      by (simp add: f.scale f.sum)
    also have "\<dots> = (\<Sum>v\<in>C. a v *\<^sub>R f (gb v))"
      by (simp add: f.scale f.sum)
    also have "\<dots> = (\<Sum>v\<in>C. a v *\<^sub>R v)"
      using \<open>bij_betw fb B C\<close>
      by (simp add: bij_betw_def gb_def bij_betw_inv_into_right ffb inv_into_into)
    also have "\<dots> = x"
      using x by blast
    finally show "f (g x) = x" .
  qed
  have gim: "g ` T = S"
    by (metis (full_types) S T \<open>f ` S \<subseteq> T\<close> d dim_eq_span dim_image_le f(2) g.linear_axioms
        image_iff linear_subspace_image span_eq_iff subset_iff)
  have fim: "f ` S = T"
    using \<open>g ` T = S\<close> image_iff by fastforce
  have [simp]: "norm (g x) = norm x" if "x \<in> T" for x
    using fim that by auto
  show ?thesis
    by (rule that [OF \<open>linear f\<close> \<open>linear g\<close>]) (simp_all add: fim gim)
qed

corollary isometry_subspaces:
  fixes S :: "'a::euclidean_space set"
    and T :: "'b::euclidean_space set"
  assumes S: "subspace S"
      and T: "subspace T"
      and d: "dim S = dim T"
  obtains f where "linear f" "f ` S = T" "\<And>x. x \<in> S \<Longrightarrow> norm(f x) = norm x"
using isometries_subspaces [OF assms]
by metis

corollary isomorphisms_UNIV_UNIV:
  assumes "DIM('M) = DIM('N)"
  obtains f::"'M::euclidean_space \<Rightarrow>'N::euclidean_space" and g
  where "linear f" "linear g"
                    "\<And>x. norm(f x) = norm x" "\<And>y. norm(g y) = norm y"
                    "\<And>x. g (f x) = x" "\<And>y. f(g y) = y"
  using assms by (auto intro: isometries_subspaces [of "UNIV::'M set" "UNIV::'N set"])

lemma homeomorphic_subspaces:
  fixes S :: "'a::euclidean_space set"
    and T :: "'b::euclidean_space set"
  assumes S: "subspace S"
      and T: "subspace T"
      and d: "dim S = dim T"
    shows "S homeomorphic T"
proof -
  obtain f g where "linear f" "linear g" "f ` S = T" "g ` T = S"
                   "\<And>x. x \<in> S \<Longrightarrow> g(f x) = x" "\<And>x. x \<in> T \<Longrightarrow> f(g x) = x"
    by (blast intro: isometries_subspaces [OF assms])
  then show ?thesis
    unfolding homeomorphic_def homeomorphism_def
    apply (rule_tac x=f in exI, rule_tac x=g in exI)
    apply (auto simp: linear_continuous_on linear_conv_bounded_linear)
    done
qed

lemma homeomorphic_affine_sets:
  assumes "affine S" "affine T" "aff_dim S = aff_dim T"
    shows "S homeomorphic T"
proof (cases "S = {} \<or> T = {}")
  case True  with assms aff_dim_empty homeomorphic_empty show ?thesis
    by metis
next
  case False
  then obtain a b where ab: "a \<in> S" "b \<in> T" by auto
  then have ss: "subspace ((+) (- a) ` S)" "subspace ((+) (- b) ` T)"
    using affine_diffs_subspace assms by blast+
  have dd: "dim ((+) (- a) ` S) = dim ((+) (- b) ` T)"
    using assms ab  by (simp add: aff_dim_eq_dim  [OF hull_inc] image_def)
  have "S homeomorphic ((+) (- a) ` S)"
    by (fact homeomorphic_translation)
  also have "\<dots> homeomorphic ((+) (- b) ` T)"
    by (rule homeomorphic_subspaces [OF ss dd])
  also have "\<dots> homeomorphic T"
    using homeomorphic_translation [of T "- b"] by (simp add: homeomorphic_sym [of T])
  finally show ?thesis .
qed


subsection\<open>Retracts, in a general sense, preserve (co)homotopic triviality)\<close>

locale\<^marker>\<open>tag important\<close> Retracts =
  fixes s h t k
  assumes conth: "continuous_on s h"
      and imh: "h ` s = t"
      and contk: "continuous_on t k"
      and imk: "k ` t \<subseteq> s"
      and idhk: "\<And>y. y \<in> t \<Longrightarrow> h(k y) = y"

begin

lemma homotopically_trivial_retraction_gen:
  assumes P: "\<And>f. \<lbrakk>continuous_on U f; f ` U \<subseteq> t; Q f\<rbrakk> \<Longrightarrow> P(k \<circ> f)"
      and Q: "\<And>f. \<lbrakk>continuous_on U f; f ` U \<subseteq> s; P f\<rbrakk> \<Longrightarrow> Q(h \<circ> f)"
      and Qeq: "\<And>h k. (\<And>x. x \<in> U \<Longrightarrow> h x = k x) \<Longrightarrow> Q h = Q k"
      and hom: "\<And>f g. \<lbrakk>continuous_on U f; f ` U \<subseteq> s; P f;
                       continuous_on U g; g ` U \<subseteq> s; P g\<rbrakk>
                       \<Longrightarrow> homotopic_with_canon P U s f g"
      and contf: "continuous_on U f" and imf: "f ` U \<subseteq> t" and Qf: "Q f"
      and contg: "continuous_on U g" and img: "g ` U \<subseteq> t" and Qg: "Q g"
    shows "homotopic_with_canon Q U t f g"
proof -
  have "continuous_on U (k \<circ> f)"
    using contf continuous_on_compose continuous_on_subset contk imf by blast
  moreover have "(k \<circ> f) ` U \<subseteq> s"
    using imf imk by fastforce
  moreover have "P (k \<circ> f)"
    by (simp add: P Qf contf imf)
  moreover have "continuous_on U (k \<circ> g)"
    using contg continuous_on_compose continuous_on_subset contk img by blast
  moreover have "(k \<circ> g) ` U \<subseteq> s"
    using img imk by fastforce
  moreover have "P (k \<circ> g)"
    by (simp add: P Qg contg img)
  ultimately have "homotopic_with_canon P U s (k \<circ> f) (k \<circ> g)"
    by (rule hom)
  then have "homotopic_with_canon Q U t (h \<circ> (k \<circ> f)) (h \<circ> (k \<circ> g))"
    apply (rule homotopic_with_compose_continuous_left [OF homotopic_with_mono])
    using Q by (auto simp: conth imh)
  then show ?thesis
  proof (rule homotopic_with_eq; simp)
    show "\<And>h k. (\<And>x. x \<in> U \<Longrightarrow> h x = k x) \<Longrightarrow> Q h = Q k"
      using Qeq topspace_euclidean_subtopology by blast
    show "\<And>x. x \<in> U \<Longrightarrow> f x = h (k (f x))" "\<And>x. x \<in> U \<Longrightarrow> g x = h (k (g x))"
      using idhk imf img by auto
  qed 
qed

lemma homotopically_trivial_retraction_null_gen:
  assumes P: "\<And>f. \<lbrakk>continuous_on U f; f ` U \<subseteq> t; Q f\<rbrakk> \<Longrightarrow> P(k \<circ> f)"
      and Q: "\<And>f. \<lbrakk>continuous_on U f; f ` U \<subseteq> s; P f\<rbrakk> \<Longrightarrow> Q(h \<circ> f)"
      and Qeq: "\<And>h k. (\<And>x. x \<in> U \<Longrightarrow> h x = k x) \<Longrightarrow> Q h = Q k"
      and hom: "\<And>f. \<lbrakk>continuous_on U f; f ` U \<subseteq> s; P f\<rbrakk>
                     \<Longrightarrow> \<exists>c. homotopic_with_canon P U s f (\<lambda>x. c)"
      and contf: "continuous_on U f" and imf:"f ` U \<subseteq> t" and Qf: "Q f"
  obtains c where "homotopic_with_canon Q U t f (\<lambda>x. c)"
proof -
  have feq: "\<And>x. x \<in> U \<Longrightarrow> (h \<circ> (k \<circ> f)) x = f x" using idhk imf by auto
  have "continuous_on U (k \<circ> f)"
    using contf continuous_on_compose continuous_on_subset contk imf by blast
  moreover have "(k \<circ> f) ` U \<subseteq> s"
    using imf imk by fastforce
  moreover have "P (k \<circ> f)"
    by (simp add: P Qf contf imf)
  ultimately obtain c where "homotopic_with_canon P U s (k \<circ> f) (\<lambda>x. c)"
    by (metis hom)
  then have "homotopic_with_canon Q U t (h \<circ> (k \<circ> f)) (h \<circ> (\<lambda>x. c))"
    apply (rule homotopic_with_compose_continuous_left [OF homotopic_with_mono])
    using Q by (auto simp: conth imh)
  then have "homotopic_with_canon Q U t f (\<lambda>x. h c)"
  proof (rule homotopic_with_eq)
    show "\<And>x. x \<in> topspace (top_of_set U) \<Longrightarrow> f x = (h \<circ> (k \<circ> f)) x"
      using feq by auto
    show "\<And>h k. (\<And>x. x \<in> topspace (top_of_set U) \<Longrightarrow> h x = k x) \<Longrightarrow> Q h = Q k"
      using Qeq topspace_euclidean_subtopology by blast
  qed auto
  then show ?thesis
    using that by blast
qed

lemma cohomotopically_trivial_retraction_gen:
  assumes P: "\<And>f. \<lbrakk>continuous_on t f; f ` t \<subseteq> U; Q f\<rbrakk> \<Longrightarrow> P(f \<circ> h)"
      and Q: "\<And>f. \<lbrakk>continuous_on s f; f ` s \<subseteq> U; P f\<rbrakk> \<Longrightarrow> Q(f \<circ> k)"
      and Qeq: "\<And>h k. (\<And>x. x \<in> t \<Longrightarrow> h x = k x) \<Longrightarrow> Q h = Q k"
      and hom: "\<And>f g. \<lbrakk>continuous_on s f; f ` s \<subseteq> U; P f;
                       continuous_on s g; g ` s \<subseteq> U; P g\<rbrakk>
                       \<Longrightarrow> homotopic_with_canon P s U f g"
      and contf: "continuous_on t f" and imf: "f ` t \<subseteq> U" and Qf: "Q f"
      and contg: "continuous_on t g" and img: "g ` t \<subseteq> U" and Qg: "Q g"
    shows "homotopic_with_canon Q t U f g"
proof -
  have feq: "\<And>x. x \<in> t \<Longrightarrow> (f \<circ> h \<circ> k) x = f x" using idhk imf by auto
  have geq: "\<And>x. x \<in> t \<Longrightarrow> (g \<circ> h \<circ> k) x = g x" using idhk img by auto
  have "continuous_on s (f \<circ> h)"
    using contf conth continuous_on_compose imh by blast
  moreover have "(f \<circ> h) ` s \<subseteq> U"
    using imf imh by fastforce
  moreover have "P (f \<circ> h)"
    by (simp add: P Qf contf imf)
  moreover have "continuous_on s (g \<circ> h)"
    using contg continuous_on_compose continuous_on_subset conth imh by blast
  moreover have "(g \<circ> h) ` s \<subseteq> U"
    using img imh by fastforce
  moreover have "P (g \<circ> h)"
    by (simp add: P Qg contg img)
  ultimately have "homotopic_with_canon P s U (f \<circ> h) (g \<circ> h)"
    by (rule hom)
  then have "homotopic_with_canon Q t U (f \<circ> h \<circ> k) (g \<circ> h \<circ> k)"
    apply (rule homotopic_with_compose_continuous_right [OF homotopic_with_mono])
    using Q by (auto simp: contk imk)
  then show ?thesis
  proof (rule homotopic_with_eq)
    show "f x = (f \<circ> h \<circ> k) x" "g x = (g \<circ> h \<circ> k) x" 
      if "x \<in> topspace (top_of_set t)" for x
      using feq geq that by force+
  qed (use Qeq topspace_euclidean_subtopology in blast)
qed

lemma cohomotopically_trivial_retraction_null_gen:
  assumes P: "\<And>f. \<lbrakk>continuous_on t f; f ` t \<subseteq> U; Q f\<rbrakk> \<Longrightarrow> P(f \<circ> h)"
      and Q: "\<And>f. \<lbrakk>continuous_on s f; f ` s \<subseteq> U; P f\<rbrakk> \<Longrightarrow> Q(f \<circ> k)"
      and Qeq: "\<And>h k. (\<And>x. x \<in> t \<Longrightarrow> h x = k x) \<Longrightarrow> Q h = Q k"
      and hom: "\<And>f g. \<lbrakk>continuous_on s f; f ` s \<subseteq> U; P f\<rbrakk>
                       \<Longrightarrow> \<exists>c. homotopic_with_canon P s U f (\<lambda>x. c)"
      and contf: "continuous_on t f" and imf: "f ` t \<subseteq> U" and Qf: "Q f"
  obtains c where "homotopic_with_canon Q t U f (\<lambda>x. c)"
proof -
  have feq: "\<And>x. x \<in> t \<Longrightarrow> (f \<circ> h \<circ> k) x = f x" using idhk imf by auto
  have "continuous_on s (f \<circ> h)"
    using contf conth continuous_on_compose imh by blast
  moreover have "(f \<circ> h) ` s \<subseteq> U"
    using imf imh by fastforce
  moreover have "P (f \<circ> h)"
    by (simp add: P Qf contf imf)
  ultimately obtain c where "homotopic_with_canon P s U (f \<circ> h) (\<lambda>x. c)"
    by (metis hom)
  then have \<section>: "homotopic_with_canon Q t U (f \<circ> h \<circ> k) ((\<lambda>x. c) \<circ> k)"
  proof (rule homotopic_with_compose_continuous_right [OF homotopic_with_mono])
    show "\<And>h. \<lbrakk>continuous_map (top_of_set s) (top_of_set U) h; P h\<rbrakk> \<Longrightarrow> Q (h \<circ> k)"
      using Q by auto
  qed (auto simp: contk imk)
  moreover have "homotopic_with_canon Q t U f (\<lambda>x. c)"
    using homotopic_with_eq [OF \<section>] feq Qeq by fastforce
  ultimately show ?thesis 
    using that by blast
qed

end

lemma simply_connected_retraction_gen:
  shows "\<lbrakk>simply_connected S; continuous_on S h; h ` S = T;
          continuous_on T k; k ` T \<subseteq> S; \<And>y. y \<in> T \<Longrightarrow> h(k y) = y\<rbrakk>
        \<Longrightarrow> simply_connected T"
apply (simp add: simply_connected_def path_def path_image_def homotopic_loops_def, clarify)
apply (rule Retracts.homotopically_trivial_retraction_gen
        [of S h _ k _ "\<lambda>p. pathfinish p = pathstart p"  "\<lambda>p. pathfinish p = pathstart p"])
apply (simp_all add: Retracts_def pathfinish_def pathstart_def)
done

lemma homeomorphic_simply_connected:
    "\<lbrakk>S homeomorphic T; simply_connected S\<rbrakk> \<Longrightarrow> simply_connected T"
  by (auto simp: homeomorphic_def homeomorphism_def intro: simply_connected_retraction_gen)

lemma homeomorphic_simply_connected_eq:
    "S homeomorphic T \<Longrightarrow> (simply_connected S \<longleftrightarrow> simply_connected T)"
  by (metis homeomorphic_simply_connected homeomorphic_sym)


subsection\<open>Homotopy equivalence\<close>

subsection\<open>Homotopy equivalence of topological spaces.\<close>

definition\<^marker>\<open>tag important\<close> homotopy_equivalent_space
             (infix "homotopy'_equivalent'_space" 50)
  where "X homotopy_equivalent_space Y \<equiv>
        (\<exists>f g. continuous_map X Y f \<and>
              continuous_map Y X g \<and>
              homotopic_with (\<lambda>x. True) X X (g \<circ> f) id \<and>
              homotopic_with (\<lambda>x. True) Y Y (f \<circ> g) id)"

lemma homeomorphic_imp_homotopy_equivalent_space:
  "X homeomorphic_space Y \<Longrightarrow> X homotopy_equivalent_space Y"
  unfolding homeomorphic_space_def homotopy_equivalent_space_def
  apply (erule ex_forward)+
  by (simp add: homotopic_with_equal homotopic_with_sym homeomorphic_maps_def)

lemma homotopy_equivalent_space_refl:
   "X homotopy_equivalent_space X"
  by (simp add: homeomorphic_imp_homotopy_equivalent_space homeomorphic_space_refl)

lemma homotopy_equivalent_space_sym:
   "X homotopy_equivalent_space Y \<longleftrightarrow> Y homotopy_equivalent_space X"
  by (meson homotopy_equivalent_space_def)

lemma homotopy_eqv_trans [trans]:
  assumes 1: "X homotopy_equivalent_space Y" and 2: "Y homotopy_equivalent_space U"
    shows "X homotopy_equivalent_space U"
proof -
  obtain f1 g1 where f1: "continuous_map X Y f1"
                 and g1: "continuous_map Y X g1"
                 and hom1: "homotopic_with (\<lambda>x. True) X X (g1 \<circ> f1) id"
                           "homotopic_with (\<lambda>x. True) Y Y (f1 \<circ> g1) id"
    using 1 by (auto simp: homotopy_equivalent_space_def)
  obtain f2 g2 where f2: "continuous_map Y U f2"
                 and g2: "continuous_map U Y g2"
                 and hom2: "homotopic_with (\<lambda>x. True) Y Y (g2 \<circ> f2) id"
                           "homotopic_with (\<lambda>x. True) U U (f2 \<circ> g2) id"
    using 2 by (auto simp: homotopy_equivalent_space_def)
  have "homotopic_with (\<lambda>f. True) X Y (g2 \<circ> f2 \<circ> f1) (id \<circ> f1)"
    using f1 hom2(1) homotopic_with_compose_continuous_map_right by metis
  then have "homotopic_with (\<lambda>f. True) X Y (g2 \<circ> (f2 \<circ> f1)) (id \<circ> f1)"
    by (simp add: o_assoc)
  then have "homotopic_with (\<lambda>x. True) X X
         (g1 \<circ> (g2 \<circ> (f2 \<circ> f1))) (g1 \<circ> (id \<circ> f1))"
    by (simp add: g1 homotopic_with_compose_continuous_map_left)
  moreover have "homotopic_with (\<lambda>x. True) X X (g1 \<circ> id \<circ> f1) id"
    using hom1 by simp
  ultimately have SS: "homotopic_with (\<lambda>x. True) X X (g1 \<circ> g2 \<circ> (f2 \<circ> f1)) id"
    by (metis comp_assoc homotopic_with_trans id_comp)
  have "homotopic_with (\<lambda>f. True) U Y (f1 \<circ> g1 \<circ> g2) (id \<circ> g2)"
    using g2 hom1(2) homotopic_with_compose_continuous_map_right by fastforce
  then have "homotopic_with (\<lambda>f. True) U Y (f1 \<circ> (g1 \<circ> g2)) (id \<circ> g2)"
    by (simp add: o_assoc)
  then have "homotopic_with (\<lambda>x. True) U U
         (f2 \<circ> (f1 \<circ> (g1 \<circ> g2))) (f2 \<circ> (id \<circ> g2))"
    by (simp add: f2 homotopic_with_compose_continuous_map_left)
  moreover have "homotopic_with (\<lambda>x. True) U U (f2 \<circ> id \<circ> g2) id"
    using hom2 by simp
  ultimately have UU: "homotopic_with (\<lambda>x. True) U U (f2 \<circ> f1 \<circ> (g1 \<circ> g2)) id"
    by (simp add: fun.map_comp hom2(2) homotopic_with_trans)
  show ?thesis
    unfolding homotopy_equivalent_space_def
    by (blast intro: f1 f2 g1 g2 continuous_map_compose SS UU)
qed

lemma deformation_retraction_imp_homotopy_equivalent_space:
  "\<lbrakk>homotopic_with (\<lambda>x. True) X X (s \<circ> r) id; retraction_maps X Y r s\<rbrakk>
    \<Longrightarrow> X homotopy_equivalent_space Y"
  unfolding homotopy_equivalent_space_def retraction_maps_def
  using homotopic_with_id2 by fastforce

lemma deformation_retract_imp_homotopy_equivalent_space:
   "\<lbrakk>homotopic_with (\<lambda>x. True) X X r id; retraction_maps X Y r id\<rbrakk>
    \<Longrightarrow> X homotopy_equivalent_space Y"
  using deformation_retraction_imp_homotopy_equivalent_space by force

lemma deformation_retract_of_space:
  "S \<subseteq> topspace X \<and>
   (\<exists>r. homotopic_with (\<lambda>x. True) X X id r \<and> retraction_maps X (subtopology X S) r id) \<longleftrightarrow>
   S retract_of_space X \<and> (\<exists>f. homotopic_with (\<lambda>x. True) X X id f \<and> f ` (topspace X) \<subseteq> S)"
proof (cases "S \<subseteq> topspace X")
  case True
  moreover have "(\<exists>r. homotopic_with (\<lambda>x. True) X X id r \<and> retraction_maps X (subtopology X S) r id)
             \<longleftrightarrow> (S retract_of_space X \<and> (\<exists>f. homotopic_with (\<lambda>x. True) X X id f \<and> f ` topspace X \<subseteq> S))"
    unfolding retract_of_space_def
  proof safe
    fix f r
    assume f: "homotopic_with (\<lambda>x. True) X X id f"
      and fS: "f ` topspace X \<subseteq> S"
      and r: "continuous_map X (subtopology X S) r"
      and req: "\<forall>x\<in>S. r x = x"
    show "\<exists>r. homotopic_with (\<lambda>x. True) X X id r \<and> retraction_maps X (subtopology X S) r id"
    proof (intro exI conjI)
      have "homotopic_with (\<lambda>x. True) X X f r"
        proof (rule homotopic_with_eq)
          show "homotopic_with (\<lambda>x. True) X X (r \<circ> f) (r \<circ> id)"
            by (metis continuous_map_into_fulltopology f homotopic_with_compose_continuous_map_left homotopic_with_symD r)
          show "f x = (r \<circ> f) x" if "x \<in> topspace X" for x
            using that fS req by auto
        qed auto
      then show "homotopic_with (\<lambda>x. True) X X id r"
        by (rule homotopic_with_trans [OF f])
    next
      show "retraction_maps X (subtopology X S) r id"
        by (simp add: r req retraction_maps_def)
    qed
  qed (use True in \<open>auto simp: retraction_maps_def topspace_subtopology_subset continuous_map_in_subtopology\<close>)
  ultimately show ?thesis by simp
qed (auto simp: retract_of_space_def retraction_maps_def)



subsection\<open>Contractible spaces\<close>

text\<open>The definition (which agrees with "contractible" on subsets of Euclidean space)
is a little cryptic because we don't in fact assume that the constant "a" is in the space.
This forces the convention that the empty space / set is contractible, avoiding some special cases. \<close>

definition contractible_space where
  "contractible_space X \<equiv> \<exists>a. homotopic_with (\<lambda>x. True) X X id (\<lambda>x. a)"

lemma contractible_space_top_of_set [simp]:"contractible_space (top_of_set S) \<longleftrightarrow> contractible S"
  by (auto simp: contractible_space_def contractible_def)

lemma contractible_space_empty:
   "topspace X = {} \<Longrightarrow> contractible_space X"
  unfolding contractible_space_def homotopic_with_def
  apply (rule_tac x=undefined in exI)
  apply (rule_tac x="\<lambda>(t,x). if t = 0 then x else undefined" in exI)
  apply (auto simp: continuous_map_on_empty)
  done

lemma contractible_space_singleton:
  "topspace X = {a} \<Longrightarrow> contractible_space X"
  unfolding contractible_space_def homotopic_with_def
  apply (rule_tac x=a in exI)
  apply (rule_tac x="\<lambda>(t,x). if t = 0 then x else a" in exI)
  apply (auto intro: continuous_map_eq [where f = "\<lambda>z. a"])
  done

lemma contractible_space_subset_singleton:
   "topspace X \<subseteq> {a} \<Longrightarrow> contractible_space X"
  by (meson contractible_space_empty contractible_space_singleton subset_singletonD)

lemma contractible_space_subtopology_singleton:
   "contractible_space(subtopology X {a})"
  by (meson contractible_space_subset_singleton insert_subset path_connectedin_singleton path_connectedin_subtopology subsetI)

lemma contractible_space:
   "contractible_space X \<longleftrightarrow>
        topspace X = {} \<or>
        (\<exists>a \<in> topspace X. homotopic_with (\<lambda>x. True) X X id (\<lambda>x. a))"
proof (cases "topspace X = {}")
  case False
  then show ?thesis
    using homotopic_with_imp_continuous_maps  by (fastforce simp: contractible_space_def)
qed (simp add: contractible_space_empty)

lemma contractible_imp_path_connected_space:
  assumes "contractible_space X" shows "path_connected_space X"
proof (cases "topspace X = {}")
  case False
  have *: "path_connected_space X"
    if "a \<in> topspace X" and conth: "continuous_map (prod_topology (top_of_set {0..1}) X) X h"
      and h: "\<forall>x. h (0, x) = x" "\<forall>x. h (1, x) = a"
    for a and h :: "real \<times> 'a \<Rightarrow> 'a"
  proof -
    have "path_component_of X b a" if "b \<in> topspace X" for b
      unfolding path_component_of_def
    proof (intro exI conjI)
      let ?g = "h \<circ> (\<lambda>x. (x,b))"
      show "pathin X ?g"
        unfolding pathin_def
      proof (rule continuous_map_compose [OF _ conth])
        show "continuous_map (top_of_set {0..1}) (prod_topology (top_of_set {0..1}) X) (\<lambda>x. (x, b))"
          using that by (auto intro!: continuous_intros)
      qed
    qed (use h in auto)
  then show ?thesis
    by (metis path_component_of_equiv path_connected_space_iff_path_component)
  qed
  show ?thesis
    using assms False by (auto simp: contractible_space homotopic_with_def *)
qed (simp add: path_connected_space_topspace_empty)

lemma contractible_imp_connected_space:
   "contractible_space X \<Longrightarrow> connected_space X"
  by (simp add: contractible_imp_path_connected_space path_connected_imp_connected_space)

lemma contractible_space_alt:
   "contractible_space X \<longleftrightarrow> (\<forall>a \<in> topspace X. homotopic_with (\<lambda>x. True) X X id (\<lambda>x. a))" (is "?lhs = ?rhs")
proof
  assume X: ?lhs
  then obtain a where a: "homotopic_with (\<lambda>x. True) X X id (\<lambda>x. a)"
    by (auto simp: contractible_space_def)
  show ?rhs
  proof
    show "homotopic_with (\<lambda>x. True) X X id (\<lambda>x. b)" if "b \<in> topspace X" for b
    proof (rule homotopic_with_trans [OF a])
      show "homotopic_with (\<lambda>x. True) X X (\<lambda>x. a) (\<lambda>x. b)"
        using homotopic_constant_maps path_connected_space_imp_path_component_of
        by (metis (full_types) X a continuous_map_const contractible_imp_path_connected_space homotopic_with_imp_continuous_maps that)
    qed
  qed
next
  assume R: ?rhs
  then show ?lhs
    unfolding contractible_space_def by (metis equals0I homotopic_on_emptyI)
qed


lemma compose_const [simp]: "f \<circ> (\<lambda>x. a) = (\<lambda>x. f a)" "(\<lambda>x. a) \<circ> g = (\<lambda>x. a)"
  by (simp_all add: o_def)

lemma nullhomotopic_through_contractible_space:
  assumes f: "continuous_map X Y f" and g: "continuous_map Y Z g" and Y: "contractible_space Y"
  obtains c where "homotopic_with (\<lambda>h. True) X Z (g \<circ> f) (\<lambda>x. c)"
proof -
  obtain b where b: "homotopic_with (\<lambda>x. True) Y Y id (\<lambda>x. b)"
    using Y by (auto simp: contractible_space_def)
  show thesis
    using homotopic_with_compose_continuous_map_right
           [OF homotopic_with_compose_continuous_map_left [OF b g] f]
    by (force simp add: that)
qed

lemma nullhomotopic_into_contractible_space:
  assumes f: "continuous_map X Y f" and Y: "contractible_space Y"
  obtains c where "homotopic_with (\<lambda>h. True) X Y f (\<lambda>x. c)"
  using nullhomotopic_through_contractible_space [OF f _ Y]
  by (metis continuous_map_id id_comp)

lemma nullhomotopic_from_contractible_space:
  assumes f: "continuous_map X Y f" and X: "contractible_space X"
  obtains c where "homotopic_with (\<lambda>h. True) X Y f (\<lambda>x. c)"
  using nullhomotopic_through_contractible_space [OF _ f X]
  by (metis comp_id continuous_map_id)

lemma homotopy_dominated_contractibility:
  assumes f: "continuous_map X Y f" and g: "continuous_map Y X g"
    and hom: "homotopic_with (\<lambda>x. True) Y Y (f \<circ> g) id" and X: "contractible_space X"
  shows "contractible_space Y"
proof -
  obtain c where c: "homotopic_with (\<lambda>h. True) X Y f (\<lambda>x. c)"
    using nullhomotopic_from_contractible_space [OF f X] .
  have "homotopic_with (\<lambda>x. True) Y Y (f \<circ> g) (\<lambda>x. c)"
    using homotopic_with_compose_continuous_map_right [OF c g] by fastforce
  then have "homotopic_with (\<lambda>x. True) Y Y id (\<lambda>x. c)"
    using homotopic_with_trans [OF _ hom] homotopic_with_symD by blast
  then show ?thesis
    unfolding contractible_space_def ..
qed

lemma homotopy_equivalent_space_contractibility:
   "X homotopy_equivalent_space Y \<Longrightarrow> (contractible_space X \<longleftrightarrow> contractible_space Y)"
  unfolding homotopy_equivalent_space_def
  by (blast intro: homotopy_dominated_contractibility)

lemma homeomorphic_space_contractibility:
   "X homeomorphic_space Y
        \<Longrightarrow> (contractible_space X \<longleftrightarrow> contractible_space Y)"
  by (simp add: homeomorphic_imp_homotopy_equivalent_space homotopy_equivalent_space_contractibility)

lemma contractible_eq_homotopy_equivalent_singleton_subtopology:
   "contractible_space X \<longleftrightarrow>
        topspace X = {} \<or> (\<exists>a \<in> topspace X. X homotopy_equivalent_space (subtopology X {a}))"(is "?lhs = ?rhs")
proof (cases "topspace X = {}")
  case False
  show ?thesis
  proof
    assume ?lhs
    then obtain a where a: "homotopic_with (\<lambda>x. True) X X id (\<lambda>x. a)"
      by (auto simp: contractible_space_def)
    then have "a \<in> topspace X"
      by (metis False continuous_map_const homotopic_with_imp_continuous_maps)
    then have "homotopic_with (\<lambda>x. True) (subtopology X {a}) (subtopology X {a}) id (\<lambda>x. a)"
      using connectedin_absolute connectedin_sing contractible_space_alt contractible_space_subtopology_singleton by fastforce
    then have "X homotopy_equivalent_space subtopology X {a}"
      unfolding homotopy_equivalent_space_def using \<open>a \<in> topspace X\<close>
      by (metis (full_types) a comp_id continuous_map_const continuous_map_id_subt empty_subsetI homotopic_with_symD
           id_comp insertI1 insert_subset topspace_subtopology_subset)
    with \<open>a \<in> topspace X\<close> show ?rhs
      by blast
  next
    assume ?rhs
    then show ?lhs
      by (meson False contractible_space_subtopology_singleton homotopy_equivalent_space_contractibility)
  qed
qed (simp add: contractible_space_empty)

lemma contractible_space_retraction_map_image:
  assumes "retraction_map X Y f" and X: "contractible_space X"
  shows "contractible_space Y"
proof -
  obtain g where f: "continuous_map X Y f" and g: "continuous_map Y X g" and fg: "\<forall>y \<in> topspace Y. f(g y) = y"
    using assms by (auto simp: retraction_map_def retraction_maps_def)
  obtain a where a: "homotopic_with (\<lambda>x. True) X X id (\<lambda>x. a)"
    using X by (auto simp: contractible_space_def)
  have "homotopic_with (\<lambda>x. True) Y Y id (\<lambda>x. f a)"
  proof (rule homotopic_with_eq)
    show "homotopic_with (\<lambda>x. True) Y Y (f \<circ> id \<circ> g) (f \<circ> (\<lambda>x. a) \<circ> g)"
      using f g a homotopic_with_compose_continuous_map_left homotopic_with_compose_continuous_map_right by metis
  qed (use fg in auto)
  then show ?thesis
    unfolding contractible_space_def by blast
qed

lemma contractible_space_prod_topology:
   "contractible_space(prod_topology X Y) \<longleftrightarrow>
    topspace X = {} \<or> topspace Y = {} \<or> contractible_space X \<and> contractible_space Y"
proof (cases "topspace X = {} \<or> topspace Y = {}")
  case True
  then have "topspace (prod_topology X Y) = {}"
    by simp
  then show ?thesis
    by (auto simp: contractible_space_empty)
next
  case False
  have "contractible_space(prod_topology X Y) \<longleftrightarrow> contractible_space X \<and> contractible_space Y"
  proof safe
    assume XY: "contractible_space (prod_topology X Y)"
    with False have "retraction_map (prod_topology X Y) X fst"
      by (auto simp: contractible_space False retraction_map_fst)
    then show "contractible_space X"
      by (rule contractible_space_retraction_map_image [OF _ XY])
    have "retraction_map (prod_topology X Y) Y snd"
      using False XY  by (auto simp: contractible_space False retraction_map_snd)
    then show "contractible_space Y"
      by (rule contractible_space_retraction_map_image [OF _ XY])
  next
    assume "contractible_space X" and "contractible_space Y"
    with False obtain a b
      where "a \<in> topspace X" and a: "homotopic_with (\<lambda>x. True) X X id (\<lambda>x. a)"
        and "b \<in> topspace Y" and b: "homotopic_with (\<lambda>x. True) Y Y id (\<lambda>x. b)"
      by (auto simp: contractible_space)
    with False show "contractible_space (prod_topology X Y)"
      apply (simp add: contractible_space)
      apply (rule_tac x=a in bexI)
       apply (rule_tac x=b in bexI)
      using homotopic_with_prod_topology [OF a b]
        apply (metis (no_types, lifting) case_prod_Pair case_prod_beta' eq_id_iff)
       apply auto
      done
  qed
  with False show ?thesis
    by auto
qed


lemma contractible_space_product_topology:
  "contractible_space(product_topology X I) \<longleftrightarrow>
    topspace (product_topology X I) = {} \<or> (\<forall>i \<in> I. contractible_space(X i))"
proof (cases "topspace (product_topology X I) = {}")
  case False
  have 1: "contractible_space (X i)"
    if XI: "contractible_space (product_topology X I)" and "i \<in> I"
    for i
  proof (rule contractible_space_retraction_map_image [OF _ XI])
    show "retraction_map (product_topology X I) (X i) (\<lambda>x. x i)"
      using False by (simp add: retraction_map_product_projection \<open>i \<in> I\<close>)
  qed
  have 2: "contractible_space (product_topology X I)"
    if "x \<in> topspace (product_topology X I)" and cs: "\<forall>i\<in>I. contractible_space (X i)"
    for x :: "'a \<Rightarrow> 'b"
  proof -
    obtain f where f: "\<And>i. i\<in>I \<Longrightarrow> homotopic_with (\<lambda>x. True) (X i) (X i) id (\<lambda>x. f i)"
      using cs unfolding contractible_space_def by metis
    have "homotopic_with (\<lambda>x. True)
                         (product_topology X I) (product_topology X I) id (\<lambda>x. restrict f I)"
      by (rule homotopic_with_eq [OF homotopic_with_product_topology [OF f]]) (auto)
    then show ?thesis
      by (auto simp: contractible_space_def)
  qed
  show ?thesis
    using False 1 2 by blast
qed (simp add: contractible_space_empty)


lemma contractible_space_subtopology_euclideanreal [simp]:
  "contractible_space(subtopology euclideanreal S) \<longleftrightarrow> is_interval S"
  (is "?lhs = ?rhs")
proof
  assume ?lhs
  then have "path_connectedin (subtopology euclideanreal S) S"
    using contractible_imp_path_connected_space path_connectedin_topspace path_connectedin_absolute
    by (simp add: contractible_imp_path_connected) 
  then show ?rhs
    by (simp add: is_interval_path_connected_1)
next
  assume ?rhs
  then have "convex S"
    by (simp add: is_interval_convex_1)
  show ?lhs
  proof (cases "S = {}")
    case False
    then obtain z where "z \<in> S"
      by blast
    show ?thesis
      unfolding contractible_space_def homotopic_with_def
    proof (intro exI conjI allI)
      note \<section> = convexD [OF \<open>convex S\<close>, simplified]
      show "continuous_map (prod_topology (top_of_set {0..1}) (top_of_set S)) (top_of_set S)
                           (\<lambda>(t,x). (1 - t) * x + t * z)"
        using  \<open>z \<in> S\<close> 
        by (auto simp add: case_prod_unfold intro!: continuous_intros \<section>)
    qed auto
  qed (simp add: contractible_space_empty)
qed


corollary contractible_space_euclideanreal: "contractible_space euclideanreal"
proof -
  have "contractible_space (subtopology euclideanreal UNIV)"
    using contractible_space_subtopology_euclideanreal by blast
  then show ?thesis
    by simp
qed


abbreviation\<^marker>\<open>tag important\<close> homotopy_eqv :: "'a::topological_space set \<Rightarrow> 'b::topological_space set \<Rightarrow> bool"
             (infix "homotopy'_eqv" 50)
  where "S homotopy_eqv T \<equiv> top_of_set S homotopy_equivalent_space top_of_set T"





lemma homeomorphic_imp_homotopy_eqv: "S homeomorphic T \<Longrightarrow> S homotopy_eqv T"
  unfolding homeomorphic_def homeomorphism_def homotopy_equivalent_space_def
  by (metis continuous_map_subtopology_eu homotopic_with_id2 openin_imp_subset openin_subtopology_self topspace_euclidean_subtopology)


lemma homotopy_eqv_inj_linear_image:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "linear f" "inj f"
    shows "(f ` S) homotopy_eqv S"
  by (metis assms homeomorphic_sym homeomorphic_imp_homotopy_eqv linear_homeomorphic_image)

lemma homotopy_eqv_translation:
    fixes S :: "'a::real_normed_vector set"
    shows "(+) a ` S homotopy_eqv S"
  using homeomorphic_imp_homotopy_eqv homeomorphic_translation homeomorphic_sym by blast

lemma homotopy_eqv_homotopic_triviality_imp:
  fixes S :: "'a::real_normed_vector set"
    and T :: "'b::real_normed_vector set"
    and U :: "'c::real_normed_vector set"
  assumes "S homotopy_eqv T"
      and f: "continuous_on U f" "f ` U \<subseteq> T"
      and g: "continuous_on U g" "g ` U \<subseteq> T"
      and homUS: "\<And>f g. \<lbrakk>continuous_on U f; f ` U \<subseteq> S;
                         continuous_on U g; g ` U \<subseteq> S\<rbrakk>
                         \<Longrightarrow> homotopic_with_canon (\<lambda>x. True) U S f g"
    shows "homotopic_with_canon (\<lambda>x. True) U T f g"
proof -
  obtain h k where h: "continuous_on S h" "h ` S \<subseteq> T"
               and k: "continuous_on T k" "k ` T \<subseteq> S"
               and hom: "homotopic_with_canon (\<lambda>x. True) S S (k \<circ> h) id"
                        "homotopic_with_canon (\<lambda>x. True) T T (h \<circ> k) id"
    using assms by (auto simp: homotopy_equivalent_space_def)
  have "homotopic_with_canon (\<lambda>f. True) U S (k \<circ> f) (k \<circ> g)"
  proof (rule homUS)
    show "continuous_on U (k \<circ> f)" "continuous_on U (k \<circ> g)"
      using continuous_on_compose continuous_on_subset f g k by blast+
  qed (use f g k in \<open>(force simp: o_def)+\<close> )
  then have "homotopic_with_canon (\<lambda>x. True) U T (h \<circ> (k \<circ> f)) (h \<circ> (k \<circ> g))"
    by (rule homotopic_with_compose_continuous_left; simp add: h)
  moreover have "homotopic_with_canon (\<lambda>x. True) U T (h \<circ> k \<circ> f) (id \<circ> f)"
    by (rule homotopic_with_compose_continuous_right [where X=T and Y=T]; simp add: hom f)
  moreover have "homotopic_with_canon (\<lambda>x. True) U T (h \<circ> k \<circ> g) (id \<circ> g)"
    by (rule homotopic_with_compose_continuous_right [where X=T and Y=T]; simp add: hom g)
  ultimately show "homotopic_with_canon (\<lambda>x. True) U T f g"
    unfolding o_assoc
    by (metis homotopic_with_trans homotopic_with_sym id_comp) 
qed

lemma homotopy_eqv_homotopic_triviality:
  fixes S :: "'a::real_normed_vector set"
    and T :: "'b::real_normed_vector set"
    and U :: "'c::real_normed_vector set"
  assumes "S homotopy_eqv T"
    shows "(\<forall>f g. continuous_on U f \<and> f ` U \<subseteq> S \<and>
                   continuous_on U g \<and> g ` U \<subseteq> S
                   \<longrightarrow> homotopic_with_canon (\<lambda>x. True) U S f g) \<longleftrightarrow>
           (\<forall>f g. continuous_on U f \<and> f ` U \<subseteq> T \<and>
                  continuous_on U g \<and> g ` U \<subseteq> T
                  \<longrightarrow> homotopic_with_canon (\<lambda>x. True) U T f g)"
      (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    by (metis assms homotopy_eqv_homotopic_triviality_imp)
next
  assume ?rhs
  moreover
  have "T homotopy_eqv S"
    using assms homotopy_equivalent_space_sym by blast
  ultimately show ?lhs
    by (blast intro: homotopy_eqv_homotopic_triviality_imp)
qed


lemma homotopy_eqv_cohomotopic_triviality_null_imp:
  fixes S :: "'a::real_normed_vector set"
    and T :: "'b::real_normed_vector set"
    and U :: "'c::real_normed_vector set"
  assumes "S homotopy_eqv T"
      and f: "continuous_on T f" "f ` T \<subseteq> U"
      and homSU: "\<And>f. \<lbrakk>continuous_on S f; f ` S \<subseteq> U\<rbrakk>
                      \<Longrightarrow> \<exists>c. homotopic_with_canon (\<lambda>x. True) S U f (\<lambda>x. c)"
  obtains c where "homotopic_with_canon (\<lambda>x. True) T U f (\<lambda>x. c)"
proof -
  obtain h k where h: "continuous_on S h" "h ` S \<subseteq> T"
               and k: "continuous_on T k" "k ` T \<subseteq> S"
               and hom: "homotopic_with_canon (\<lambda>x. True) S S (k \<circ> h) id"
                        "homotopic_with_canon (\<lambda>x. True) T T (h \<circ> k) id"
    using assms by (auto simp: homotopy_equivalent_space_def)
  obtain c where "homotopic_with_canon (\<lambda>x. True) S U (f \<circ> h) (\<lambda>x. c)"
  proof (rule exE [OF homSU])
    show "continuous_on S (f \<circ> h)"
      using continuous_on_compose continuous_on_subset f h by blast
  qed (use f h in force)
  then have "homotopic_with_canon (\<lambda>x. True) T U ((f \<circ> h) \<circ> k) ((\<lambda>x. c) \<circ> k)"
    by (rule homotopic_with_compose_continuous_right [where X=S]) (use k in auto)
  moreover have "homotopic_with_canon (\<lambda>x. True) T U (f \<circ> id) (f \<circ> (h \<circ> k))"
    by (rule homotopic_with_compose_continuous_left [where Y=T])
       (use f in \<open>auto simp add: hom homotopic_with_symD\<close>)
  ultimately show ?thesis
    using that homotopic_with_trans by (fastforce simp add: o_def)
qed

lemma homotopy_eqv_cohomotopic_triviality_null:
  fixes S :: "'a::real_normed_vector set"
    and T :: "'b::real_normed_vector set"
    and U :: "'c::real_normed_vector set"
  assumes "S homotopy_eqv T"
    shows "(\<forall>f. continuous_on S f \<and> f ` S \<subseteq> U
                \<longrightarrow> (\<exists>c. homotopic_with_canon (\<lambda>x. True) S U f (\<lambda>x. c))) \<longleftrightarrow>
           (\<forall>f. continuous_on T f \<and> f ` T \<subseteq> U
                \<longrightarrow> (\<exists>c. homotopic_with_canon (\<lambda>x. True) T U f (\<lambda>x. c)))"
by (rule iffI; metis assms homotopy_eqv_cohomotopic_triviality_null_imp homotopy_equivalent_space_sym)

text \<open>Similar to the proof above\<close>
lemma homotopy_eqv_homotopic_triviality_null_imp:
  fixes S :: "'a::real_normed_vector set"
    and T :: "'b::real_normed_vector set"
    and U :: "'c::real_normed_vector set"
  assumes "S homotopy_eqv T"
      and f: "continuous_on U f" "f ` U \<subseteq> T"
      and homSU: "\<And>f. \<lbrakk>continuous_on U f; f ` U \<subseteq> S\<rbrakk>
                      \<Longrightarrow> \<exists>c. homotopic_with_canon (\<lambda>x. True) U S f (\<lambda>x. c)"
    shows "\<exists>c. homotopic_with_canon (\<lambda>x. True) U T f (\<lambda>x. c)"
proof -
  obtain h k where h: "continuous_on S h" "h ` S \<subseteq> T"
               and k: "continuous_on T k" "k ` T \<subseteq> S"
               and hom: "homotopic_with_canon (\<lambda>x. True) S S (k \<circ> h) id"
                        "homotopic_with_canon (\<lambda>x. True) T T (h \<circ> k) id"
    using assms by (auto simp: homotopy_equivalent_space_def)
  obtain c::'a where "homotopic_with_canon (\<lambda>x. True) U S (k \<circ> f) (\<lambda>x. c)"
  proof (rule exE [OF homSU [of "k \<circ> f"]])
    show "continuous_on U (k \<circ> f)"
      using continuous_on_compose continuous_on_subset f k by blast
  qed (use f k in force)
  then have "homotopic_with_canon (\<lambda>x. True) U T (h \<circ> (k \<circ> f)) (h \<circ> (\<lambda>x. c))"
    by (rule homotopic_with_compose_continuous_left [where Y=S]) (use h in auto)
  moreover have "homotopic_with_canon (\<lambda>x. True) U T (id \<circ> f) ((h \<circ> k) \<circ> f)"
    by (rule homotopic_with_compose_continuous_right [where X=T])
       (use f in \<open>auto simp add: hom homotopic_with_symD\<close>)
  ultimately show ?thesis
    using homotopic_with_trans by (fastforce simp add: o_def)
qed

lemma homotopy_eqv_homotopic_triviality_null:
  fixes S :: "'a::real_normed_vector set"
    and T :: "'b::real_normed_vector set"
    and U :: "'c::real_normed_vector set"
  assumes "S homotopy_eqv T"
    shows "(\<forall>f. continuous_on U f \<and> f ` U \<subseteq> S
                  \<longrightarrow> (\<exists>c. homotopic_with_canon (\<lambda>x. True) U S f (\<lambda>x. c))) \<longleftrightarrow>
           (\<forall>f. continuous_on U f \<and> f ` U \<subseteq> T
                  \<longrightarrow> (\<exists>c. homotopic_with_canon (\<lambda>x. True) U T f (\<lambda>x. c)))"
by (rule iffI; metis assms homotopy_eqv_homotopic_triviality_null_imp homotopy_equivalent_space_sym)

lemma homotopy_eqv_contractible_sets:
  fixes S :: "'a::real_normed_vector set"
    and T :: "'b::real_normed_vector set"
  assumes "contractible S" "contractible T" "S = {} \<longleftrightarrow> T = {}"
    shows "S homotopy_eqv T"
proof (cases "S = {}")
  case True with assms show ?thesis
    by (simp add: homeomorphic_imp_homotopy_eqv)
next
  case False
  with assms obtain a b where "a \<in> S" "b \<in> T"
    by auto
  then show ?thesis
    unfolding homotopy_equivalent_space_def
    apply (rule_tac x="\<lambda>x. b" in exI, rule_tac x="\<lambda>x. a" in exI)
    apply (intro assms conjI continuous_on_id' homotopic_into_contractible; force)
    done
qed

lemma homotopy_eqv_empty1 [simp]:
  fixes S :: "'a::real_normed_vector set"
  shows "S homotopy_eqv ({}::'b::real_normed_vector set) \<longleftrightarrow> S = {}" (is "?lhs = ?rhs")
proof
  assume ?lhs then show ?rhs
    by (metis continuous_map_subtopology_eu empty_iff equalityI homotopy_equivalent_space_def image_subset_iff subsetI)
qed (simp add: homotopy_eqv_contractible_sets)

lemma homotopy_eqv_empty2 [simp]:
  fixes S :: "'a::real_normed_vector set"
  shows "({}::'b::real_normed_vector set) homotopy_eqv S \<longleftrightarrow> S = {}"
  using homotopy_equivalent_space_sym homotopy_eqv_empty1 by blast

lemma homotopy_eqv_contractibility:
  fixes S :: "'a::real_normed_vector set" and T :: "'b::real_normed_vector set"
  shows "S homotopy_eqv T \<Longrightarrow> (contractible S \<longleftrightarrow> contractible T)"
  by (meson contractible_space_top_of_set homotopy_equivalent_space_contractibility)

lemma homotopy_eqv_sing:
  fixes S :: "'a::real_normed_vector set" and a :: "'b::real_normed_vector"
  shows "S homotopy_eqv {a} \<longleftrightarrow> S \<noteq> {} \<and> contractible S"
proof (cases "S = {}")
  case False then show ?thesis
    by (metis contractible_sing empty_not_insert homotopy_eqv_contractibility homotopy_eqv_contractible_sets)
qed simp

lemma homeomorphic_contractible_eq:
  fixes S :: "'a::real_normed_vector set" and T :: "'b::real_normed_vector set"
  shows "S homeomorphic T \<Longrightarrow> (contractible S \<longleftrightarrow> contractible T)"
by (simp add: homeomorphic_imp_homotopy_eqv homotopy_eqv_contractibility)

lemma homeomorphic_contractible:
  fixes S :: "'a::real_normed_vector set" and T :: "'b::real_normed_vector set"
  shows "\<lbrakk>contractible S; S homeomorphic T\<rbrakk> \<Longrightarrow> contractible T"
  by (metis homeomorphic_contractible_eq)


subsection\<^marker>\<open>tag unimportant\<close>\<open>Misc other results\<close>

lemma bounded_connected_Compl_real:
  fixes S :: "real set"
  assumes "bounded S" and conn: "connected(- S)"
    shows "S = {}"
proof -
  obtain a b where "S \<subseteq> box a b"
    by (meson assms bounded_subset_box_symmetric)
  then have "a \<notin> S" "b \<notin> S"
    by auto
  then have "\<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> x \<in> - S"
    by (meson Compl_iff conn connected_iff_interval)
  then show ?thesis
    using \<open>S \<subseteq> box a b\<close> by auto
qed

corollary bounded_path_connected_Compl_real:
  fixes S :: "real set"
  assumes "bounded S" "path_connected(- S)" shows "S = {}"
  by (simp add: assms bounded_connected_Compl_real path_connected_imp_connected)

lemma bounded_connected_Compl_1:
  fixes S :: "'a::{euclidean_space} set"
  assumes "bounded S" and conn: "connected(- S)" and 1: "DIM('a) = 1"
    shows "S = {}"
proof -
  have "DIM('a) = DIM(real)"
    by (simp add: "1")
  then obtain f::"'a \<Rightarrow> real" and g
  where "linear f" "\<And>x. norm(f x) = norm x" and fg: "\<And>x. g(f x) = x" "\<And>y. f(g y) = y"
    by (rule isomorphisms_UNIV_UNIV) blast
  with \<open>bounded S\<close> have "bounded (f ` S)"
    using bounded_linear_image linear_linear by blast
  have "bij f" by (metis fg bijI')
  have "connected (f ` (-S))"
    using connected_linear_image assms \<open>linear f\<close> by blast
  moreover have "f ` (-S) = - (f ` S)"
    by (simp add: \<open>bij f\<close> bij_image_Compl_eq)
  finally have "connected (- (f ` S))"
    by simp
  then have "f ` S = {}"
    using \<open>bounded (f ` S)\<close> bounded_connected_Compl_real by blast
  then show ?thesis
    by blast
qed


subsection\<^marker>\<open>tag unimportant\<close>\<open>Some Uncountable Sets\<close>

lemma uncountable_closed_segment:
  fixes a :: "'a::real_normed_vector"
  assumes "a \<noteq> b" shows "uncountable (closed_segment a b)"
unfolding path_image_linepath [symmetric] path_image_def
  using inj_on_linepath [OF assms] uncountable_closed_interval [of 0 1]
        countable_image_inj_on by auto

lemma uncountable_open_segment:
  fixes a :: "'a::real_normed_vector"
  assumes "a \<noteq> b" shows "uncountable (open_segment a b)"
  by (simp add: assms open_segment_def uncountable_closed_segment uncountable_minus_countable)

lemma uncountable_convex:
  fixes a :: "'a::real_normed_vector"
  assumes "convex S" "a \<in> S" "b \<in> S" "a \<noteq> b"
    shows "uncountable S"
proof -
  have "uncountable (closed_segment a b)"
    by (simp add: uncountable_closed_segment assms)
  then show ?thesis
    by (meson assms convex_contains_segment countable_subset)
qed

lemma uncountable_ball:
  fixes a :: "'a::euclidean_space"
  assumes "r > 0"
    shows "uncountable (ball a r)"
proof -
  have "uncountable (open_segment a (a + r *\<^sub>R (SOME i. i \<in> Basis)))"
    by (metis Basis_zero SOME_Basis add_cancel_right_right assms less_le scale_eq_0_iff uncountable_open_segment)
  moreover have "open_segment a (a + r *\<^sub>R (SOME i. i \<in> Basis)) \<subseteq> ball a r"
    using assms by (auto simp: in_segment algebra_simps dist_norm SOME_Basis)
  ultimately show ?thesis
    by (metis countable_subset)
qed

lemma ball_minus_countable_nonempty:
  assumes "countable (A :: 'a :: euclidean_space set)" "r > 0"
  shows   "ball z r - A \<noteq> {}"
proof
  assume *: "ball z r - A = {}"
  have "uncountable (ball z r - A)"
    by (intro uncountable_minus_countable assms uncountable_ball)
  thus False by (subst (asm) *) auto
qed

lemma uncountable_cball:
  fixes a :: "'a::euclidean_space"
  assumes "r > 0"
  shows "uncountable (cball a r)"
  using assms countable_subset uncountable_ball by auto

lemma pairwise_disjnt_countable:
  fixes \<N> :: "nat set set"
  assumes "pairwise disjnt \<N>"
    shows "countable \<N>"
proof -
  have "inj_on (\<lambda>X. SOME n. n \<in> X) (\<N> - {{}})"
    by (clarsimp simp: inj_on_def) (metis assms disjnt_iff pairwiseD some_in_eq)
  then show ?thesis
    by (metis countable_Diff_eq countable_def)
qed

lemma pairwise_disjnt_countable_Union:
    assumes "countable (\<Union>\<N>)" and pwd: "pairwise disjnt \<N>"
    shows "countable \<N>"
proof -
  obtain f :: "_ \<Rightarrow> nat" where f: "inj_on f (\<Union>\<N>)"
    using assms by blast
  then have "pairwise disjnt (\<Union> X \<in> \<N>. {f ` X})"
    using assms by (force simp: pairwise_def disjnt_inj_on_iff [OF f])
  then have "countable (\<Union> X \<in> \<N>. {f ` X})"
    using pairwise_disjnt_countable by blast
  then show ?thesis
    by (meson pwd countable_image_inj_on disjoint_image f inj_on_image pairwise_disjnt_countable)
qed

lemma connected_uncountable:
  fixes S :: "'a::metric_space set"
  assumes "connected S" "a \<in> S" "b \<in> S" "a \<noteq> b" shows "uncountable S"
proof -
  have "continuous_on S (dist a)"
    by (intro continuous_intros)
  then have "connected (dist a ` S)"
    by (metis connected_continuous_image \<open>connected S\<close>)
  then have "closed_segment 0 (dist a b) \<subseteq> (dist a ` S)"
    by (simp add: assms closed_segment_subset is_interval_connected_1 is_interval_convex)
  then have "uncountable (dist a ` S)"
    by (metis \<open>a \<noteq> b\<close> countable_subset dist_eq_0_iff uncountable_closed_segment)
  then show ?thesis
    by blast
qed

lemma path_connected_uncountable:
  fixes S :: "'a::metric_space set"
  assumes "path_connected S" "a \<in> S" "b \<in> S" "a \<noteq> b" shows "uncountable S"
  using path_connected_imp_connected assms connected_uncountable by metis

lemma connected_finite_iff_sing:
  fixes S :: "'a::metric_space set"
  assumes "connected S"
  shows "finite S \<longleftrightarrow> S = {} \<or> (\<exists>a. S = {a})"  (is "_ = ?rhs")
proof -
  have "uncountable S" if "\<not> ?rhs"
    using connected_uncountable assms that by blast
  then show ?thesis
    using uncountable_infinite by auto
qed

lemma connected_card_eq_iff_nontrivial:
  fixes S :: "'a::metric_space set"
  shows "connected S \<Longrightarrow> uncountable S \<longleftrightarrow> \<not>(\<exists>a. S \<subseteq> {a})"
  by (metis connected_uncountable finite.emptyI finite.insertI rev_finite_subset singleton_iff subsetI uncountable_infinite)

lemma simple_path_image_uncountable: 
  fixes g :: "real \<Rightarrow> 'a::metric_space"
  assumes "simple_path g"
  shows "uncountable (path_image g)"
proof -
  have "g 0 \<in> path_image g" "g (1/2) \<in> path_image g"
    by (simp_all add: path_defs)
  moreover have "g 0 \<noteq> g (1/2)"
    using assms by (fastforce simp add: simple_path_def)
  ultimately have "\<forall>a. \<not> path_image g \<subseteq> {a}"
    by blast
  then show ?thesis
    using assms connected_simple_path_image connected_uncountable by blast
qed

lemma arc_image_uncountable:
  fixes g :: "real \<Rightarrow> 'a::metric_space"
  assumes "arc g"
  shows "uncountable (path_image g)"
  by (simp add: arc_imp_simple_path assms simple_path_image_uncountable)


subsection\<^marker>\<open>tag unimportant\<close>\<open> Some simple positive connection theorems\<close>

proposition path_connected_convex_diff_countable:
  fixes U :: "'a::euclidean_space set"
  assumes "convex U" "\<not> collinear U" "countable S"
    shows "path_connected(U - S)"
proof (clarsimp simp add: path_connected_def)
  fix a b
  assume "a \<in> U" "a \<notin> S" "b \<in> U" "b \<notin> S"
  let ?m = "midpoint a b"
  show "\<exists>g. path g \<and> path_image g \<subseteq> U - S \<and> pathstart g = a \<and> pathfinish g = b"
  proof (cases "a = b")
    case True
    then show ?thesis
      by (metis DiffI \<open>a \<in> U\<close> \<open>a \<notin> S\<close> path_component_def path_component_refl)
  next
    case False
    then have "a \<noteq> ?m" "b \<noteq> ?m"
      using midpoint_eq_endpoint by fastforce+
    have "?m \<in> U"
      using \<open>a \<in> U\<close> \<open>b \<in> U\<close> \<open>convex U\<close> convex_contains_segment by force
    obtain c where "c \<in> U" and nc_abc: "\<not> collinear {a,b,c}"
      by (metis False \<open>a \<in> U\<close> \<open>b \<in> U\<close> \<open>\<not> collinear U\<close> collinear_triples insert_absorb)
    have ncoll_mca: "\<not> collinear {?m,c,a}"
      by (metis (full_types) \<open>a \<noteq> ?m\<close> collinear_3_trans collinear_midpoint insert_commute nc_abc)
    have ncoll_mcb: "\<not> collinear {?m,c,b}"
      by (metis (full_types) \<open>b \<noteq> ?m\<close> collinear_3_trans collinear_midpoint insert_commute nc_abc)
    have "c \<noteq> ?m"
      by (metis collinear_midpoint insert_commute nc_abc)
    then have "closed_segment ?m c \<subseteq> U"
      by (simp add: \<open>c \<in> U\<close> \<open>?m \<in> U\<close> \<open>convex U\<close> closed_segment_subset)
    then obtain z where z: "z \<in> closed_segment ?m c"
                    and disjS: "(closed_segment a z \<union> closed_segment z b) \<inter> S = {}"
    proof -
      have False if "closed_segment ?m c \<subseteq> {z. (closed_segment a z \<union> closed_segment z b) \<inter> S \<noteq> {}}"
      proof -
        have closb: "closed_segment ?m c \<subseteq>
                 {z \<in> closed_segment ?m c. closed_segment a z \<inter> S \<noteq> {}} \<union> {z \<in> closed_segment ?m c. closed_segment z b \<inter> S \<noteq> {}}"
          using that by blast
        have *: "countable {z \<in> closed_segment ?m c. closed_segment z u \<inter> S \<noteq> {}}"
          if "u \<in> U" "u \<notin> S" and ncoll: "\<not> collinear {?m, c, u}" for u
        proof -
          have **: False if x1: "x1 \<in> closed_segment ?m c" and x2: "x2 \<in> closed_segment ?m c"
                            and "x1 \<noteq> x2" "x1 \<noteq> u"
                            and w: "w \<in> closed_segment x1 u" "w \<in> closed_segment x2 u"
                            and "w \<in> S" for x1 x2 w
          proof -
            have "x1 \<in> affine hull {?m,c}" "x2 \<in> affine hull {?m,c}"
              using segment_as_ball x1 x2 by auto
            then have coll_x1: "collinear {x1, ?m, c}" and coll_x2: "collinear {?m, c, x2}"
              by (simp_all add: affine_hull_3_imp_collinear) (metis affine_hull_3_imp_collinear insert_commute)
            have "\<not> collinear {x1, u, x2}"
            proof
              assume "collinear {x1, u, x2}"
              then have "collinear {?m, c, u}"
                by (metis (full_types) \<open>c \<noteq> ?m\<close> coll_x1 coll_x2 collinear_3_trans insert_commute ncoll \<open>x1 \<noteq> x2\<close>)
              with ncoll show False ..
            qed
            then have "closed_segment x1 u \<inter> closed_segment u x2 = {u}"
              by (blast intro!: Int_closed_segment)
            then have "w = u"
              using closed_segment_commute w by auto
            show ?thesis
              using \<open>u \<notin> S\<close> \<open>w = u\<close> that(7) by auto
          qed
          then have disj: "disjoint ((\<Union>z\<in>closed_segment ?m c. {closed_segment z u \<inter> S}))"
            by (fastforce simp: pairwise_def disjnt_def)
          have cou: "countable ((\<Union>z \<in> closed_segment ?m c. {closed_segment z u \<inter> S}) - {{}})"
            apply (rule pairwise_disjnt_countable_Union [OF _ pairwise_subset [OF disj]])
             apply (rule countable_subset [OF _ \<open>countable S\<close>], auto)
            done
          define f where "f \<equiv> \<lambda>X. (THE z. z \<in> closed_segment ?m c \<and> X = closed_segment z u \<inter> S)"
          show ?thesis
          proof (rule countable_subset [OF _ countable_image [OF cou, where f=f]], clarify)
            fix x
            assume x: "x \<in> closed_segment ?m c" "closed_segment x u \<inter> S \<noteq> {}"
            show "x \<in> f ` ((\<Union>z\<in>closed_segment ?m c. {closed_segment z u \<inter> S}) - {{}})"
            proof (rule_tac x="closed_segment x u \<inter> S" in image_eqI)
              show "x = f (closed_segment x u \<inter> S)"
                unfolding f_def 
                by (rule the_equality [symmetric]) (use x in \<open>auto dest: **\<close>)
            qed (use x in auto)
          qed
        qed
        have "uncountable (closed_segment ?m c)"
          by (metis \<open>c \<noteq> ?m\<close> uncountable_closed_segment)
        then show False
          using closb * [OF \<open>a \<in> U\<close> \<open>a \<notin> S\<close> ncoll_mca] * [OF \<open>b \<in> U\<close> \<open>b \<notin> S\<close> ncoll_mcb]
          by (simp add: closed_segment_commute countable_subset)
      qed
      then show ?thesis
        by (force intro: that)
    qed
    show ?thesis
    proof (intro exI conjI)
      have "path_image (linepath a z +++ linepath z b) \<subseteq> U"
        by (metis \<open>a \<in> U\<close> \<open>b \<in> U\<close> \<open>closed_segment ?m c \<subseteq> U\<close> z \<open>convex U\<close> closed_segment_subset contra_subsetD path_image_linepath subset_path_image_join)
      with disjS show "path_image (linepath a z +++ linepath z b) \<subseteq> U - S"
        by (force simp: path_image_join)
    qed auto
  qed
qed


corollary connected_convex_diff_countable:
  fixes U :: "'a::euclidean_space set"
  assumes "convex U" "\<not> collinear U" "countable S"
  shows "connected(U - S)"
  by (simp add: assms path_connected_convex_diff_countable path_connected_imp_connected)

lemma path_connected_punctured_convex:
  assumes "convex S" and aff: "aff_dim S \<noteq> 1"
    shows "path_connected(S - {a})"
proof -
  consider "aff_dim S = -1" | "aff_dim S = 0" | "aff_dim S \<ge> 2"
    using assms aff_dim_geq [of S] by linarith
  then show ?thesis
  proof cases
    assume "aff_dim S = -1"
    then show ?thesis
      by (metis aff_dim_empty empty_Diff path_connected_empty)
  next
    assume "aff_dim S = 0"
    then show ?thesis
      by (metis aff_dim_eq_0 Diff_cancel Diff_empty Diff_insert0 convex_empty convex_imp_path_connected path_connected_singleton singletonD)
  next
    assume ge2: "aff_dim S \<ge> 2"
    then have "\<not> collinear S"
    proof (clarsimp simp add: collinear_affine_hull)
      fix u v
      assume "S \<subseteq> affine hull {u, v}"
      then have "aff_dim S \<le> aff_dim {u, v}"
        by (metis (no_types) aff_dim_affine_hull aff_dim_subset)
      with ge2 show False
        by (metis (no_types) aff_dim_2 antisym aff not_numeral_le_zero one_le_numeral order_trans)
    qed
    moreover have "countable {a}"
      by simp
    ultimately show ?thesis
      by (metis path_connected_convex_diff_countable [OF \<open>convex S\<close>])
  qed
qed

lemma connected_punctured_convex:
  shows "\<lbrakk>convex S; aff_dim S \<noteq> 1\<rbrakk> \<Longrightarrow> connected(S - {a})"
  using path_connected_imp_connected path_connected_punctured_convex by blast

lemma path_connected_complement_countable:
  fixes S :: "'a::euclidean_space set"
  assumes "2 \<le> DIM('a)" "countable S"
  shows "path_connected(- S)"
proof -
  have "\<not> collinear (UNIV::'a set)"
    using assms by (auto simp: collinear_aff_dim [of "UNIV :: 'a set"])
  then have "path_connected(UNIV - S)"
    by (simp add: \<open>countable S\<close> path_connected_convex_diff_countable)
  then show ?thesis
    by (simp add: Compl_eq_Diff_UNIV)
qed

proposition path_connected_openin_diff_countable:
  fixes S :: "'a::euclidean_space set"
  assumes "connected S" and ope: "openin (top_of_set (affine hull S)) S"
      and "\<not> collinear S" "countable T"
    shows "path_connected(S - T)"
proof (clarsimp simp add: path_connected_component)
  fix x y
  assume xy: "x \<in> S" "x \<notin> T" "y \<in> S" "y \<notin> T"
  show "path_component (S - T) x y"
  proof (rule connected_equivalence_relation_gen [OF \<open>connected S\<close>, where P = "\<lambda>x. x \<notin> T"])
    show "\<exists>z. z \<in> U \<and> z \<notin> T" if opeU: "openin (top_of_set S) U" and "x \<in> U" for U x
    proof -
      have "openin (top_of_set (affine hull S)) U"
        using opeU ope openin_trans by blast
      with \<open>x \<in> U\<close> obtain r where Usub: "U \<subseteq> affine hull S" and "r > 0"
                              and subU: "ball x r \<inter> affine hull S \<subseteq> U"
        by (auto simp: openin_contains_ball)
      with \<open>x \<in> U\<close> have x: "x \<in> ball x r \<inter> affine hull S"
        by auto
      have "\<not> S \<subseteq> {x}"
        using \<open>\<not> collinear S\<close>  collinear_subset by blast
      then obtain x' where "x' \<noteq> x" "x' \<in> S"
        by blast
      obtain y where y: "y \<noteq> x" "y \<in> ball x r \<inter> affine hull S"
      proof
        show "x + (r / 2 / norm(x' - x)) *\<^sub>R (x' - x) \<noteq> x"
          using \<open>x' \<noteq> x\<close> \<open>r > 0\<close> by auto
        show "x + (r / 2 / norm (x' - x)) *\<^sub>R (x' - x) \<in> ball x r \<inter> affine hull S"
          using \<open>x' \<noteq> x\<close> \<open>r > 0\<close> \<open>x' \<in> S\<close> x
          by (simp add: dist_norm mem_affine_3_minus hull_inc)
      qed
      have "convex (ball x r \<inter> affine hull S)"
        by (simp add: affine_imp_convex convex_Int)
      with x y subU have "uncountable U"
        by (meson countable_subset uncountable_convex)
      then have "\<not> U \<subseteq> T"
        using \<open>countable T\<close> countable_subset by blast
      then show ?thesis by blast
    qed
    show "\<exists>U. openin (top_of_set S) U \<and> x \<in> U \<and>
              (\<forall>x\<in>U. \<forall>y\<in>U. x \<notin> T \<and> y \<notin> T \<longrightarrow> path_component (S - T) x y)"
          if "x \<in> S" for x
    proof -
      obtain r where Ssub: "S \<subseteq> affine hull S" and "r > 0"
                 and subS: "ball x r \<inter> affine hull S \<subseteq> S"
        using ope \<open>x \<in> S\<close> by (auto simp: openin_contains_ball)
      then have conv: "convex (ball x r \<inter> affine hull S)"
        by (simp add: affine_imp_convex convex_Int)
      have "\<not> aff_dim (affine hull S) \<le> 1"
        using \<open>\<not> collinear S\<close> collinear_aff_dim by auto
      then have "\<not> aff_dim (ball x r \<inter> affine hull S) \<le> 1"
        by (metis (no_types, hide_lams) aff_dim_convex_Int_open IntI open_ball \<open>0 < r\<close> aff_dim_affine_hull affine_affine_hull affine_imp_convex centre_in_ball empty_iff hull_subset inf_commute subsetCE that)
      then have "\<not> collinear (ball x r \<inter> affine hull S)"
        by (simp add: collinear_aff_dim)
      then have *: "path_connected ((ball x r \<inter> affine hull S) - T)"
        by (rule path_connected_convex_diff_countable [OF conv _ \<open>countable T\<close>])
      have ST: "ball x r \<inter> affine hull S - T \<subseteq> S - T"
        using subS by auto
      show ?thesis
      proof (intro exI conjI)
        show "x \<in> ball x r \<inter> affine hull S"
          using \<open>x \<in> S\<close> \<open>r > 0\<close> by (simp add: hull_inc)
        have "openin (top_of_set (affine hull S)) (ball x r \<inter> affine hull S)"
          by (subst inf.commute) (simp add: openin_Int_open)
        then show "openin (top_of_set S) (ball x r \<inter> affine hull S)"
          by (rule openin_subset_trans [OF _ subS Ssub])
      qed (use * path_component_trans in \<open>auto simp: path_connected_component path_component_of_subset [OF ST]\<close>)
    qed
  qed (use xy path_component_trans in auto)
qed

corollary connected_openin_diff_countable:
  fixes S :: "'a::euclidean_space set"
  assumes "connected S" and ope: "openin (top_of_set (affine hull S)) S"
      and "\<not> collinear S" "countable T"
    shows "connected(S - T)"
  by (metis path_connected_imp_connected path_connected_openin_diff_countable [OF assms])

corollary path_connected_open_diff_countable:
  fixes S :: "'a::euclidean_space set"
  assumes "2 \<le> DIM('a)" "open S" "connected S" "countable T"
  shows "path_connected(S - T)"
proof (cases "S = {}")
  case True
  then show ?thesis
    by (simp)
next
  case False
  show ?thesis
  proof (rule path_connected_openin_diff_countable)
    show "openin (top_of_set (affine hull S)) S"
      by (simp add: assms hull_subset open_subset)
    show "\<not> collinear S"
      using assms False by (simp add: collinear_aff_dim aff_dim_open)
  qed (simp_all add: assms)
qed

corollary connected_open_diff_countable:
  fixes S :: "'a::euclidean_space set"
  assumes "2 \<le> DIM('a)" "open S" "connected S" "countable T"
  shows "connected(S - T)"
by (simp add: assms path_connected_imp_connected path_connected_open_diff_countable)



subsection\<^marker>\<open>tag unimportant\<close> \<open>Self-homeomorphisms shuffling points about\<close>

subsubsection\<^marker>\<open>tag unimportant\<close>\<open>The theorem \<open>homeomorphism_moving_points_exists\<close>\<close>

lemma homeomorphism_moving_point_1:
  fixes a :: "'a::euclidean_space"
  assumes "affine T" "a \<in> T" and u: "u \<in> ball a r \<inter> T"
  obtains f g where "homeomorphism (cball a r \<inter> T) (cball a r \<inter> T) f g"
                    "f a = u" "\<And>x. x \<in> sphere a r \<Longrightarrow> f x = x"
proof -
  have nou: "norm (u - a) < r" and "u \<in> T"
    using u by (auto simp: dist_norm norm_minus_commute)
  then have "0 < r"
    by (metis DiffD1 Diff_Diff_Int ball_eq_empty centre_in_ball not_le u)
  define f where "f \<equiv> \<lambda>x. (1 - norm(x - a) / r) *\<^sub>R (u - a) + x"
  have *: "False" if eq: "x + (norm y / r) *\<^sub>R u = y + (norm x / r) *\<^sub>R u"
                  and nou: "norm u < r" and yx: "norm y < norm x" for x y and u::'a
  proof -
    have "x = y + (norm x / r - (norm y / r)) *\<^sub>R u"
      using eq by (simp add: algebra_simps)
    then have "norm x = norm (y + ((norm x - norm y) / r) *\<^sub>R u)"
      by (metis diff_divide_distrib)
    also have "\<dots> \<le> norm y + norm(((norm x - norm y) / r) *\<^sub>R u)"
      using norm_triangle_ineq by blast
    also have "\<dots> = norm y + (norm x - norm y) * (norm u / r)"
      using yx \<open>r > 0\<close>
      by (simp add: field_split_simps)
    also have "\<dots> < norm y + (norm x - norm y) * 1"
    proof (subst add_less_cancel_left)
      show "(norm x - norm y) * (norm u / r) < (norm x - norm y) * 1"
      proof (rule mult_strict_left_mono)
        show "norm u / r < 1"
          using \<open>0 < r\<close> divide_less_eq_1_pos nou by blast
      qed (simp add: yx)
    qed
    also have "\<dots> = norm x"
      by simp
    finally show False by simp
  qed
  have "inj f"
    unfolding f_def
  proof (clarsimp simp: inj_on_def)
    fix x y
    assume "(1 - norm (x - a) / r) *\<^sub>R (u - a) + x =
            (1 - norm (y - a) / r) *\<^sub>R (u - a) + y"
    then have eq: "(x - a) + (norm (y - a) / r) *\<^sub>R (u - a) = (y - a) + (norm (x - a) / r) *\<^sub>R (u - a)"
      by (auto simp: algebra_simps)
    show "x=y"
    proof (cases "norm (x - a) = norm (y - a)")
      case True
      then show ?thesis
        using eq by auto
    next
      case False
      then consider "norm (x - a) < norm (y - a)" | "norm (x - a) > norm (y - a)"
        by linarith
      then have "False"
      proof cases
        case 1 show False
          using * [OF _ nou 1] eq by simp
      next
        case 2 with * [OF eq nou] show False
          by auto
      qed
      then show "x=y" ..
    qed
  qed
  then have inj_onf: "inj_on f (cball a r \<inter> T)"
    using inj_on_Int by fastforce
  have contf: "continuous_on (cball a r \<inter> T) f"
    unfolding f_def using \<open>0 < r\<close>  by (intro continuous_intros) blast
  have fim: "f ` (cball a r \<inter> T) = cball a r \<inter> T"
  proof
    have *: "norm (y + (1 - norm y / r) *\<^sub>R u) \<le> r" if "norm y \<le> r" "norm u < r" for y u::'a
    proof -
      have "norm (y + (1 - norm y / r) *\<^sub>R u) \<le> norm y + norm((1 - norm y / r) *\<^sub>R u)"
        using norm_triangle_ineq by blast
      also have "\<dots> = norm y + abs(1 - norm y / r) * norm u"
        by simp
      also have "\<dots> \<le> r"
      proof -
        have "(r - norm u) * (r - norm y) \<ge> 0"
          using that by auto
        then have "r * norm u + r * norm y \<le> r * r + norm u * norm y"
          by (simp add: algebra_simps)
        then show ?thesis
        using that \<open>0 < r\<close> by (simp add: abs_if field_simps)
      qed
      finally show ?thesis .
    qed
    have "f ` (cball a r) \<subseteq> cball a r"
      using * nou
      apply (clarsimp simp: dist_norm norm_minus_commute f_def)
      by (metis diff_add_eq diff_diff_add diff_diff_eq2 norm_minus_commute)
    moreover have "f ` T \<subseteq> T"
      unfolding f_def using \<open>affine T\<close> \<open>a \<in> T\<close> \<open>u \<in> T\<close>
      by (force simp: add.commute mem_affine_3_minus)
    ultimately show "f ` (cball a r \<inter> T) \<subseteq> cball a r \<inter> T"
      by blast
  next
    show "cball a r \<inter> T \<subseteq> f ` (cball a r \<inter> T)"
    proof (clarsimp simp add: dist_norm norm_minus_commute)
      fix x
      assume x: "norm (x - a) \<le> r" and "x \<in> T"
      have "\<exists>v \<in> {0..1}. ((1 - v) * r - norm ((x - a) - v *\<^sub>R (u - a))) \<bullet> 1 = 0"
        by (rule ivt_decreasing_component_on_1) (auto simp: x continuous_intros)
      then obtain v where "0 \<le> v" "v \<le> 1"
        and v: "(1 - v) * r = norm ((x - a) - v *\<^sub>R (u - a))"
        by auto
      then have n: "norm (a - (x - v *\<^sub>R (u - a))) = r - r * v"
        by (simp add: field_simps norm_minus_commute)
      show "x \<in> f ` (cball a r \<inter> T)"
      proof (rule image_eqI)
        show "x = f (x - v *\<^sub>R (u - a))"
          using \<open>r > 0\<close> v by (simp add: f_def) (simp add: field_simps)
        have "x - v *\<^sub>R (u - a) \<in> cball a r"
          using \<open>r > 0\<close>\<open>0 \<le> v\<close>
          by (simp add: dist_norm n)
        moreover have "x - v *\<^sub>R (u - a) \<in> T"
          by (simp add: f_def \<open>u \<in> T\<close> \<open>x \<in> T\<close> assms mem_affine_3_minus2)
        ultimately show "x - v *\<^sub>R (u - a) \<in> cball a r \<inter> T"
          by blast
      qed
    qed
  qed
  have "compact (cball a r \<inter> T)"
    by (simp add: affine_closed compact_Int_closed \<open>affine T\<close>)
  then obtain g where "homeomorphism (cball a r \<inter> T) (cball a r \<inter> T) f g"
    by (metis homeomorphism_compact [OF _ contf fim inj_onf])
  then show thesis
    apply (rule_tac f=f in that)
    using \<open>r > 0\<close> by (simp_all add: f_def dist_norm norm_minus_commute)
qed

corollary\<^marker>\<open>tag unimportant\<close> homeomorphism_moving_point_2:
  fixes a :: "'a::euclidean_space"
  assumes "affine T" "a \<in> T" and u: "u \<in> ball a r \<inter> T" and v: "v \<in> ball a r \<inter> T"
  obtains f g where "homeomorphism (cball a r \<inter> T) (cball a r \<inter> T) f g"
                    "f u = v" "\<And>x. \<lbrakk>x \<in> sphere a r; x \<in> T\<rbrakk> \<Longrightarrow> f x = x"
proof -
  have "0 < r"
    by (metis DiffD1 Diff_Diff_Int ball_eq_empty centre_in_ball not_le u)
  obtain f1 g1 where hom1: "homeomorphism (cball a r \<inter> T) (cball a r \<inter> T) f1 g1"
                 and "f1 a = u" and f1: "\<And>x. x \<in> sphere a r \<Longrightarrow> f1 x = x"
    using homeomorphism_moving_point_1 [OF \<open>affine T\<close> \<open>a \<in> T\<close> u] by blast
  obtain f2 g2 where hom2: "homeomorphism (cball a r \<inter> T) (cball a r \<inter> T) f2 g2"
                 and "f2 a = v" and f2: "\<And>x. x \<in> sphere a r \<Longrightarrow> f2 x = x"
    using homeomorphism_moving_point_1 [OF \<open>affine T\<close> \<open>a \<in> T\<close> v] by blast
  show ?thesis
  proof
    show "homeomorphism (cball a r \<inter> T) (cball a r \<inter> T) (f2 \<circ> g1) (f1 \<circ> g2)"
      by (metis homeomorphism_compose homeomorphism_symD hom1 hom2)
    have "g1 u = a"
      using \<open>0 < r\<close> \<open>f1 a = u\<close> assms hom1 homeomorphism_apply1 by fastforce
    then show "(f2 \<circ> g1) u = v"
      by (simp add: \<open>f2 a = v\<close>)
    show "\<And>x. \<lbrakk>x \<in> sphere a r; x \<in> T\<rbrakk> \<Longrightarrow> (f2 \<circ> g1) x = x"
      using f1 f2 hom1 homeomorphism_apply1 by fastforce
  qed
qed


corollary\<^marker>\<open>tag unimportant\<close> homeomorphism_moving_point_3:
  fixes a :: "'a::euclidean_space"
  assumes "affine T" "a \<in> T" and ST: "ball a r \<inter> T \<subseteq> S" "S \<subseteq> T"
      and u: "u \<in> ball a r \<inter> T" and v: "v \<in> ball a r \<inter> T"
  obtains f g where "homeomorphism S S f g"
                    "f u = v" "{x. \<not> (f x = x \<and> g x = x)} \<subseteq> ball a r \<inter> T"
proof -
  obtain f g where hom: "homeomorphism (cball a r \<inter> T) (cball a r \<inter> T) f g"
               and "f u = v" and fid: "\<And>x. \<lbrakk>x \<in> sphere a r; x \<in> T\<rbrakk> \<Longrightarrow> f x = x"
    using homeomorphism_moving_point_2 [OF \<open>affine T\<close> \<open>a \<in> T\<close> u v] by blast
  have gid: "\<And>x. \<lbrakk>x \<in> sphere a r; x \<in> T\<rbrakk> \<Longrightarrow> g x = x"
    using fid hom homeomorphism_apply1 by fastforce
  define ff where "ff \<equiv> \<lambda>x. if x \<in> ball a r \<inter> T then f x else x"
  define gg where "gg \<equiv> \<lambda>x. if x \<in> ball a r \<inter> T then g x else x"
  show ?thesis
  proof
    show "homeomorphism S S ff gg"
    proof (rule homeomorphismI)
      have "continuous_on ((cball a r \<inter> T) \<union> (T - ball a r)) ff"
        unfolding ff_def
        using homeomorphism_cont1 [OF hom] 
        by (intro continuous_on_cases) (auto simp: affine_closed \<open>affine T\<close> fid)
      then show "continuous_on S ff"
        by (rule continuous_on_subset) (use ST in auto)
      have "continuous_on ((cball a r \<inter> T) \<union> (T - ball a r)) gg"
        unfolding gg_def
        using homeomorphism_cont2 [OF hom] 
        by (intro continuous_on_cases) (auto simp: affine_closed \<open>affine T\<close> gid)
      then show "continuous_on S gg"
        by (rule continuous_on_subset) (use ST in auto)
      show "ff ` S \<subseteq> S"
      proof (clarsimp simp add: ff_def)
        fix x
        assume "x \<in> S" and x: "dist a x < r" and "x \<in> T"
        then have "f x \<in> cball a r \<inter> T"
          using homeomorphism_image1 [OF hom] by force
        then show "f x \<in> S"
          using ST(1) \<open>x \<in> T\<close> gid hom homeomorphism_def x by fastforce
      qed
      show "gg ` S \<subseteq> S"
      proof (clarsimp simp add: gg_def)
        fix x
        assume "x \<in> S" and x: "dist a x < r" and "x \<in> T"
        then have "g x \<in> cball a r \<inter> T"
          using homeomorphism_image2 [OF hom] by force
        then have "g x \<in> ball a r"
          using homeomorphism_apply2 [OF hom]
            by (metis Diff_Diff_Int Diff_iff  \<open>x \<in> T\<close> cball_def fid le_less mem_Collect_eq mem_ball mem_sphere x)
        then show "g x \<in> S"
          using ST(1) \<open>g x \<in> cball a r \<inter> T\<close> by force
        qed
      show "\<And>x. x \<in> S \<Longrightarrow> gg (ff x) = x"
        unfolding ff_def gg_def
        using homeomorphism_apply1 [OF hom] homeomorphism_image1 [OF hom]
        by simp (metis Int_iff homeomorphism_apply1 [OF hom] fid image_eqI less_eq_real_def mem_cball mem_sphere)
      show "\<And>x. x \<in> S \<Longrightarrow> ff (gg x) = x"
        unfolding ff_def gg_def
        using homeomorphism_apply2 [OF hom] homeomorphism_image2 [OF hom]
        by simp (metis Int_iff fid image_eqI less_eq_real_def mem_cball mem_sphere)
    qed
    show "ff u = v"
      using u by (auto simp: ff_def \<open>f u = v\<close>)
    show "{x. \<not> (ff x = x \<and> gg x = x)} \<subseteq> ball a r \<inter> T"
      by (auto simp: ff_def gg_def)
  qed
qed


proposition\<^marker>\<open>tag unimportant\<close> homeomorphism_moving_point:
  fixes a :: "'a::euclidean_space"
  assumes ope: "openin (top_of_set (affine hull S)) S"
      and "S \<subseteq> T"
      and TS: "T \<subseteq> affine hull S"
      and S: "connected S" "a \<in> S" "b \<in> S"
  obtains f g where "homeomorphism T T f g" "f a = b"
                    "{x. \<not> (f x = x \<and> g x = x)} \<subseteq> S"
                    "bounded {x. \<not> (f x = x \<and> g x = x)}"
proof -
  have 1: "\<exists>h k. homeomorphism T T h k \<and> h (f d) = d \<and>
              {x. \<not> (h x = x \<and> k x = x)} \<subseteq> S \<and> bounded {x. \<not> (h x = x \<and> k x = x)}"
        if "d \<in> S" "f d \<in> S" and homfg: "homeomorphism T T f g"
        and S: "{x. \<not> (f x = x \<and> g x = x)} \<subseteq> S"
        and bo: "bounded {x. \<not> (f x = x \<and> g x = x)}" for d f g
  proof (intro exI conjI)
    show homgf: "homeomorphism T T g f"
      by (metis homeomorphism_symD homfg)
    then show "g (f d) = d"
      by (meson \<open>S \<subseteq> T\<close> homeomorphism_def subsetD \<open>d \<in> S\<close>)
    show "{x. \<not> (g x = x \<and> f x = x)} \<subseteq> S"
      using S by blast
    show "bounded {x. \<not> (g x = x \<and> f x = x)}"
      using bo by (simp add: conj_commute)
  qed
  have 2: "\<exists>f g. homeomorphism T T f g \<and> f x = f2 (f1 x) \<and>
                 {x. \<not> (f x = x \<and> g x = x)} \<subseteq> S \<and> bounded {x. \<not> (f x = x \<and> g x = x)}"
             if "x \<in> S" "f1 x \<in> S" "f2 (f1 x) \<in> S"
                and hom: "homeomorphism T T f1 g1" "homeomorphism T T f2 g2"
                and sub: "{x. \<not> (f1 x = x \<and> g1 x = x)} \<subseteq> S"   "{x. \<not> (f2 x = x \<and> g2 x = x)} \<subseteq> S"
                and bo: "bounded {x. \<not> (f1 x = x \<and> g1 x = x)}"  "bounded {x. \<not> (f2 x = x \<and> g2 x = x)}"
             for x f1 f2 g1 g2
  proof (intro exI conjI)
    show homgf: "homeomorphism T T (f2 \<circ> f1) (g1 \<circ> g2)"
      by (metis homeomorphism_compose hom)
    then show "(f2 \<circ> f1) x = f2 (f1 x)"
      by force
    show "{x. \<not> ((f2 \<circ> f1) x = x \<and> (g1 \<circ> g2) x = x)} \<subseteq> S"
      using sub by force
    have "bounded ({x. \<not>(f1 x = x \<and> g1 x = x)} \<union> {x. \<not>(f2 x = x \<and> g2 x = x)})"
      using bo by simp
    then show "bounded {x. \<not> ((f2 \<circ> f1) x = x \<and> (g1 \<circ> g2) x = x)}"
      by (rule bounded_subset) auto
  qed
  have 3: "\<exists>U. openin (top_of_set S) U \<and>
              d \<in> U \<and>
              (\<forall>x\<in>U.
                  \<exists>f g. homeomorphism T T f g \<and> f d = x \<and>
                        {x. \<not> (f x = x \<and> g x = x)} \<subseteq> S \<and>
                        bounded {x. \<not> (f x = x \<and> g x = x)})"
           if "d \<in> S" for d
  proof -
    obtain r where "r > 0" and r: "ball d r \<inter> affine hull S \<subseteq> S"
      by (metis \<open>d \<in> S\<close> ope openin_contains_ball)
    have *: "\<exists>f g. homeomorphism T T f g \<and> f d = e \<and>
                   {x. \<not> (f x = x \<and> g x = x)} \<subseteq> S \<and>
                   bounded {x. \<not> (f x = x \<and> g x = x)}" if "e \<in> S" "e \<in> ball d r" for e
      apply (rule homeomorphism_moving_point_3 [of "affine hull S" d r T d e])
      using r \<open>S \<subseteq> T\<close> TS that 
            apply (auto simp: \<open>d \<in> S\<close> \<open>0 < r\<close> hull_inc)
      using bounded_subset by blast
    show ?thesis
      by (rule_tac x="S \<inter> ball d r" in exI) (fastforce simp: openin_open_Int \<open>0 < r\<close> that intro: *)
  qed
  have "\<exists>f g. homeomorphism T T f g \<and> f a = b \<and>
              {x. \<not> (f x = x \<and> g x = x)} \<subseteq> S \<and> bounded {x. \<not> (f x = x \<and> g x = x)}"
    by (rule connected_equivalence_relation [OF S]; blast intro: 1 2 3)
  then show ?thesis
    using that by auto
qed


lemma homeomorphism_moving_points_exists_gen:
  assumes K: "finite K" "\<And>i. i \<in> K \<Longrightarrow> x i \<in> S \<and> y i \<in> S"
             "pairwise (\<lambda>i j. (x i \<noteq> x j) \<and> (y i \<noteq> y j)) K"
      and "2 \<le> aff_dim S"
      and ope: "openin (top_of_set (affine hull S)) S"
      and "S \<subseteq> T" "T \<subseteq> affine hull S" "connected S"
  shows "\<exists>f g. homeomorphism T T f g \<and> (\<forall>i \<in> K. f(x i) = y i) \<and>
               {x. \<not> (f x = x \<and> g x = x)} \<subseteq> S \<and> bounded {x. \<not> (f x = x \<and> g x = x)}"
  using assms
proof (induction K)
  case empty
  then show ?case
    by (force simp: homeomorphism_ident)
next
  case (insert i K)
  then have xney: "\<And>j. \<lbrakk>j \<in> K; j \<noteq> i\<rbrakk> \<Longrightarrow> x i \<noteq> x j \<and> y i \<noteq> y j"
       and pw: "pairwise (\<lambda>i j. x i \<noteq> x j \<and> y i \<noteq> y j) K"
       and "x i \<in> S" "y i \<in> S"
       and xyS: "\<And>i. i \<in> K \<Longrightarrow> x i \<in> S \<and> y i \<in> S"
    by (simp_all add: pairwise_insert)
  obtain f g where homfg: "homeomorphism T T f g" and feq: "\<And>i. i \<in> K \<Longrightarrow> f(x i) = y i"
               and fg_sub: "{x. \<not> (f x = x \<and> g x = x)} \<subseteq> S"
               and bo_fg: "bounded {x. \<not> (f x = x \<and> g x = x)}"
    using insert.IH [OF xyS pw] insert.prems by (blast intro: that)
  then have "\<exists>f g. homeomorphism T T f g \<and> (\<forall>i \<in> K. f(x i) = y i) \<and>
                   {x. \<not> (f x = x \<and> g x = x)} \<subseteq> S \<and> bounded {x. \<not> (f x = x \<and> g x = x)}"
    using insert by blast
  have aff_eq: "affine hull (S - y ` K) = affine hull S"
  proof (rule affine_hull_Diff [OF ope])
    show "finite (y ` K)"
      by (simp add: insert.hyps(1))
    show "y ` K \<subset> S"
      using \<open>y i \<in> S\<close> insert.hyps(2) xney xyS by fastforce
  qed
  have f_in_S: "f x \<in> S" if "x \<in> S" for x
    using homfg fg_sub homeomorphism_apply1 \<open>S \<subseteq> T\<close>
  proof -
    have "(f (f x) \<noteq> f x \<or> g (f x) \<noteq> f x) \<or> f x \<in> S"
      by (metis \<open>S \<subseteq> T\<close> homfg subsetD homeomorphism_apply1 that)
    then show ?thesis
      using fg_sub by force
  qed
  obtain h k where homhk: "homeomorphism T T h k" and heq: "h (f (x i)) = y i"
               and hk_sub: "{x. \<not> (h x = x \<and> k x = x)} \<subseteq> S - y ` K"
               and bo_hk:  "bounded {x. \<not> (h x = x \<and> k x = x)}"
  proof (rule homeomorphism_moving_point [of "S - y`K" T "f(x i)" "y i"])
    show "openin (top_of_set (affine hull (S - y ` K))) (S - y ` K)"
      by (simp add: aff_eq openin_diff finite_imp_closedin image_subset_iff hull_inc insert xyS)
    show "S - y ` K \<subseteq> T"
      using \<open>S \<subseteq> T\<close> by auto
    show "T \<subseteq> affine hull (S - y ` K)"
      using insert by (simp add: aff_eq)
    show "connected (S - y ` K)"
    proof (rule connected_openin_diff_countable [OF \<open>connected S\<close> ope])
      show "\<not> collinear S"
        using collinear_aff_dim \<open>2 \<le> aff_dim S\<close> by force
      show "countable (y ` K)"
        using countable_finite insert.hyps(1) by blast
    qed
    have "\<And>k. \<lbrakk>f (x i) = y k; k \<in> K\<rbrakk> \<Longrightarrow> False"
        by (metis feq homfg \<open>x i \<in> S\<close> homeomorphism_def \<open>S \<subseteq> T\<close> \<open>i \<notin> K\<close> subsetCE xney xyS)
    then show "f (x i) \<in> S - y ` K"
      by (auto simp: f_in_S \<open>x i \<in> S\<close>)
    show "y i \<in> S - y ` K"
      using insert.hyps xney by (auto simp: \<open>y i \<in> S\<close>)
  qed blast
  show ?case
  proof (intro exI conjI)
    show "homeomorphism T T (h \<circ> f) (g \<circ> k)"
      using homfg homhk homeomorphism_compose by blast
    show "\<forall>i \<in> insert i K. (h \<circ> f) (x i) = y i"
      using feq hk_sub by (auto simp: heq)
    show "{x. \<not> ((h \<circ> f) x = x \<and> (g \<circ> k) x = x)} \<subseteq> S"
      using fg_sub hk_sub by force
    have "bounded ({x. \<not>(f x = x \<and> g x = x)} \<union> {x. \<not>(h x = x \<and> k x = x)})"
      using bo_fg bo_hk bounded_Un by blast
    then show "bounded {x. \<not> ((h \<circ> f) x = x \<and> (g \<circ> k) x = x)}"
      by (rule bounded_subset) auto
  qed
qed

proposition\<^marker>\<open>tag unimportant\<close> homeomorphism_moving_points_exists:
  fixes S :: "'a::euclidean_space set"
  assumes 2: "2 \<le> DIM('a)" "open S" "connected S" "S \<subseteq> T" "finite K"
      and KS: "\<And>i. i \<in> K \<Longrightarrow> x i \<in> S \<and> y i \<in> S"
      and pw: "pairwise (\<lambda>i j. (x i \<noteq> x j) \<and> (y i \<noteq> y j)) K"
      and S: "S \<subseteq> T" "T \<subseteq> affine hull S" "connected S"
  obtains f g where "homeomorphism T T f g" "\<And>i. i \<in> K \<Longrightarrow> f(x i) = y i"
                    "{x. \<not> (f x = x \<and> g x = x)} \<subseteq> S" "bounded {x. (\<not> (f x = x \<and> g x = x))}"
proof (cases "S = {}")
  case True
  then show ?thesis
    using KS homeomorphism_ident that by fastforce
next
  case False
  then have affS: "affine hull S = UNIV"
    by (simp add: affine_hull_open \<open>open S\<close>)
  then have ope: "openin (top_of_set (affine hull S)) S"
    using \<open>open S\<close> open_openin by auto
  have "2 \<le> DIM('a)" by (rule 2)
  also have "\<dots> = aff_dim (UNIV :: 'a set)"
    by simp
  also have "\<dots> \<le> aff_dim S"
    by (metis aff_dim_UNIV aff_dim_affine_hull aff_dim_le_DIM affS)
  finally have "2 \<le> aff_dim S"
    by linarith
  then show ?thesis
    using homeomorphism_moving_points_exists_gen [OF \<open>finite K\<close> KS pw _ ope S] that by fastforce
qed

subsubsection\<^marker>\<open>tag unimportant\<close>\<open>The theorem \<open>homeomorphism_grouping_points_exists\<close>\<close>

lemma homeomorphism_grouping_point_1:
  fixes a::real and c::real
  assumes "a < b" "c < d"
  obtains f g where "homeomorphism (cbox a b) (cbox c d) f g" "f a = c" "f b = d"
proof -
  define f where "f \<equiv> \<lambda>x. ((d - c) / (b - a)) * x + (c - a * ((d - c) / (b - a)))"
  have "\<exists>g. homeomorphism (cbox a b) (cbox c d) f g"
  proof (rule homeomorphism_compact)
    show "continuous_on (cbox a b) f"
      unfolding f_def by (intro continuous_intros)
    have "f ` {a..b} = {c..d}"
      unfolding f_def image_affinity_atLeastAtMost
      using assms sum_sqs_eq by (auto simp: field_split_simps)
    then show "f ` cbox a b = cbox c d"
      by auto
    show "inj_on f (cbox a b)"
      unfolding f_def inj_on_def using assms by auto
  qed auto
  then obtain g where "homeomorphism (cbox a b) (cbox c d) f g" ..
  then show ?thesis
  proof
    show "f a = c"
      by (simp add: f_def)
    show "f b = d"
      using assms sum_sqs_eq [of a b] by (auto simp: f_def field_split_simps)
  qed
qed

lemma homeomorphism_grouping_point_2:
  fixes a::real and w::real
  assumes hom_ab: "homeomorphism (cbox a b) (cbox u v) f1 g1"
      and hom_bc: "homeomorphism (cbox b c) (cbox v w) f2 g2"
      and "b \<in> cbox a c" "v \<in> cbox u w"
      and eq: "f1 a = u" "f1 b = v" "f2 b = v" "f2 c = w"
 obtains f g where "homeomorphism (cbox a c) (cbox u w) f g" "f a = u" "f c = w"
                   "\<And>x. x \<in> cbox a b \<Longrightarrow> f x = f1 x" "\<And>x. x \<in> cbox b c \<Longrightarrow> f x = f2 x"
proof -
  have le: "a \<le> b" "b \<le> c" "u \<le> v" "v \<le> w"
    using assms by simp_all
  then have ac: "cbox a c = cbox a b \<union> cbox b c" and uw: "cbox u w = cbox u v \<union> cbox v w"
    by auto
  define f where "f \<equiv> \<lambda>x. if x \<le> b then f1 x else f2 x"
  have "\<exists>g. homeomorphism (cbox a c) (cbox u w) f g"
  proof (rule homeomorphism_compact)
    have cf1: "continuous_on (cbox a b) f1"
      using hom_ab homeomorphism_cont1 by blast
    have cf2: "continuous_on (cbox b c) f2"
      using hom_bc homeomorphism_cont1 by blast
    show "continuous_on (cbox a c) f"
      unfolding f_def using le eq
      by (force intro: continuous_on_cases_le [OF continuous_on_subset [OF cf1] continuous_on_subset [OF cf2]])
    have "f ` cbox a b = f1 ` cbox a b" "f ` cbox b c = f2 ` cbox b c"
      unfolding f_def using eq by force+
    then show "f ` cbox a c = cbox u w"
      unfolding ac uw image_Un by (metis hom_ab hom_bc homeomorphism_def)
    have neq12: "f1 x \<noteq> f2 y" if x: "a \<le> x" "x \<le> b" and y: "b < y" "y \<le> c" for x y
    proof -
      have "f1 x \<in> cbox u v"
        by (metis hom_ab homeomorphism_def image_eqI mem_box_real(2) x)
      moreover have "f2 y \<in> cbox v w"
        by (metis (full_types) hom_bc homeomorphism_def image_subset_iff mem_box_real(2) not_le not_less_iff_gr_or_eq order_refl y)
      moreover have "f2 y \<noteq> f2 b"
        by (metis cancel_comm_monoid_add_class.diff_cancel diff_gt_0_iff_gt hom_bc homeomorphism_def le(2) less_imp_le less_numeral_extra(3) mem_box_real(2) order_refl y)
      ultimately show ?thesis
        using le eq by simp
    qed
    have "inj_on f1 (cbox a b)"
      by (metis (full_types) hom_ab homeomorphism_def inj_onI)
    moreover have "inj_on f2 (cbox b c)"
      by (metis (full_types) hom_bc homeomorphism_def inj_onI)
    ultimately show "inj_on f (cbox a c)"
      apply (simp (no_asm) add: inj_on_def)
      apply (simp add: f_def inj_on_eq_iff)
      using neq12 by force
  qed auto
  then obtain g where "homeomorphism (cbox a c) (cbox u w) f g" ..
  then show ?thesis
    using eq f_def le that by force
qed

lemma homeomorphism_grouping_point_3:
  fixes a::real
  assumes cbox_sub: "cbox c d \<subseteq> box a b" "cbox u v \<subseteq> box a b"
      and box_ne: "box c d \<noteq> {}" "box u v \<noteq> {}"
  obtains f g where "homeomorphism (cbox a b) (cbox a b) f g" "f a = a" "f b = b"
                    "\<And>x. x \<in> cbox c d \<Longrightarrow> f x \<in> cbox u v"
proof -
  have less: "a < c" "a < u" "d < b" "v < b" "c < d" "u < v" "cbox c d \<noteq> {}"
    using assms
    by (simp_all add: cbox_sub subset_eq)
  obtain f1 g1 where 1: "homeomorphism (cbox a c) (cbox a u) f1 g1"
                   and f1_eq: "f1 a = a" "f1 c = u"
    using homeomorphism_grouping_point_1 [OF \<open>a < c\<close> \<open>a < u\<close>] .
  obtain f2 g2 where 2: "homeomorphism (cbox c d) (cbox u v) f2 g2"
                   and f2_eq: "f2 c = u" "f2 d = v"
    using homeomorphism_grouping_point_1 [OF \<open>c < d\<close> \<open>u < v\<close>] .
  obtain f3 g3 where 3: "homeomorphism (cbox d b) (cbox v b) f3 g3"
                   and f3_eq: "f3 d = v" "f3 b = b"
    using homeomorphism_grouping_point_1 [OF \<open>d < b\<close> \<open>v < b\<close>] .
  obtain f4 g4 where 4: "homeomorphism (cbox a d) (cbox a v) f4 g4" and "f4 a = a" "f4 d = v"
                 and f4_eq: "\<And>x. x \<in> cbox a c \<Longrightarrow> f4 x = f1 x" "\<And>x. x \<in> cbox c d \<Longrightarrow> f4 x = f2 x"
    using homeomorphism_grouping_point_2 [OF 1 2] less  by (auto simp: f1_eq f2_eq)
  obtain f g where fg: "homeomorphism (cbox a b) (cbox a b) f g" "f a = a" "f b = b"
               and f_eq: "\<And>x. x \<in> cbox a d \<Longrightarrow> f x = f4 x" "\<And>x. x \<in> cbox d b \<Longrightarrow> f x = f3 x"
    using homeomorphism_grouping_point_2 [OF 4 3] less by (auto simp: f4_eq f3_eq f2_eq f1_eq)
  show ?thesis
  proof (rule that [OF fg])
    show "f x \<in> cbox u v" if "x \<in> cbox c d" for x 
      using that f4_eq f_eq homeomorphism_image1 [OF 2]
      by (metis atLeastAtMost_iff box_real(2) image_eqI less(1) less_eq_real_def order_trans)
  qed
qed


lemma homeomorphism_grouping_point_4:
  fixes T :: "real set"
  assumes "open U" "open S" "connected S" "U \<noteq> {}" "finite K" "K \<subseteq> S" "U \<subseteq> S" "S \<subseteq> T"
  obtains f g where "homeomorphism T T f g"
                    "\<And>x. x \<in> K \<Longrightarrow> f x \<in> U" "{x. (\<not> (f x = x \<and> g x = x))} \<subseteq> S"
                    "bounded {x. (\<not> (f x = x \<and> g x = x))}"
proof -
  obtain c d where "box c d \<noteq> {}" "cbox c d \<subseteq> U"
  proof -
    obtain u where "u \<in> U"
      using \<open>U \<noteq> {}\<close> by blast
    then obtain e where "e > 0" "cball u e \<subseteq> U"
      using \<open>open U\<close> open_contains_cball by blast
    then show ?thesis
      by (rule_tac c=u and d="u+e" in that) (auto simp: dist_norm subset_iff)
  qed
  have "compact K"
    by (simp add: \<open>finite K\<close> finite_imp_compact)
  obtain a b where "box a b \<noteq> {}" "K \<subseteq> cbox a b" "cbox a b \<subseteq> S"
  proof (cases "K = {}")
    case True then show ?thesis
      using \<open>box c d \<noteq> {}\<close> \<open>cbox c d \<subseteq> U\<close> \<open>U \<subseteq> S\<close> that by blast
  next
    case False
    then obtain a b where "a \<in> K" "b \<in> K"
            and a: "\<And>x. x \<in> K \<Longrightarrow> a \<le> x" and b: "\<And>x. x \<in> K \<Longrightarrow> x \<le> b"
      using compact_attains_inf compact_attains_sup by (metis \<open>compact K\<close>)+
    obtain e where "e > 0" "cball b e \<subseteq> S"
      using \<open>open S\<close> open_contains_cball
      by (metis \<open>b \<in> K\<close> \<open>K \<subseteq> S\<close> subsetD)
    show ?thesis
    proof
      show "box a (b + e) \<noteq> {}"
        using \<open>0 < e\<close> \<open>b \<in> K\<close> a by force
      show "K \<subseteq> cbox a (b + e)"
        using \<open>0 < e\<close> a b by fastforce
      have "a \<in> S"
        using \<open>a \<in> K\<close> assms(6) by blast
      have "b + e \<in> S"
        using \<open>0 < e\<close> \<open>cball b e \<subseteq> S\<close>  by (force simp: dist_norm)
      show "cbox a (b + e) \<subseteq> S"
        using \<open>a \<in> S\<close> \<open>b + e \<in> S\<close> \<open>connected S\<close> connected_contains_Icc by auto
    qed
  qed
  obtain w z where "cbox w z \<subseteq> S" and sub_wz: "cbox a b \<union> cbox c d \<subseteq> box w z"
  proof -
    have "a \<in> S" "b \<in> S"
      using \<open>box a b \<noteq> {}\<close> \<open>cbox a b \<subseteq> S\<close> by auto
    moreover have "c \<in> S" "d \<in> S"
      using \<open>box c d \<noteq> {}\<close> \<open>cbox c d \<subseteq> U\<close> \<open>U \<subseteq> S\<close> by force+
    ultimately have "min a c \<in> S" "max b d \<in> S"
      by linarith+
    then obtain e1 e2 where "e1 > 0" "cball (min a c) e1 \<subseteq> S" "e2 > 0" "cball (max b d) e2 \<subseteq> S"
      using \<open>open S\<close> open_contains_cball by metis
    then have *: "min a c - e1 \<in> S" "max b d + e2 \<in> S"
      by (auto simp: dist_norm)
    show ?thesis
    proof
      show "cbox (min a c - e1) (max b d+ e2) \<subseteq> S"
        using * \<open>connected S\<close> connected_contains_Icc by auto
      show "cbox a b \<union> cbox c d \<subseteq> box (min a c - e1) (max b d + e2)"
        using \<open>0 < e1\<close> \<open>0 < e2\<close> by auto
    qed
  qed
  then
  obtain f g where hom: "homeomorphism (cbox w z) (cbox w z) f g"
               and "f w = w" "f z = z"
               and fin: "\<And>x. x \<in> cbox a b \<Longrightarrow> f x \<in> cbox c d"
    using homeomorphism_grouping_point_3 [of a b w z c d]
    using \<open>box a b \<noteq> {}\<close> \<open>box c d \<noteq> {}\<close> by blast
  have contfg: "continuous_on (cbox w z) f" "continuous_on (cbox w z) g"
    using hom homeomorphism_def by blast+
  define f' where "f' \<equiv> \<lambda>x. if x \<in> cbox w z then f x else x"
  define g' where "g' \<equiv> \<lambda>x. if x \<in> cbox w z then g x else x"
  show ?thesis
  proof
    have T: "cbox w z \<union> (T - box w z) = T"
      using \<open>cbox w z \<subseteq> S\<close> \<open>S \<subseteq> T\<close> by auto
    show "homeomorphism T T f' g'"
    proof
      have clo: "closedin (top_of_set (cbox w z \<union> (T - box w z))) (T - box w z)"
        by (metis Diff_Diff_Int Diff_subset T closedin_def open_box openin_open_Int topspace_euclidean_subtopology)
      have "\<And>x. \<lbrakk>w \<le> x \<and> x \<le> z; w < x \<longrightarrow> \<not> x < z\<rbrakk> \<Longrightarrow> f x = x"
        using \<open>f w = w\<close> \<open>f z = z\<close> by auto
      moreover have "\<And>x. \<lbrakk>w \<le> x \<and> x \<le> z; w < x \<longrightarrow> \<not> x < z\<rbrakk> \<Longrightarrow> g x = x"
        using \<open>f w = w\<close> \<open>f z = z\<close> hom homeomorphism_apply1 by fastforce
      ultimately
      have "continuous_on (cbox w z \<union> (T - box w z)) f'" "continuous_on (cbox w z \<union> (T - box w z)) g'"
        unfolding f'_def g'_def
        by (intro continuous_on_cases_local contfg continuous_on_id clo; auto simp: closed_subset)+
      then show "continuous_on T f'" "continuous_on T g'"
        by (simp_all only: T)
      show "f' ` T \<subseteq> T"
        unfolding f'_def
        by clarsimp (metis \<open>cbox w z \<subseteq> S\<close> \<open>S \<subseteq> T\<close> subsetD hom homeomorphism_def imageI mem_box_real(2))
      show "g' ` T \<subseteq> T"
        unfolding g'_def
        by clarsimp (metis \<open>cbox w z \<subseteq> S\<close> \<open>S \<subseteq> T\<close> subsetD hom homeomorphism_def imageI mem_box_real(2))
      show "\<And>x. x \<in> T \<Longrightarrow> g' (f' x) = x"
        unfolding f'_def g'_def
        using homeomorphism_apply1 [OF hom]  homeomorphism_image1 [OF hom] by fastforce
      show "\<And>y. y \<in> T \<Longrightarrow> f' (g' y) = y"
        unfolding f'_def g'_def
        using homeomorphism_apply2 [OF hom]  homeomorphism_image2 [OF hom] by fastforce
    qed
    show "\<And>x. x \<in> K \<Longrightarrow> f' x \<in> U"
      using fin sub_wz \<open>K \<subseteq> cbox a b\<close> \<open>cbox c d \<subseteq> U\<close> by (force simp: f'_def)
    show "{x. \<not> (f' x = x \<and> g' x = x)} \<subseteq> S"
      using \<open>cbox w z \<subseteq> S\<close> by (auto simp: f'_def g'_def)
    show "bounded {x. \<not> (f' x = x \<and> g' x = x)}"
    proof (rule bounded_subset [of "cbox w z"])
      show "bounded (cbox w z)"
        using bounded_cbox by blast
      show "{x. \<not> (f' x = x \<and> g' x = x)} \<subseteq> cbox w z"
        by (auto simp: f'_def g'_def)
    qed
  qed
qed

proposition\<^marker>\<open>tag unimportant\<close> homeomorphism_grouping_points_exists:
  fixes S :: "'a::euclidean_space set"
  assumes "open U" "open S" "connected S" "U \<noteq> {}" "finite K" "K \<subseteq> S" "U \<subseteq> S" "S \<subseteq> T"
  obtains f g where "homeomorphism T T f g" "{x. (\<not> (f x = x \<and> g x = x))} \<subseteq> S"
                    "bounded {x. (\<not> (f x = x \<and> g x = x))}" "\<And>x. x \<in> K \<Longrightarrow> f x \<in> U"
proof (cases "2 \<le> DIM('a)")
  case True
  have TS: "T \<subseteq> affine hull S"
    using affine_hull_open assms by blast
  have "infinite U"
    using \<open>open U\<close> \<open>U \<noteq> {}\<close> finite_imp_not_open by blast
  then obtain P where "P \<subseteq> U" "finite P" "card K = card P"
    using infinite_arbitrarily_large by metis
  then obtain \<gamma> where \<gamma>: "bij_betw \<gamma> K P"
    using \<open>finite K\<close> finite_same_card_bij by blast
  obtain f g where "homeomorphism T T f g" "\<And>i. i \<in> K \<Longrightarrow> f (id i) = \<gamma> i" "{x. \<not> (f x = x \<and> g x = x)} \<subseteq> S" "bounded {x. \<not> (f x = x \<and> g x = x)}"
  proof (rule homeomorphism_moving_points_exists [OF True \<open>open S\<close> \<open>connected S\<close> \<open>S \<subseteq> T\<close> \<open>finite K\<close>])
    show "\<And>i. i \<in> K \<Longrightarrow> id i \<in> S \<and> \<gamma> i \<in> S"
      using \<open>P \<subseteq> U\<close> \<open>bij_betw \<gamma> K P\<close> \<open>K \<subseteq> S\<close> \<open>U \<subseteq> S\<close> bij_betwE by blast
    show "pairwise (\<lambda>i j. id i \<noteq> id j \<and> \<gamma> i \<noteq> \<gamma> j) K"
      using \<gamma> by (auto simp: pairwise_def bij_betw_def inj_on_def)
  qed (use affine_hull_open assms that in auto)
  then show ?thesis
    using \<gamma> \<open>P \<subseteq> U\<close> bij_betwE by (fastforce simp add: intro!: that)
next
  case False
  with DIM_positive have "DIM('a) = 1"
    by (simp add: dual_order.antisym)
  then obtain h::"'a \<Rightarrow>real" and j
  where "linear h" "linear j"
    and noh: "\<And>x. norm(h x) = norm x" and noj: "\<And>y. norm(j y) = norm y"
    and hj:  "\<And>x. j(h x) = x" "\<And>y. h(j y) = y"
    and ranh: "surj h"
    using isomorphisms_UNIV_UNIV
    by (metis (mono_tags, hide_lams) DIM_real UNIV_eq_I range_eqI)
  obtain f g where hom: "homeomorphism (h ` T) (h ` T) f g"
               and f: "\<And>x. x \<in> h ` K \<Longrightarrow> f x \<in> h ` U"
               and sub: "{x. \<not> (f x = x \<and> g x = x)} \<subseteq> h ` S"
               and bou: "bounded {x. \<not> (f x = x \<and> g x = x)}"
    apply (rule homeomorphism_grouping_point_4 [of "h ` U" "h ` S" "h ` K" "h ` T"])
    by (simp_all add: assms image_mono  \<open>linear h\<close> open_surjective_linear_image connected_linear_image ranh)
  have jf: "j (f (h x)) = x \<longleftrightarrow> f (h x) = h x" for x
    by (metis hj)
  have jg: "j (g (h x)) = x \<longleftrightarrow> g (h x) = h x" for x
    by (metis hj)
  have cont_hj: "continuous_on X h"  "continuous_on Y j" for X Y
    by (simp_all add: \<open>linear h\<close> \<open>linear j\<close> linear_linear linear_continuous_on)
  show ?thesis
  proof
    show "homeomorphism T T (j \<circ> f \<circ> h) (j \<circ> g \<circ> h)"
    proof
      show "continuous_on T (j \<circ> f \<circ> h)" "continuous_on T (j \<circ> g \<circ> h)"
        using hom homeomorphism_def
        by (blast intro: continuous_on_compose cont_hj)+
      show "(j \<circ> f \<circ> h) ` T \<subseteq> T" "(j \<circ> g \<circ> h) ` T \<subseteq> T"
        by auto (metis (mono_tags, hide_lams) hj(1) hom homeomorphism_def imageE imageI)+
      show "\<And>x. x \<in> T \<Longrightarrow> (j \<circ> g \<circ> h) ((j \<circ> f \<circ> h) x) = x"
        using hj hom homeomorphism_apply1 by fastforce
      show "\<And>y. y \<in> T \<Longrightarrow> (j \<circ> f \<circ> h) ((j \<circ> g \<circ> h) y) = y"
        using hj hom homeomorphism_apply2 by fastforce
    qed
    show "{x. \<not> ((j \<circ> f \<circ> h) x = x \<and> (j \<circ> g \<circ> h) x = x)} \<subseteq> S"
    proof (clarsimp simp: jf jg hj)
      show "f (h x) = h x \<longrightarrow> g (h x) \<noteq> h x \<Longrightarrow> x \<in> S" for x
        using sub [THEN subsetD, of "h x"] hj by simp (metis imageE)
    qed
    have "bounded (j ` {x. (\<not> (f x = x \<and> g x = x))})"
      by (rule bounded_linear_image [OF bou]) (use \<open>linear j\<close> linear_conv_bounded_linear in auto)
    moreover
    have *: "{x. \<not>((j \<circ> f \<circ> h) x = x \<and> (j \<circ> g \<circ> h) x = x)} = j ` {x. (\<not> (f x = x \<and> g x = x))}"
      using hj by (auto simp: jf jg image_iff, metis+)
    ultimately show "bounded {x. \<not> ((j \<circ> f \<circ> h) x = x \<and> (j \<circ> g \<circ> h) x = x)}"
      by metis
    show "\<And>x. x \<in> K \<Longrightarrow> (j \<circ> f \<circ> h) x \<in> U"
      using f hj by fastforce
  qed
qed


proposition\<^marker>\<open>tag unimportant\<close> homeomorphism_grouping_points_exists_gen:
  fixes S :: "'a::euclidean_space set"
  assumes opeU: "openin (top_of_set S) U"
      and opeS: "openin (top_of_set (affine hull S)) S"
      and "U \<noteq> {}" "finite K" "K \<subseteq> S" and S: "S \<subseteq> T" "T \<subseteq> affine hull S" "connected S"
  obtains f g where "homeomorphism T T f g" "{x. (\<not> (f x = x \<and> g x = x))} \<subseteq> S"
                    "bounded {x. (\<not> (f x = x \<and> g x = x))}" "\<And>x. x \<in> K \<Longrightarrow> f x \<in> U"
proof (cases "2 \<le> aff_dim S")
  case True
  have opeU': "openin (top_of_set (affine hull S)) U"
    using opeS opeU openin_trans by blast
  obtain u where "u \<in> U" "u \<in> S"
    using \<open>U \<noteq> {}\<close> opeU openin_imp_subset by fastforce+
  have "infinite U"
  proof (rule infinite_openin [OF opeU \<open>u \<in> U\<close>])
    show "u islimpt S"
      using True \<open>u \<in> S\<close> assms(8) connected_imp_perfect_aff_dim by fastforce
  qed
  then obtain P where "P \<subseteq> U" "finite P" "card K = card P"
    using infinite_arbitrarily_large by metis
  then obtain \<gamma> where \<gamma>: "bij_betw \<gamma> K P"
    using \<open>finite K\<close> finite_same_card_bij by blast
  have "\<exists>f g. homeomorphism T T f g \<and> (\<forall>i \<in> K. f(id i) = \<gamma> i) \<and>
               {x. \<not> (f x = x \<and> g x = x)} \<subseteq> S \<and> bounded {x. \<not> (f x = x \<and> g x = x)}"
  proof (rule homeomorphism_moving_points_exists_gen [OF \<open>finite K\<close> _ _ True opeS S])
    show "\<And>i. i \<in> K \<Longrightarrow> id i \<in> S \<and> \<gamma> i \<in> S"
      by (metis id_apply opeU openin_contains_cball subsetCE \<open>P \<subseteq> U\<close> \<open>bij_betw \<gamma> K P\<close> \<open>K \<subseteq> S\<close> bij_betwE)
    show "pairwise (\<lambda>i j. id i \<noteq> id j \<and> \<gamma> i \<noteq> \<gamma> j) K"
      using \<gamma> by (auto simp: pairwise_def bij_betw_def inj_on_def)
  qed
  then show ?thesis
    using \<gamma> \<open>P \<subseteq> U\<close> bij_betwE by (fastforce simp add: intro!: that)
next
  case False
  with aff_dim_geq [of S] consider "aff_dim S = -1" | "aff_dim S = 0" | "aff_dim S = 1" by linarith
  then show ?thesis
  proof cases
    assume "aff_dim S = -1"
    then have "S = {}"
      using aff_dim_empty by blast
    then have "False"
      using \<open>U \<noteq> {}\<close> \<open>K \<subseteq> S\<close> openin_imp_subset [OF opeU] by blast
    then show ?thesis ..
  next
    assume "aff_dim S = 0"
    then obtain a where "S = {a}"
      using aff_dim_eq_0 by blast
    then have "K \<subseteq> U"
      using \<open>U \<noteq> {}\<close> \<open>K \<subseteq> S\<close> openin_imp_subset [OF opeU] by blast
    show ?thesis
      using \<open>K \<subseteq> U\<close> by (intro that [of id id]) (auto intro: homeomorphismI)
  next
    assume "aff_dim S = 1"
    then have "affine hull S homeomorphic (UNIV :: real set)"
      by (auto simp: homeomorphic_affine_sets)
    then obtain h::"'a\<Rightarrow>real" and j where homhj: "homeomorphism (affine hull S) UNIV h j"
      using homeomorphic_def by blast
    then have h: "\<And>x. x \<in> affine hull S \<Longrightarrow> j(h(x)) = x" and j: "\<And>y. j y \<in> affine hull S \<and> h(j y) = y"
      by (auto simp: homeomorphism_def)
    have connh: "connected (h ` S)"
      by (meson Topological_Spaces.connected_continuous_image \<open>connected S\<close> homeomorphism_cont1 homeomorphism_of_subsets homhj hull_subset top_greatest)
    have hUS: "h ` U \<subseteq> h ` S"
      by (meson homeomorphism_imp_open_map homeomorphism_of_subsets homhj hull_subset opeS opeU open_UNIV openin_open_eq)
    have opn: "openin (top_of_set (affine hull S)) U \<Longrightarrow> open (h ` U)" for U
      using homeomorphism_imp_open_map [OF homhj]  by simp
    have "open (h ` U)" "open (h ` S)"
      by (auto intro: opeS opeU openin_trans opn)
    then obtain f g where hom: "homeomorphism (h ` T) (h ` T) f g"
                 and f: "\<And>x. x \<in> h ` K \<Longrightarrow> f x \<in> h ` U"
                 and sub: "{x. \<not> (f x = x \<and> g x = x)} \<subseteq> h ` S"
                 and bou: "bounded {x. \<not> (f x = x \<and> g x = x)}"
      apply (rule homeomorphism_grouping_points_exists [of "h ` U" "h ` S" "h ` K" "h ` T"])
      using assms by (auto simp: connh hUS)
    have jf: "\<And>x. x \<in> affine hull S \<Longrightarrow> j (f (h x)) = x \<longleftrightarrow> f (h x) = h x"
      by (metis h j)
    have jg: "\<And>x. x \<in> affine hull S \<Longrightarrow> j (g (h x)) = x \<longleftrightarrow> g (h x) = h x"
      by (metis h j)
    have cont_hj: "continuous_on T h"  "continuous_on Y j" for Y
    proof (rule continuous_on_subset [OF _ \<open>T \<subseteq> affine hull S\<close>])
      show "continuous_on (affine hull S) h"
        using homeomorphism_def homhj by blast
    qed (meson continuous_on_subset homeomorphism_def homhj top_greatest)
    define f' where "f' \<equiv> \<lambda>x. if x \<in> affine hull S then (j \<circ> f \<circ> h) x else x"
    define g' where "g' \<equiv> \<lambda>x. if x \<in> affine hull S then (j \<circ> g \<circ> h) x else x"
    show ?thesis
    proof
      show "homeomorphism T T f' g'"
      proof
        have "continuous_on T (j \<circ> f \<circ> h)"
          using hom homeomorphism_def by (intro continuous_on_compose cont_hj) blast
        then show "continuous_on T f'"
          apply (rule continuous_on_eq)
          using \<open>T \<subseteq> affine hull S\<close> f'_def by auto
        have "continuous_on T (j \<circ> g \<circ> h)"
          using hom homeomorphism_def by (intro continuous_on_compose cont_hj) blast
        then show "continuous_on T g'"
          apply (rule continuous_on_eq)
          using \<open>T \<subseteq> affine hull S\<close> g'_def by auto
        show "f' ` T \<subseteq> T"
        proof (clarsimp simp: f'_def)
          fix x assume "x \<in> T"
          then have "f (h x) \<in> h ` T"
            by (metis (no_types) hom homeomorphism_def image_subset_iff subset_refl)
          then show "j (f (h x)) \<in> T"
            using \<open>T \<subseteq> affine hull S\<close> h by auto
        qed
        show "g' ` T \<subseteq> T"
        proof (clarsimp simp: g'_def)
          fix x assume "x \<in> T"
          then have "g (h x) \<in> h ` T"
            by (metis (no_types) hom homeomorphism_def image_subset_iff subset_refl)
          then show "j (g (h x)) \<in> T"
            using \<open>T \<subseteq> affine hull S\<close> h by auto
        qed
        show "\<And>x. x \<in> T \<Longrightarrow> g' (f' x) = x"
          using h j hom homeomorphism_apply1 by (fastforce simp add: f'_def g'_def)
        show "\<And>y. y \<in> T \<Longrightarrow> f' (g' y) = y"
          using h j hom homeomorphism_apply2 by (fastforce simp add: f'_def g'_def)
      qed
    next
      have \<section>: "\<And>x y. \<lbrakk>x \<in> affine hull S; h x = h y; y \<in> S\<rbrakk> \<Longrightarrow> x \<in> S"
        by (metis h hull_inc)
      show "{x. \<not> (f' x = x \<and> g' x = x)} \<subseteq> S"
        using sub by (simp add: f'_def g'_def jf jg) (force elim: \<section>)
    next
      have "compact (j ` closure {x. \<not> (f x = x \<and> g x = x)})"
        using bou by (auto simp: compact_continuous_image cont_hj)
      then have "bounded (j ` {x. \<not> (f x = x \<and> g x = x)})"
        by (rule bounded_closure_image [OF compact_imp_bounded])
      moreover
      have *: "{x \<in> affine hull S. j (f (h x)) \<noteq> x \<or> j (g (h x)) \<noteq> x} = j ` {x. (\<not> (f x = x \<and> g x = x))}"
        using h j by (auto simp: image_iff; metis)
      ultimately have "bounded {x \<in> affine hull S. j (f (h x)) \<noteq> x \<or> j (g (h x)) \<noteq> x}"
        by metis
      then show "bounded {x. \<not> (f' x = x \<and> g' x = x)}"
        by (simp add: f'_def g'_def Collect_mono bounded_subset)
    next
      show "f' x \<in> U" if "x \<in> K" for x
      proof -
        have "U \<subseteq> S"
          using opeU openin_imp_subset by blast
        then have "j (f (h x)) \<in> U"
          using f h hull_subset that by fastforce
        then show "f' x \<in> U"
          using \<open>K \<subseteq> S\<close> S f'_def that by auto
      qed
    qed
  qed
qed


subsection\<open>Nullhomotopic mappings\<close>

text\<open> A mapping out of a sphere is nullhomotopic iff it extends to the ball.
This even works out in the degenerate cases when the radius is \<open>\<le>\<close> 0, and
we also don't need to explicitly assume continuity since it's already implicit
in both sides of the equivalence.\<close>

lemma nullhomotopic_from_lemma:
  assumes contg: "continuous_on (cball a r - {a}) g"
      and fa: "\<And>e. 0 < e
               \<Longrightarrow> \<exists>d. 0 < d \<and> (\<forall>x. x \<noteq> a \<and> norm(x - a) < d \<longrightarrow> norm(g x - f a) < e)"
      and r: "\<And>x. x \<in> cball a r \<and> x \<noteq> a \<Longrightarrow> f x = g x"
    shows "continuous_on (cball a r) f"
proof (clarsimp simp: continuous_on_eq_continuous_within Ball_def)
  fix x
  assume x: "dist a x \<le> r"
  show "continuous (at x within cball a r) f"
  proof (cases "x=a")
    case True
    then show ?thesis
      by (metis continuous_within_eps_delta fa dist_norm dist_self r)
  next
    case False
    show ?thesis
    proof (rule continuous_transform_within [where f=g and d = "norm(x-a)"])
      have "\<exists>d>0. \<forall>x'\<in>cball a r.
                      dist x' x < d \<longrightarrow> dist (g x') (g x) < e" if "e>0" for e
      proof -
        obtain d where "d > 0"
           and d: "\<And>x'. \<lbrakk>dist x' a \<le> r; x' \<noteq> a; dist x' x < d\<rbrakk> \<Longrightarrow>
                                 dist (g x') (g x) < e"
          using contg False x \<open>e>0\<close>
          unfolding continuous_on_iff by (fastforce simp add: dist_commute intro: that)
        show ?thesis
          using \<open>d > 0\<close> \<open>x \<noteq> a\<close>
          by (rule_tac x="min d (norm(x - a))" in exI)
             (auto simp: dist_commute dist_norm [symmetric]  intro!: d)
      qed
      then show "continuous (at x within cball a r) g"
        using contg False by (auto simp: continuous_within_eps_delta)
      show "0 < norm (x - a)"
        using False by force
      show "x \<in> cball a r"
        by (simp add: x)
      show "\<And>x'. \<lbrakk>x' \<in> cball a r; dist x' x < norm (x - a)\<rbrakk>
        \<Longrightarrow> g x' = f x'"
        by (metis dist_commute dist_norm less_le r)
    qed
  qed
qed

proposition nullhomotopic_from_sphere_extension:
  fixes f :: "'M::euclidean_space \<Rightarrow> 'a::real_normed_vector"
  shows  "(\<exists>c. homotopic_with_canon (\<lambda>x. True) (sphere a r) S f (\<lambda>x. c)) \<longleftrightarrow>
          (\<exists>g. continuous_on (cball a r) g \<and> g ` (cball a r) \<subseteq> S \<and>
               (\<forall>x \<in> sphere a r. g x = f x))"
         (is "?lhs = ?rhs")
proof (cases r "0::real" rule: linorder_cases)
  case less
  then show ?thesis
    by (simp add: homotopic_on_emptyI)
next
  case equal
  show ?thesis
  proof
    assume L: ?lhs
    with equal have [simp]: "f a \<in> S"
      using homotopic_with_imp_subset1 by fastforce
    obtain h:: "real \<times> 'M \<Rightarrow> 'a" 
      where h: "continuous_on ({0..1} \<times> {a}) h" "h ` ({0..1} \<times> {a}) \<subseteq> S" "h (0, a) = f a"    
      using L equal by (auto simp: homotopic_with)
    then have "continuous_on (cball a r) (\<lambda>x. h (0, a))" "(\<lambda>x. h (0, a)) ` cball a r \<subseteq> S"
      by (auto simp: equal)
    then show ?rhs
      using h(3) local.equal by force
  next
    assume ?rhs
    then show ?lhs
      using equal continuous_on_const by (force simp add: homotopic_with)
  qed
next
  case greater
  let ?P = "continuous_on {x. norm(x - a) = r} f \<and> f ` {x. norm(x - a) = r} \<subseteq> S"
  have ?P if ?lhs using that
  proof
    fix c
    assume c: "homotopic_with_canon (\<lambda>x. True) (sphere a r) S f (\<lambda>x. c)"
    then have contf: "continuous_on (sphere a r) f" 
      by (metis homotopic_with_imp_continuous)
    moreover have fim: "f ` sphere a r \<subseteq> S"
      by (meson continuous_map_subtopology_eu c homotopic_with_imp_continuous_maps)
    show ?P
      using contf fim by (auto simp: sphere_def dist_norm norm_minus_commute)
  qed
  moreover have ?P if ?rhs using that
  proof
    fix g
    assume g: "continuous_on (cball a r) g \<and> g ` cball a r \<subseteq> S \<and> (\<forall>xa\<in>sphere a r. g xa = f xa)"
    then have "f ` {x. norm (x - a) = r} \<subseteq> S"
      using sphere_cball [of a r] unfolding image_subset_iff sphere_def
      by (metis dist_commute dist_norm mem_Collect_eq subset_eq)
    with g show ?P
      by (auto simp: dist_norm norm_minus_commute elim!: continuous_on_eq [OF continuous_on_subset])
  qed
  moreover have ?thesis if ?P
  proof
    assume ?lhs
    then obtain c where "homotopic_with_canon (\<lambda>x. True) (sphere a r) S (\<lambda>x. c) f"
      using homotopic_with_sym by blast
    then obtain h where conth: "continuous_on ({0..1::real} \<times> sphere a r) h"
                    and him: "h ` ({0..1} \<times> sphere a r) \<subseteq> S"
                    and h: "\<And>x. h(0, x) = c" "\<And>x. h(1, x) = f x"
      by (auto simp: homotopic_with_def)
    obtain b1::'M where "b1 \<in> Basis"
      using SOME_Basis by auto
    have "c \<in> h ` ({0..1} \<times> sphere a r)"
    proof
      show "c = h (0, a + r *\<^sub>R b1)"
        by (simp add: h)
      show "(0, a + r *\<^sub>R b1) \<in> {0..1::real} \<times> sphere a r"
        using greater \<open>b1 \<in> Basis\<close> by (auto simp: dist_norm)
    qed
    then have "c \<in> S"
      using him by blast
    have uconth: "uniformly_continuous_on ({0..1::real} \<times> (sphere a r)) h"
      by (force intro: compact_Times conth compact_uniformly_continuous)
    let ?g = "\<lambda>x. h (norm (x - a)/r,
                     a + (if x = a then r *\<^sub>R b1 else (r / norm(x - a)) *\<^sub>R (x - a)))"
    let ?g' = "\<lambda>x. h (norm (x - a)/r, a + (r / norm(x - a)) *\<^sub>R (x - a))"
    show ?rhs
    proof (intro exI conjI)
      have "continuous_on (cball a r - {a}) ?g'"
        using greater
        by (force simp: dist_norm norm_minus_commute intro: continuous_on_compose2 [OF conth] continuous_intros)
      then show "continuous_on (cball a r) ?g"
      proof (rule nullhomotopic_from_lemma)
        show "\<exists>d>0. \<forall>x. x \<noteq> a \<and> norm (x - a) < d \<longrightarrow> norm (?g' x - ?g a) < e" if "0 < e" for e
        proof -
          obtain d where "0 < d"
             and d: "\<And>x x'. \<lbrakk>x \<in> {0..1} \<times> sphere a r; x' \<in> {0..1} \<times> sphere a r; norm ( x' - x) < d\<rbrakk>
                        \<Longrightarrow> norm (h x' - h x) < e"
            using uniformly_continuous_onE [OF uconth \<open>0 < e\<close>] by (auto simp: dist_norm)
          have *: "norm (h (norm (x - a) / r,
                         a + (r / norm (x - a)) *\<^sub>R (x - a)) - h (0, a + r *\<^sub>R b1)) < e" (is  "norm (?ha - ?hb) < e")
                   if "x \<noteq> a" "norm (x - a) < r" "norm (x - a) < d * r" for x
          proof -
            have "norm (?ha - ?hb) = norm (?ha - h (0, a + (r / norm (x - a)) *\<^sub>R (x - a)))"
              by (simp add: h)
            also have "\<dots> < e"
              using greater \<open>0 < d\<close> \<open>b1 \<in> Basis\<close> that
              by (intro d) (simp_all add: dist_norm, simp add: field_simps) 
            finally show ?thesis .
          qed
          show ?thesis
            using greater \<open>0 < d\<close> 
            by (rule_tac x = "min r (d * r)" in exI) (auto simp: *)
        qed
        show "\<And>x. x \<in> cball a r \<and> x \<noteq> a \<Longrightarrow> ?g x = ?g' x"
          by auto
      qed
    next
      show "?g ` cball a r \<subseteq> S"
        using greater him \<open>c \<in> S\<close>
        by (force simp: h dist_norm norm_minus_commute)
    next
      show "\<forall>x\<in>sphere a r. ?g x = f x"
        using greater by (auto simp: h dist_norm norm_minus_commute)
    qed
  next
    assume ?rhs
    then obtain g where contg: "continuous_on (cball a r) g"
                    and gim: "g ` cball a r \<subseteq> S"
                    and gf: "\<forall>x \<in> sphere a r. g x = f x"
      by auto
    let ?h = "\<lambda>y. g (a + (fst y) *\<^sub>R (snd y - a))"
    have "continuous_on ({0..1} \<times> sphere a r) ?h"
    proof (rule continuous_on_compose2 [OF contg])
      show "continuous_on ({0..1} \<times> sphere a r) (\<lambda>x. a + fst x *\<^sub>R (snd x - a))"
        by (intro continuous_intros)
      qed (auto simp: dist_norm norm_minus_commute mult_left_le_one_le)
    moreover
    have "?h ` ({0..1} \<times> sphere a r) \<subseteq> S"
      by (auto simp: dist_norm norm_minus_commute mult_left_le_one_le gim [THEN subsetD])
    moreover
    have "\<forall>x\<in>sphere a r. ?h (0, x) = g a" "\<forall>x\<in>sphere a r. ?h (1, x) = f x"
      by (auto simp: dist_norm norm_minus_commute mult_left_le_one_le gf)
    ultimately have "homotopic_with_canon (\<lambda>x. True) (sphere a r) S (\<lambda>x. g a) f"
      by (auto simp: homotopic_with)
    then show ?lhs
      using homotopic_with_symD by blast
  qed
  ultimately
  show ?thesis by meson
qed 

end