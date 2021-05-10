theory FAE_Sequence
  imports "HOL-Library.Confluent_Quotient"
begin

type_synonym 'a seq = "nat \<Rightarrow> 'a"

abbreviation finite_range :: "('a \<Rightarrow> 'b) \<Rightarrow> bool" where "finite_range f \<equiv> finite (range f)"

lemma finite_range_pair:
  assumes 1: "finite_range (\<lambda>x. fst (f x))" and 2: "finite_range (\<lambda>x. snd (f x))"
  shows "finite_range f"
proof -
  have "range f \<subseteq> range (\<lambda>x. fst (f x)) \<times> range (\<lambda>x. snd (f x))"
    by(auto 4 3 intro: rev_image_eqI dest: sym)
  then show ?thesis by(rule finite_subset)(use assms in simp)
qed

definition seq_at :: "'a seq \<Rightarrow> 'a \<Rightarrow> nat set" where "seq_at f x = f -` {x}"

typedef 'a fseq = "{f :: 'a seq. finite_range f}" morphisms ap_fseq Abs_fseq
  by(rule exI[where x="\<lambda>_. undefined"]) simp

setup_lifting type_definition_fseq

lift_bnf 'a fseq [wits: "\<lambda>x. (\<lambda>_ :: nat. x)"]
  subgoal by(metis finite_imageI fun.set_map mem_Collect_eq)
  subgoal by(auto intro: finite_range_pair)
  subgoal by auto
  subgoal by auto
  done

lemma ap_map_fseq [simp]: "ap_fseq (map_fseq f x) = f \<circ> ap_fseq x"
  by transfer simp

lift_definition fseq_eq :: "'a fseq \<Rightarrow> 'a fseq \<Rightarrow> bool" is "\<lambda>f g. finite {n. f n \<noteq> g n}" .

lemma fseq_eq_unfold: "fseq_eq f g \<longleftrightarrow> finite {n. ap_fseq f n \<noteq> ap_fseq g n}"
  by transfer simp

lemma reflp_fseq_eq [simp]: "reflp fseq_eq"
  by(rule reflpI)(simp add: fseq_eq_unfold)

lemma symp_fseq_eq [simp]: "symp fseq_eq"
  by(rule sympI)(simp add: fseq_eq_unfold eq_commute)

lemma transp_fseq_eq [simp]: "transp fseq_eq"
  apply(rule transpI)
  subgoal for f g h unfolding fseq_eq_unfold
    by(rule finite_subset[where B="{n. ap_fseq f n \<noteq> ap_fseq g n} \<union> {n. ap_fseq g n \<noteq> ap_fseq h n}"]) auto
  done

lemma equivp_fseq_eq [simp]: "equivp fseq_eq"
  by(simp add: equivp_reflp_symp_transp)

functor map_fseq
  by(simp_all add: fseq.map_id0 fseq.map_comp fun_eq_iff)

quotient_type 'a fae_seq = "'a fseq" / fseq_eq by simp

lemma map_fseq_eq: "fseq_eq f g \<Longrightarrow> fseq_eq (map_fseq h f) (map_fseq h g)"
  unfolding fseq_eq_unfold by(auto elim!: finite_subset[rotated])

lemma finite_set_fseq [simp]: "finite (set_fseq x)"
  by transfer

interpretation wide_intersection_fseq: wide_intersection_finite fseq_eq map_fseq set_fseq
  by unfold_locales(simp_all add: map_fseq_eq fseq.map_id[unfolded id_def] fseq.set_map cong: fseq.map_cong)

lemma fseq_subdistributivity:
  assumes "A OO B \<noteq> bot"
  shows "rel_fseq A OO fseq_eq OO rel_fseq B \<le> fseq_eq OO rel_fseq (A OO B) OO fseq_eq"
proof(rule predicate2I; elim relcomppE; transfer fixing: A B)
  fix f and g g' :: "'c seq" and h
  assume fg: "rel_fun(=) A f g" and gg': "finite {n. g n \<noteq> g' n}" and g'h: "rel_fun (=) B g' h"
    and f: "finite_range f" and g: "finite_range g" and g': "finite_range g'" and h: "finite_range h"
  from assms obtain a c b where ac: "A a c" and cb: "B c b" by(auto simp add: fun_eq_iff)
  let ?X = "{n. g n \<noteq> g' n}"
  let ?f = "\<lambda>n. if n \<in> ?X then a else f n"
  let ?h = "\<lambda>n. if n \<in> ?X then b else h n"
  have "range ?f \<subseteq> insert a (range f)" by auto
  then have "finite_range ?f" by(rule finite_subset)(simp add: f)
  moreover have "range ?h \<subseteq> insert b (range h)" by auto
  then have "finite_range ?h" by(rule finite_subset)(simp add: h)
  moreover have "{n. f n \<noteq> ?f n} \<subseteq> ?X" by auto
  then have "finite {n. f n \<noteq> ?f n}" by(rule finite_subset)(simp add: gg')
  moreover have "{n. ?h n \<noteq> h n} \<subseteq> ?X" by auto
  then have "finite {n. ?h n \<noteq> h n}" by(rule finite_subset)(simp add: gg')
  moreover have "rel_fun (=) (A OO B) ?f ?h" using fg g'h ac cb by(auto simp add: rel_fun_def)
  ultimately
  show "\<exists>ya\<in>{f. finite_range f}. finite {n. f n \<noteq> ya n} \<and> (\<exists>yb\<in>{f. finite_range f}. rel_fun (=) (A OO B) ya yb \<and> finite {n. yb n \<noteq> h n})"
    unfolding mem_Collect_eq Bex_def by blast
qed

lift_bnf 'a fae_seq
  subgoal by(rule fseq_subdistributivity)
  subgoal by(rule wide_intersection_fseq.wide_intersection)
  done

lift_definition fseq_at :: "'a fseq \<Rightarrow> 'a \<Rightarrow> nat set" is seq_at .

lemma fae_vimage_singleton: "finite (f -` {x}) \<longleftrightarrow> finite (g -` {x})" if "finite {n. f n \<noteq> g n}"
proof
  assume *: "finite (g -` {x})"
  have "f -` {x} \<subseteq> g -` {x} \<union> {n. f n \<noteq> g n}" by auto
  thus "finite (f -` {x})" by(rule finite_subset)(use that * in auto)
next
  assume *: "finite (f -` {x})"
  have "g -` {x} \<subseteq> f -` {x} \<union> {n. f n \<noteq> g n}" by auto
  thus "finite (g -` {x})" by(rule finite_subset)(use that * in auto)
qed

lift_definition set_fae_seq_alt :: "'a fae_seq \<Rightarrow> 'a set" is "\<lambda>f. {a. infinite (fseq_at f a)}"
  by(transfer)(clarsimp simp add: set_eq_iff seq_at_def fae_vimage_singleton)

lemma fseq_at_infinite_Inr:
  "\<lbrakk>infinite (fseq_at f x); fseq_eq (map_fseq Inr f) g\<rbrakk> \<Longrightarrow> \<exists>x'\<in>set_fseq g. x \<in> Basic_BNFs.setr x'"
  apply transfer
  apply (auto simp add: seq_at_def vimage_def)
  apply (smt (verit, ccfv_SIG) finite_subset mem_Collect_eq setr.simps subsetI)
  done

lemma fseq_at_Inr_infinite:
  assumes "\<And>g. fseq_eq (map_fseq Inr f) g \<longrightarrow> (\<exists>x'\<in>set_fseq g. x \<in> Basic_BNFs.setr x')"
  shows "infinite (fseq_at f x)"
proof
  assume fin: "finite (fseq_at f x)"
  let ?g = "map_fseq (\<lambda>y. if x = y then Inl undefined else Inr y) f"
  have "fseq_eq (map_fseq Inr f) ?g" using fin
    by transfer(simp add: seq_at_def vimage_def eq_commute)
  with assms[of "?g"] show False by(auto simp add: fseq.set_map)
qed

lemma set_fae_seq_eq_alt: "set_fae_seq f = set_fae_seq_alt f"
  by transfer(use fseq_at_Inr_infinite in \<open>force simp add: fseq_at_infinite_Inr\<close>)

end
