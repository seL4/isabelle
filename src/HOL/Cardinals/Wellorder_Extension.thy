(*  Title:      HOL/Cardinals/Wellorder_Extension.thy
    Author:     Christian Sternagel, JAIST
*)

section \<open>Extending Well-founded Relations to Wellorders\<close>

theory Wellorder_Extension
imports Main Order_Union
begin

subsection \<open>Extending Well-founded Relations to Wellorders\<close>

text \<open>A \emph{downset} (also lower set, decreasing set, initial segment, or
downward closed set) is closed w.r.t.\ smaller elements.\<close>
definition downset_on where
  "downset_on A r = (\<forall>x y. (x, y) \<in> r \<and> y \<in> A \<longrightarrow> x \<in> A)"

(*
text {*Connection to order filters of the @{theory Cardinals} theory.*}
lemma (in wo_rel) ofilter_downset_on_conv:
  "ofilter A \<longleftrightarrow> downset_on A r \<and> A \<subseteq> Field r"
  by (auto simp: downset_on_def ofilter_def under_def)
*)

lemma downset_onI:
  "(\<And>x y. (x, y) \<in> r \<Longrightarrow> y \<in> A \<Longrightarrow> x \<in> A) \<Longrightarrow> downset_on A r"
  by (auto simp: downset_on_def)

lemma downset_onD:
  "downset_on A r \<Longrightarrow> (x, y) \<in> r \<Longrightarrow> y \<in> A \<Longrightarrow> x \<in> A"
  unfolding downset_on_def by blast

text \<open>Extensions of relations w.r.t.\ a given set.\<close>
definition extension_on where
  "extension_on A r s = (\<forall>x\<in>A. \<forall>y\<in>A. (x, y) \<in> s \<longrightarrow> (x, y) \<in> r)"

lemma extension_onI:
  "(\<And>x y. \<lbrakk>x \<in> A; y \<in> A; (x, y) \<in> s\<rbrakk> \<Longrightarrow> (x, y) \<in> r) \<Longrightarrow> extension_on A r s"
  by (auto simp: extension_on_def)

lemma extension_onD:
  "extension_on A r s \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> (x, y) \<in> s \<Longrightarrow> (x, y) \<in> r"
  by (auto simp: extension_on_def)

lemma downset_on_Union:
  assumes "\<And>r. r \<in> R \<Longrightarrow> downset_on (Field r) p"
  shows "downset_on (Field (\<Union>R)) p"
  using assms by (auto intro: downset_onI dest: downset_onD)

lemma chain_subset_extension_on_Union:
  assumes "chain\<^sub>\<subseteq> R" and "\<And>r. r \<in> R \<Longrightarrow> extension_on (Field r) r p"
  shows "extension_on (Field (\<Union>R)) (\<Union>R) p"
  using assms
  by (simp add: chain_subset_def extension_on_def)
     (metis (no_types) mono_Field subsetD)

lemma downset_on_empty [simp]: "downset_on {} p"
  by (auto simp: downset_on_def)

lemma extension_on_empty [simp]: "extension_on {} p q"
  by (auto simp: extension_on_def)

text \<open>Every well-founded relation can be extended to a wellorder.\<close>
theorem well_order_extension:
  assumes "wf p"
  shows "\<exists>w. p \<subseteq> w \<and> Well_order w"
proof -
  let ?K = "{r. Well_order r \<and> downset_on (Field r) p \<and> extension_on (Field r) r p}"
  define I where "I = init_seg_of \<inter> ?K \<times> ?K"
  have I_init: "I \<subseteq> init_seg_of" by (simp add: I_def)
  then have subch: "\<And>R. R \<in> Chains I \<Longrightarrow> chain\<^sub>\<subseteq> R"
    by (auto simp: init_seg_of_def chain_subset_def Chains_def)
  have Chains_wo: "\<And>R r. R \<in> Chains I \<Longrightarrow> r \<in> R \<Longrightarrow>
      Well_order r \<and> downset_on (Field r) p \<and> extension_on (Field r) r p"
    by (simp add: Chains_def I_def) blast
  have FI: "Field I = ?K" by (auto simp: I_def init_seg_of_def Field_def)
  then have 0: "Partial_order I"
    by (auto simp: partial_order_on_def preorder_on_def antisym_def antisym_init_seg_of refl_on_def
      trans_def I_def elim: trans_init_seg_of)
  have "\<Union>R \<in> ?K \<and> (\<forall>r\<in>R. (r,\<Union>R) \<in> I)" if "R \<in> Chains I" for R
  proof -
    from that have Ris: "R \<in> Chains init_seg_of" using mono_Chains [OF I_init] by blast
    have subch: "chain\<^sub>\<subseteq> R" using \<open>R \<in> Chains I\<close> I_init
      by (auto simp: init_seg_of_def chain_subset_def Chains_def)
    have "\<forall>r\<in>R. Refl r" and "\<forall>r\<in>R. trans r" and "\<forall>r\<in>R. antisym r" and
      "\<forall>r\<in>R. Total r" and "\<forall>r\<in>R. wf (r - Id)" and
      "\<And>r. r \<in> R \<Longrightarrow> downset_on (Field r) p" and
      "\<And>r. r \<in> R \<Longrightarrow> extension_on (Field r) r p"
      using Chains_wo [OF \<open>R \<in> Chains I\<close>] by (simp_all add: order_on_defs)
    have "Refl (\<Union>R)" using \<open>\<forall>r\<in>R. Refl r\<close>  unfolding refl_on_def by fastforce
    moreover have "trans (\<Union>R)"
      by (rule chain_subset_trans_Union [OF subch \<open>\<forall>r\<in>R. trans r\<close>])
    moreover have "antisym (\<Union>R)"
      by (rule chain_subset_antisym_Union [OF subch \<open>\<forall>r\<in>R. antisym r\<close>])
    moreover have "Total (\<Union>R)"
      by (rule chain_subset_Total_Union [OF subch \<open>\<forall>r\<in>R. Total r\<close>])
    moreover have "wf ((\<Union>R) - Id)"
    proof -
      have "(\<Union>R) - Id = \<Union>{r - Id | r. r \<in> R}" by blast
      with \<open>\<forall>r\<in>R. wf (r - Id)\<close> wf_Union_wf_init_segs [OF Chains_inits_DiffI [OF Ris]]
      show ?thesis by fastforce
    qed
    ultimately have "Well_order (\<Union>R)" by (simp add: order_on_defs)
    moreover have "\<forall>r\<in>R. r initial_segment_of \<Union>R" using Ris
      by (simp add: Chains_init_seg_of_Union)
    moreover have "downset_on (Field (\<Union>R)) p"
      by (rule downset_on_Union [OF \<open>\<And>r. r \<in> R \<Longrightarrow> downset_on (Field r) p\<close>])
    moreover have "extension_on (Field (\<Union>R)) (\<Union>R) p"
      by (rule chain_subset_extension_on_Union [OF subch \<open>\<And>r. r \<in> R \<Longrightarrow> extension_on (Field r) r p\<close>])
    ultimately show ?thesis
      using mono_Chains [OF I_init] and \<open>R \<in> Chains I\<close>
      by (simp (no_asm) add: I_def del: Field_Union) (metis Chains_wo)
  qed
  then have 1: "\<exists>u\<in>Field I. \<forall>r\<in>R. (r, u) \<in> I" if "R\<in>Chains I" for R 
    using that by (subst FI) blast
  txt \<open>Zorn's Lemma yields a maximal wellorder m.\<close>
  from Zorns_po_lemma [OF 0 1] obtain m :: "('a \<times> 'a) set"
    where "Well_order m" and "downset_on (Field m) p" and "extension_on (Field m) m p" and
    max: "\<forall>r. Well_order r \<and> downset_on (Field r) p \<and> extension_on (Field r) r p \<and>
      (m, r) \<in> I \<longrightarrow> r = m"
    by (auto simp: FI)
  have "Field p \<subseteq> Field m"
  proof (rule ccontr)
    let ?Q = "Field p - Field m"
    assume "\<not> (Field p \<subseteq> Field m)"
    with assms [unfolded wf_eq_minimal, THEN spec, of ?Q]
      obtain x where "x \<in> Field p" and "x \<notin> Field m" and
      min: "\<forall>y. (y, x) \<in> p \<longrightarrow> y \<notin> ?Q" by blast
    txt \<open>Add \<^term>\<open>x\<close> as topmost element to \<^term>\<open>m\<close>.\<close>
    let ?s = "{(y, x) | y. y \<in> Field m}"
    let ?m = "insert (x, x) m \<union> ?s"
    have Fm: "Field ?m = insert x (Field m)" by (auto simp: Field_def)
    have "Refl m" and "trans m" and "antisym m" and "Total m" and "wf (m - Id)"
      using \<open>Well_order m\<close> by (simp_all add: order_on_defs)
    txt \<open>We show that the extension is a wellorder.\<close>
    have "Refl ?m" using \<open>Refl m\<close> Fm by (auto simp: refl_on_def)
    moreover have "trans ?m" using \<open>trans m\<close> \<open>x \<notin> Field m\<close>
      unfolding trans_def Field_def Domain_unfold Domain_converse [symmetric] by blast
    moreover have "antisym ?m" using \<open>antisym m\<close> \<open>x \<notin> Field m\<close>
      unfolding antisym_def Field_def Domain_unfold Domain_converse [symmetric] by blast
    moreover have "Total ?m" using \<open>Total m\<close> Fm by (auto simp: Relation.total_on_def)
    moreover have "wf (?m - Id)"
    proof -
      have "wf ?s" using \<open>x \<notin> Field m\<close>
        by (simp add: wf_eq_minimal Field_def Domain_unfold Domain_converse [symmetric]) metis
      thus ?thesis using \<open>wf (m - Id)\<close> \<open>x \<notin> Field m\<close>
        wf_subset [OF \<open>wf ?s\<close> Diff_subset]
        by (fastforce intro!: wf_Un simp add: Un_Diff Field_def)
    qed
    ultimately have "Well_order ?m" by (simp add: order_on_defs)
    moreover have "extension_on (Field ?m) ?m p"
      using \<open>extension_on (Field m) m p\<close> \<open>downset_on (Field m) p\<close>
      by (subst Fm) (auto simp: extension_on_def dest: downset_onD)
    moreover have "downset_on (Field ?m) p"
      apply (subst Fm)
      using \<open>downset_on (Field m) p\<close> and min
      unfolding downset_on_def Field_def by blast
    moreover have "(m, ?m) \<in> I"
      using \<open>Well_order m\<close> and \<open>Well_order ?m\<close> and
      \<open>downset_on (Field m) p\<close> and \<open>downset_on (Field ?m) p\<close> and
      \<open>extension_on (Field m) m p\<close> and \<open>extension_on (Field ?m) ?m p\<close> and
      \<open>Refl m\<close> and \<open>x \<notin> Field m\<close>
      by (auto simp: I_def init_seg_of_def refl_on_def)
    ultimately
    \<comment> \<open>This contradicts maximality of m:\<close>
    show False using max and \<open>x \<notin> Field m\<close> unfolding Field_def by blast
  qed
  have "p \<subseteq> m"
    using \<open>Field p \<subseteq> Field m\<close> and \<open>extension_on (Field m) m p\<close>
    unfolding Field_def extension_on_def by auto fast
  with \<open>Well_order m\<close> show ?thesis by blast
qed

text \<open>Every well-founded relation can be extended to a total wellorder.\<close>
corollary total_well_order_extension:
  assumes "wf p"
  shows "\<exists>w. p \<subseteq> w \<and> Well_order w \<and> Field w = UNIV"
proof -
  from well_order_extension [OF assms] obtain w
    where "p \<subseteq> w" and wo: "Well_order w" by blast
  let ?A = "UNIV - Field w"
  from well_order_on [of ?A] obtain w' where wo': "well_order_on ?A w'" ..
  have [simp]: "Field w' = ?A" using well_order_on_Well_order [OF wo'] by simp
  have *: "Field w \<inter> Field w' = {}" by simp
  let ?w = "w \<union>o w'"
  have "p \<subseteq> ?w" using \<open>p \<subseteq> w\<close> by (auto simp: Osum_def)
  moreover have "Well_order ?w" using Osum_Well_order [OF * wo] and wo' by simp
  moreover have "Field ?w = UNIV" by (simp add: Field_Osum)
  ultimately show ?thesis by blast
qed

corollary well_order_on_extension:
  assumes "wf p" and "Field p \<subseteq> A"
  shows "\<exists>w. p \<subseteq> w \<and> well_order_on A w"
proof -
  from total_well_order_extension [OF \<open>wf p\<close>] obtain r
    where "p \<subseteq> r" and wo: "Well_order r" and univ: "Field r = UNIV" by blast
  let ?r = "{(x, y). x \<in> A \<and> y \<in> A \<and> (x, y) \<in> r}"
  from \<open>p \<subseteq> r\<close> have "p \<subseteq> ?r" using \<open>Field p \<subseteq> A\<close> by (auto simp: Field_def)
  have "Refl r" "trans r" "antisym r" "Total r" "wf (r - Id)"
    using \<open>Well_order r\<close> by (simp_all add: order_on_defs)
  have "refl_on A ?r" using \<open>Refl r\<close> by (auto simp: refl_on_def univ)
  moreover have "trans ?r" using \<open>trans r\<close>
    unfolding trans_def by blast
  moreover have "antisym ?r" using \<open>antisym r\<close>
    unfolding antisym_def by blast
  moreover have "total_on A ?r" using \<open>Total r\<close> by (simp add: total_on_def univ)
  moreover have "wf (?r - Id)" by (rule wf_subset [OF \<open>wf(r - Id)\<close>]) blast
  ultimately have "well_order_on A ?r" by (simp add: order_on_defs)
  with \<open>p \<subseteq> ?r\<close> show ?thesis by blast
qed

end
