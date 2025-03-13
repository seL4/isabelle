(*  Title:      HOL/BNF_Wellorder_Embedding.thy
    Author:     Andrei Popescu, TU Muenchen
    Copyright   2012

Well-order embeddings as needed by bounded natural functors.
*)

section \<open>Well-Order Embeddings as Needed by Bounded Natural Functors\<close>

theory BNF_Wellorder_Embedding
  imports Hilbert_Choice BNF_Wellorder_Relation
begin

text\<open>In this section, we introduce well-order {\em embeddings} and {\em isomorphisms} and
prove their basic properties.  The notion of embedding is considered from the point
of view of the theory of ordinals, and therefore requires the source to be injected
as an {\em initial segment} (i.e., {\em order filter}) of the target.  A main result
of this section is the existence of embeddings (in one direction or another) between
any two well-orders, having as a consequence the fact that, given any two sets on
any two types, one is smaller than (i.e., can be injected into) the other.\<close>


subsection \<open>Auxiliaries\<close>

lemma UNION_inj_on_ofilter:
  assumes WELL: "Well_order r" and
    OF: "\<And> i. i \<in> I \<Longrightarrow> wo_rel.ofilter r (A i)" and
    INJ: "\<And> i. i \<in> I \<Longrightarrow> inj_on f (A i)"
  shows "inj_on f (\<Union>i \<in> I. A i)"
proof-
  have "wo_rel r" using WELL by (simp add: wo_rel_def)
  hence "\<And> i j. \<lbrakk>i \<in> I; j \<in> I\<rbrakk> \<Longrightarrow> A i <= A j \<or> A j <= A i"
    using wo_rel.ofilter_linord[of r] OF by blast
  with WELL INJ show ?thesis
    by (auto simp add: inj_on_UNION_chain)
qed

lemma under_underS_bij_betw:
  assumes WELL: "Well_order r" and WELL': "Well_order r'" and
    IN: "a \<in> Field r" and IN': "f a \<in> Field r'" and
    BIJ: "bij_betw f (underS r a) (underS r' (f a))"
  shows "bij_betw f (under r a) (under r' (f a))"
proof-
  have "a \<notin> underS r a \<and> f a \<notin> underS r' (f a)"
    unfolding underS_def by auto
  moreover
  {have "Refl r \<and> Refl r'" using WELL WELL'
      by (auto simp add: order_on_defs)
    hence "under r a = underS r a \<union> {a} \<and>
          under r' (f a) = underS r' (f a) \<union> {f a}"
      using IN IN' by(auto simp add: Refl_under_underS)
  }
  ultimately show ?thesis
    using BIJ notIn_Un_bij_betw[of a "underS r a" f "underS r' (f a)"] by auto
qed


subsection \<open>(Well-order) embeddings, strict embeddings, isomorphisms and order-compatible
functions\<close>

text\<open>Standardly, a function is an embedding of a well-order in another if it injectively and
order-compatibly maps the former into an order filter of the latter.
Here we opt for a more succinct definition (operator \<open>embed\<close>),
asking that, for any element in the source, the function should be a bijection
between the set of strict lower bounds of that element
and the set of strict lower bounds of its image.  (Later we prove equivalence with
the standard definition -- lemma \<open>embed_iff_compat_inj_on_ofilter\<close>.)
A {\em strict embedding} (operator \<open>embedS\<close>)  is a non-bijective embedding
and an isomorphism (operator \<open>iso\<close>) is a bijective embedding.\<close>

definition embed :: "'a rel \<Rightarrow> 'a' rel \<Rightarrow> ('a \<Rightarrow> 'a') \<Rightarrow> bool"
  where
    "embed r r' f \<equiv> \<forall>a \<in> Field r. bij_betw f (under r a) (under r' (f a))"

lemmas embed_defs = embed_def embed_def[abs_def]

text \<open>Strict embeddings:\<close>

definition embedS :: "'a rel \<Rightarrow> 'a' rel \<Rightarrow> ('a \<Rightarrow> 'a') \<Rightarrow> bool"
  where
    "embedS r r' f \<equiv> embed r r' f \<and> \<not> bij_betw f (Field r) (Field r')"

lemmas embedS_defs = embedS_def embedS_def[abs_def]

definition iso :: "'a rel \<Rightarrow> 'a' rel \<Rightarrow> ('a \<Rightarrow> 'a') \<Rightarrow> bool"
  where
    "iso r r' f \<equiv> embed r r' f \<and> bij_betw f (Field r) (Field r')"

lemmas iso_defs = iso_def iso_def[abs_def]

definition compat :: "'a rel \<Rightarrow> 'a' rel \<Rightarrow> ('a \<Rightarrow> 'a') \<Rightarrow> bool"
  where
    "compat r r' f \<equiv> \<forall>a b. (a,b) \<in> r \<longrightarrow> (f a, f b) \<in> r'"

lemma compat_wf:
  assumes CMP: "compat r r' f" and WF: "wf r'"
  shows "wf r"
proof-
  have "r \<le> inv_image r' f"
    unfolding inv_image_def using CMP
    by (auto simp add: compat_def)
  with WF show ?thesis
    using wf_inv_image[of r' f] wf_subset[of "inv_image r' f"] by auto
qed

lemma id_embed: "embed r r id"
  by(auto simp add: id_def embed_def bij_betw_def)

lemma id_iso: "iso r r id"
  by(auto simp add: id_def embed_def iso_def bij_betw_def)

lemma embed_compat:
  assumes EMB: "embed r r' f"
  shows "compat r r' f"
  unfolding compat_def
proof clarify
  fix a b
  assume *: "(a,b) \<in> r"
  hence 1: "b \<in> Field r" using Field_def[of r] by blast
  have "a \<in> under r b"
    using * under_def[of r] by simp
  hence "f a \<in> under r' (f b)"
    using EMB embed_def[of r r' f]
      bij_betw_def[of f "under r b" "under r' (f b)"]
      image_def[of f "under r b"] 1 by auto
  thus "(f a, f b) \<in> r'"
    by (auto simp add: under_def)
qed

lemma embed_in_Field:
  assumes EMB: "embed r r' f" and IN: "a \<in> Field r"
  shows "f a \<in> Field r'"
proof -
  have "a \<in> Domain r \<or> a \<in> Range r"
    using IN unfolding Field_def by blast
  then show ?thesis
    using embed_compat [OF EMB]
    unfolding Field_def compat_def by force
qed

lemma comp_embed:
  assumes EMB: "embed r r' f" and EMB': "embed r' r'' f'"
  shows "embed r r'' (f' \<circ> f)"
proof(unfold embed_def, auto)
  fix a assume *: "a \<in> Field r"
  hence "bij_betw f (under r a) (under r' (f a))"
    using embed_def[of r] EMB by auto
  moreover
  {have "f a \<in> Field r'"
      using EMB * by (auto simp add: embed_in_Field)
    hence "bij_betw f' (under r' (f a)) (under r'' (f' (f a)))"
      using embed_def[of r'] EMB' by auto
  }
  ultimately
  show "bij_betw (f' \<circ> f) (under r a) (under r'' (f'(f a)))"
    by(auto simp add: bij_betw_trans)
qed

lemma comp_iso:
  assumes EMB: "iso r r' f" and EMB': "iso r' r'' f'"
  shows "iso r r'' (f' \<circ> f)"
  using assms unfolding iso_def
  by (auto simp add: comp_embed bij_betw_trans)

text\<open>That \<open>embedS\<close> is also preserved by function composition shall be proved only later.\<close>

lemma embed_Field: "embed r r' f \<Longrightarrow> f`(Field r) \<le> Field r'"
  by (auto simp add: embed_in_Field)

lemma embed_preserves_ofilter:
  assumes WELL: "Well_order r" and WELL': "Well_order r'" and
    EMB: "embed r r' f" and OF: "wo_rel.ofilter r A"
  shows "wo_rel.ofilter r' (f`A)"
proof-
  (* Preliminary facts *)
  from WELL have Well: "wo_rel r" unfolding wo_rel_def .
  from WELL' have Well': "wo_rel r'" unfolding wo_rel_def .
  from OF have 0: "A \<le> Field r" by(auto simp add: Well wo_rel.ofilter_def)
      (* Main proof *)
  show ?thesis  using Well' WELL EMB 0 embed_Field[of r r' f]
  proof(unfold wo_rel.ofilter_def, auto simp add: image_def)
    fix a b'
    assume *: "a \<in> A" and **: "b' \<in> under r' (f a)"
    hence "a \<in> Field r" using 0 by auto
    hence "bij_betw f (under r a) (under r' (f a))"
      using * EMB by (auto simp add: embed_def)
    hence "f`(under r a) = under r' (f a)"
      by (simp add: bij_betw_def)
    with ** image_def[of f "under r a"] obtain b where
      1: "b \<in> under r a \<and> b' = f b" by blast
    hence "b \<in> A" using Well * OF
      by (auto simp add: wo_rel.ofilter_def)
    with 1 show "\<exists>b \<in> A. b' = f b" by blast
  qed
qed

lemma embed_Field_ofilter:
  assumes WELL: "Well_order r" and WELL': "Well_order r'" and
    EMB: "embed r r' f"
  shows "wo_rel.ofilter r' (f`(Field r))"
proof-
  have "wo_rel.ofilter r (Field r)"
    using WELL by (auto simp add: wo_rel_def wo_rel.Field_ofilter)
  with WELL WELL' EMB
  show ?thesis by (auto simp add: embed_preserves_ofilter)
qed

lemma embed_inj_on:
  assumes WELL: "Well_order r" and EMB: "embed r r' f"
  shows "inj_on f (Field r)"
proof(unfold inj_on_def, clarify)
  (* Preliminary facts *)
  from WELL have Well: "wo_rel r" unfolding wo_rel_def .
  with wo_rel.TOTAL[of r]
  have Total: "Total r" by simp
  from Well wo_rel.REFL[of r]
  have Refl: "Refl r" by simp
      (* Main proof *)
  fix a b
  assume *: "a \<in> Field r" and **: "b \<in> Field r" and
    ***: "f a = f b"
  hence 1: "a \<in> Field r \<and> b \<in> Field r"
    unfolding Field_def by auto
  {assume "(a,b) \<in> r"
    hence "a \<in> under r b \<and> b \<in> under r b"
      using Refl by (auto simp add: under_def refl_on_def Field_def)
    hence "a = b"
      using EMB 1 ***
      by (auto simp add: embed_def bij_betw_def inj_on_def)
  }
  moreover
  {assume "(b,a) \<in> r"
    hence "a \<in> under r a \<and> b \<in> under r a"
      using Refl by (auto simp add: under_def refl_on_def Field_def)
    hence "a = b"
      using EMB 1 ***
      by (auto simp add: embed_def bij_betw_def inj_on_def)
  }
  ultimately
  show "a = b" using Total 1
    by (auto simp add: total_on_def)
qed

lemma embed_underS:
  assumes WELL: "Well_order r" and
    EMB: "embed r r' f" and IN: "a \<in> Field r"
  shows "bij_betw f (underS r a) (underS r' (f a))"
proof-
  have "f a \<in> Field r'" using assms embed_Field[of r r' f] by auto
  then have 0: "under r a = underS r a \<union> {a}"
    by (simp add: IN Refl_under_underS WELL wo_rel.REFL wo_rel.intro)
  moreover have 1: "bij_betw f (under r a) (under r' (f a))"
    using assms by (auto simp add: embed_def) 
  moreover have "under r' (f a) = underS r' (f a) \<union> {f a}"
  proof
    show "under r' (f a) \<subseteq> underS r' (f a) \<union> {f a}"
      using underS_def under_def by fastforce
    show "underS r' (f a) \<union> {f a} \<subseteq> under r' (f a)"
      using bij_betwE 0 1 underS_subset_under by fastforce
  qed
  moreover have "a \<notin> underS r a \<and> f a \<notin> underS r' (f a)"
    unfolding underS_def by blast
  ultimately show ?thesis
    by (auto simp add: notIn_Un_bij_betw3)
qed

lemma embed_iff_compat_inj_on_ofilter:
  assumes WELL: "Well_order r" and WELL': "Well_order r'"
  shows "embed r r' f = (compat r r' f \<and> inj_on f (Field r) \<and> wo_rel.ofilter r' (f`(Field r)))"
  using assms
proof(auto simp add: embed_compat embed_inj_on embed_Field_ofilter,
    unfold embed_def, auto) (* get rid of one implication *)
  fix a
  assume *: "inj_on f (Field r)" and
    **: "compat r r' f" and
    ***: "wo_rel.ofilter r' (f`(Field r))" and
    ****: "a \<in> Field r"
    (* Preliminary facts *)
  have Well: "wo_rel r"
    using WELL wo_rel_def[of r] by simp
  hence Refl: "Refl r"
    using wo_rel.REFL[of r] by simp
  have Total: "Total r"
    using Well wo_rel.TOTAL[of r] by simp
  have Well': "wo_rel r'"
    using WELL' wo_rel_def[of r'] by simp
  hence Antisym': "antisym r'"
    using wo_rel.ANTISYM[of r'] by simp
  have "(a,a) \<in> r"
    using **** Well wo_rel.REFL[of r]
      refl_on_def[of _ r] by auto
  hence "(f a, f a) \<in> r'"
    using ** by(auto simp add: compat_def)
  hence 0: "f a \<in> Field r'"
    unfolding Field_def by auto
  have "f a \<in> f`(Field r)"
    using **** by auto
  hence 2: "under r' (f a) \<le> f`(Field r)"
    using Well' *** wo_rel.ofilter_def[of r' "f`(Field r)"] by fastforce
      (* Main proof *)
  show "bij_betw f (under r a) (under r' (f a))"
  proof(unfold bij_betw_def, auto)
    show  "inj_on f (under r a)" by (rule subset_inj_on[OF * under_Field])
  next
    fix b assume "b \<in> under r a"
    thus "f b \<in> under r' (f a)"
      unfolding under_def using **
      by (auto simp add: compat_def)
  next
    fix b' assume *****: "b' \<in> under r' (f a)"
    hence "b' \<in> f`(Field r)"
      using 2 by auto
    with Field_def[of r] obtain b where
      3: "b \<in> Field r" and 4: "b' = f b" by auto
    have "(b,a) \<in> r"
    proof-
      {assume "(a,b) \<in> r"
        with ** 4 have "(f a, b') \<in> r'"
          by (auto simp add: compat_def)
        with ***** Antisym' have "f a = b'"
          by(auto simp add: under_def antisym_def)
        with 3 **** 4 * have "a = b"
          by(auto simp add: inj_on_def)
      }
      moreover
      {assume "a = b"
        hence "(b,a) \<in> r" using Refl **** 3
          by (auto simp add: refl_on_def)
      }
      ultimately
      show ?thesis using Total **** 3 by (fastforce simp add: total_on_def)
    qed
    with 4 show  "b' \<in> f`(under r a)"
      unfolding under_def by auto
  qed
qed

lemma inv_into_ofilter_embed:
  assumes WELL: "Well_order r" and OF: "wo_rel.ofilter r A" and
    BIJ: "\<forall>b \<in> A. bij_betw f (under r b) (under r' (f b))" and
    IMAGE: "f ` A = Field r'"
  shows "embed r' r (inv_into A f)"
proof-
  (* Preliminary facts *)
  have Well: "wo_rel r"
    using WELL wo_rel_def[of r] by simp
  have Refl: "Refl r"
    using Well wo_rel.REFL[of r] by simp
  have Total: "Total r"
    using Well wo_rel.TOTAL[of r] by simp
      (* Main proof *)
  have 1: "bij_betw f A (Field r')"
  proof(unfold bij_betw_def inj_on_def, auto simp add: IMAGE)
    fix b1 b2
    assume *: "b1 \<in> A" and **: "b2 \<in> A" and
      ***: "f b1 = f b2"
    have 11: "b1 \<in> Field r \<and> b2 \<in> Field r"
      using * ** Well OF by (auto simp add: wo_rel.ofilter_def)
    moreover
    {assume "(b1,b2) \<in> r"
      hence "b1 \<in> under r b2 \<and> b2 \<in> under r b2"
        unfolding under_def using 11 Refl
        by (auto simp add: refl_on_def)
      hence "b1 = b2" using BIJ * ** ***
        by (simp add: bij_betw_def inj_on_def)
    }
    moreover
    {assume "(b2,b1) \<in> r"
      hence "b1 \<in> under r b1 \<and> b2 \<in> under r b1"
        unfolding under_def using 11 Refl
        by (auto simp add: refl_on_def)
      hence "b1 = b2" using BIJ * ** ***
        by (simp add: bij_betw_def inj_on_def)
    }
    ultimately
    show "b1 = b2"
      using Total by (auto simp add: total_on_def)
  qed
    (*  *)
  let ?f' = "(inv_into A f)"
    (*  *)
  have 2: "\<forall>b \<in> A. bij_betw ?f' (under r' (f b)) (under r b)"
  proof(clarify)
    fix b assume *: "b \<in> A"
    hence "under r b \<le> A"
      using Well OF by(auto simp add: wo_rel.ofilter_def)
    moreover
    have "f ` (under r b) = under r' (f b)"
      using * BIJ by (auto simp add: bij_betw_def)
    ultimately
    show "bij_betw ?f' (under r' (f b)) (under r b)"
      using 1 by (auto simp add: bij_betw_inv_into_subset)
  qed
    (*  *)
  have 3: "\<forall>b' \<in> Field r'. bij_betw ?f' (under r' b') (under r (?f' b'))"
  proof(clarify)
    fix b' assume *: "b' \<in> Field r'"
    have "b' = f (?f' b')" using * 1
      by (auto simp add: bij_betw_inv_into_right)
    moreover
    {obtain b where 31: "b \<in> A" and "f b = b'" using IMAGE * by force
      hence "?f' b' = b" using 1 by (auto simp add: bij_betw_inv_into_left)
      with 31 have "?f' b' \<in> A" by auto
    }
    ultimately
    show  "bij_betw ?f' (under r' b') (under r (?f' b'))"
      using 2 by auto
  qed
    (*  *)
  thus ?thesis unfolding embed_def .
qed

lemma inv_into_underS_embed:
  assumes WELL: "Well_order r" and
    BIJ: "\<forall>b \<in> underS r a. bij_betw f (under r b) (under r' (f b))" and
    IN: "a \<in> Field r" and
    IMAGE: "f ` (underS r a) = Field r'"
  shows "embed r' r (inv_into (underS r a) f)"
  using assms
  by(auto simp add: wo_rel_def wo_rel.underS_ofilter inv_into_ofilter_embed)

lemma inv_into_Field_embed:
  assumes WELL: "Well_order r" and EMB: "embed r r' f" and
    IMAGE: "Field r' \<le> f ` (Field r)"
  shows "embed r' r (inv_into (Field r) f)"
proof-
  have "(\<forall>b \<in> Field r. bij_betw f (under r b) (under r' (f b)))"
    using EMB by (auto simp add: embed_def)
  moreover
  have "f ` (Field r) \<le> Field r'"
    using EMB WELL by (auto simp add: embed_Field)
  ultimately
  show ?thesis using assms
    by(auto simp add: wo_rel_def wo_rel.Field_ofilter inv_into_ofilter_embed)
qed

lemma inv_into_Field_embed_bij_betw:
  assumes EMB: "embed r r' f" and BIJ: "bij_betw f (Field r) (Field r')"
  shows "embed r' r (inv_into (Field r) f)"
proof-
  have "Field r' \<le> f ` (Field r)"
    using BIJ by (auto simp add: bij_betw_def)
  then have iso: "iso  r r' f"
    by (simp add: BIJ EMB iso_def)
  have *: "\<forall>a. a \<in> Field r \<longrightarrow> bij_betw f (under r a) (under r' (f a))"
    using EMB embed_def by fastforce
  show ?thesis 
  proof (clarsimp simp add: embed_def)
    fix a
    assume a: "a \<in> Field r'"
    then have ar: "a \<in> f ` Field r"
      using BIJ bij_betw_imp_surj_on by blast
    have [simp]: "f (inv_into (Field r) f a) = a"
      by (simp add: ar f_inv_into_f)
    show "bij_betw (inv_into (Field r) f) (under r' a) (under r (inv_into (Field r) f a))"
    proof (rule bij_betw_inv_into_subset [OF BIJ])
      show "under r (inv_into (Field r) f a) \<subseteq> Field r"
        by (simp add: under_Field)
      have "inv_into (Field r) f a \<in> Field r"
        by (simp add: ar inv_into_into)
      then show "f ` under r (inv_into (Field r) f a) = under r' a"
        using bij_betw_imp_surj_on * by fastforce
    qed
  qed
qed


subsection \<open>Given any two well-orders, one can be embedded in the other\<close>

text\<open>Here is an overview of the proof of of this fact, stated in theorem
\<open>wellorders_totally_ordered\<close>:

   Fix the well-orders \<open>r::'a rel\<close> and \<open>r'::'a' rel\<close>.
   Attempt to define an embedding \<open>f::'a \<Rightarrow> 'a'\<close> from \<open>r\<close> to \<open>r'\<close> in the
   natural way by well-order recursion ("hoping" that \<open>Field r\<close> turns out to be smaller
   than \<open>Field r'\<close>), but also record, at the recursive step, in a function
   \<open>g::'a \<Rightarrow> bool\<close>, the extra information of whether \<open>Field r'\<close>
   gets exhausted or not.

   If \<open>Field r'\<close> does not get exhausted, then \<open>Field r\<close> is indeed smaller
   and \<open>f\<close> is the desired embedding from \<open>r\<close> to \<open>r'\<close>
   (lemma \<open>wellorders_totally_ordered_aux\<close>).

   Otherwise, it means that \<open>Field r'\<close> is the smaller one, and the inverse of
   (the "good" segment of) \<open>f\<close> is the desired embedding from \<open>r'\<close> to \<open>r\<close>
   (lemma \<open>wellorders_totally_ordered_aux2\<close>).
\<close>

lemma wellorders_totally_ordered_aux:
  fixes r ::"'a rel"  and r'::"'a' rel" and
    f :: "'a \<Rightarrow> 'a'" and a::'a
  assumes WELL: "Well_order r" and WELL': "Well_order r'" and IN: "a \<in> Field r" and
    IH: "\<forall>b \<in> underS r a. bij_betw f (under r b) (under r' (f b))" and
    NOT: "f ` (underS r a) \<noteq> Field r'" and SUC: "f a = wo_rel.suc r' (f`(underS r a))"
  shows "bij_betw f (under r a) (under r' (f a))"
proof-
  (* Preliminary facts *)
  have Well: "wo_rel r" using WELL unfolding wo_rel_def .
  hence Refl: "Refl r" using wo_rel.REFL[of r] by auto
  have Trans: "trans r" using Well wo_rel.TRANS[of r] by auto
  have Well': "wo_rel r'" using WELL' unfolding wo_rel_def .
  have OF: "wo_rel.ofilter r (underS r a)"
    by (auto simp add: Well wo_rel.underS_ofilter)
  hence UN: "underS r a = (\<Union>b \<in> underS r a. under r b)"
    using Well wo_rel.ofilter_under_UNION[of r "underS r a"] by blast
      (* Gather facts about elements of underS r a *)
  {fix b assume *: "b \<in> underS r a"
    hence t0: "(b,a) \<in> r \<and> b \<noteq> a" unfolding underS_def by auto
    have t1: "b \<in> Field r"
      using * underS_Field[of r a] by auto
    have t2: "f`(under r b) = under r' (f b)"
      using IH * by (auto simp add: bij_betw_def)
    hence t3: "wo_rel.ofilter r' (f`(under r b))"
      using Well' by (auto simp add: wo_rel.under_ofilter)
    have "f`(under r b) \<le> Field r'"
      using t2 by (auto simp add: under_Field)
    moreover
    have "b \<in> under r b"
      using t1 by(auto simp add: Refl Refl_under_in)
    ultimately
    have t4:  "f b \<in> Field r'" by auto
    have "f`(under r b) = under r' (f b) \<and>
         wo_rel.ofilter r' (f`(under r b)) \<and>
         f b \<in> Field r'"
      using t2 t3 t4 by auto
  }
  hence bFact:
    "\<forall>b \<in> underS r a. f`(under r b) = under r' (f b) \<and>
                       wo_rel.ofilter r' (f`(under r b)) \<and>
                       f b \<in> Field r'" by blast
    (*  *)
  have subField: "f`(underS r a) \<le> Field r'"
    using bFact by blast
      (*  *)
  have OF': "wo_rel.ofilter r' (f`(underS r a))"
  proof-
    have "f`(underS r a) = f`(\<Union>b \<in> underS r a. under r b)"
      using UN by auto
    also have "\<dots> = (\<Union>b \<in> underS r a. f`(under r b))" by blast
    also have "\<dots> = (\<Union>b \<in> underS r a. (under r' (f b)))"
      using bFact by auto
    finally
    have "f`(underS r a) = (\<Union>b \<in> underS r a. (under r' (f b)))" .
    thus ?thesis
      using Well' bFact
        wo_rel.ofilter_UNION[of r' "underS r a" "\<lambda> b. under r' (f b)"] by fastforce
  qed
    (*  *)
  have "f`(underS r a) \<union> AboveS r' (f`(underS r a)) = Field r'"
    using Well' OF' by (auto simp add: wo_rel.ofilter_AboveS_Field)
  hence NE: "AboveS r' (f`(underS r a)) \<noteq> {}"
    using subField NOT by blast
      (* Main proof *)
  have INCL1: "f`(underS r a) \<le> underS r' (f a) "
  proof(auto)
    fix b assume *: "b \<in> underS r a"
    have "f b \<noteq> f a \<and> (f b, f a) \<in> r'"
      using subField Well' SUC NE *
        wo_rel.suc_greater[of r' "f`(underS r a)" "f b"] by force
    thus "f b \<in> underS r' (f a)"
      unfolding underS_def by simp
  qed
    (*  *)
  have INCL2: "underS r' (f a) \<le> f`(underS r a)"
  proof
    fix b' assume "b' \<in> underS r' (f a)"
    hence "b' \<noteq> f a \<and> (b', f a) \<in> r'"
      unfolding underS_def by simp
    thus "b' \<in> f`(underS r a)"
      using Well' SUC NE OF'
        wo_rel.suc_ofilter_in[of r' "f ` underS r a" b'] by auto
  qed
    (*  *)
  have INJ: "inj_on f (underS r a)"
  proof-
    have "\<forall>b \<in> underS r a. inj_on f (under r b)"
      using IH by (auto simp add: bij_betw_def)
    moreover
    have "\<forall>b. wo_rel.ofilter r (under r b)"
      using Well by (auto simp add: wo_rel.under_ofilter)
    ultimately show  ?thesis
      using WELL bFact UN
        UNION_inj_on_ofilter[of r "underS r a" "\<lambda>b. under r b" f]
      by auto
  qed
    (*  *)
  have BIJ: "bij_betw f (underS r a) (underS r' (f a))"
    unfolding bij_betw_def
    using INJ INCL1 INCL2 by auto
      (*  *)
  have "f a \<in> Field r'"
    using Well' subField NE SUC
    by (auto simp add: wo_rel.suc_inField)
  thus ?thesis
    using WELL WELL' IN BIJ under_underS_bij_betw[of r r' a f] by auto
qed

lemma wellorders_totally_ordered_aux2:
  fixes r ::"'a rel"  and r'::"'a' rel" and
    f :: "'a \<Rightarrow> 'a'" and g :: "'a \<Rightarrow> bool"  and a::'a
  assumes WELL: "Well_order r" and WELL': "Well_order r'" and
    MAIN1:
    "\<And> a. (False \<notin> g`(underS r a) \<and> f`(underS r a) \<noteq> Field r'
          \<longrightarrow> f a = wo_rel.suc r' (f`(underS r a)) \<and> g a = True)
         \<and>
         (\<not>(False \<notin> (g`(underS r a)) \<and> f`(underS r a) \<noteq> Field r')
          \<longrightarrow> g a = False)" and
    MAIN2: "\<And> a. a \<in> Field r \<and> False \<notin> g`(under r a) \<longrightarrow>
              bij_betw f (under r a) (under r' (f a))" and
    Case: "a \<in> Field r \<and> False \<in> g`(under r a)"
  shows "\<exists>f'. embed r' r f'"
proof-
  have Well: "wo_rel r" using WELL unfolding wo_rel_def .
  hence Refl: "Refl r" using wo_rel.REFL[of r] by auto
  have Trans: "trans r" using Well wo_rel.TRANS[of r] by auto
  have Antisym: "antisym r" using Well wo_rel.ANTISYM[of r] by auto
  have Well': "wo_rel r'" using WELL' unfolding wo_rel_def .
      (*  *)
  have 0: "under r a = underS r a \<union> {a}"
    using Refl Case by(auto simp add: Refl_under_underS)
      (*  *)
  have 1: "g a = False"
  proof-
    {assume "g a \<noteq> False"
      with 0 Case have "False \<in> g`(underS r a)" by blast
      with MAIN1 have "g a = False" by blast}
    thus ?thesis by blast
  qed
  let ?A = "{a \<in> Field r. g a = False}"
  let ?a = "(wo_rel.minim r ?A)"
    (*  *)
  have 2: "?A \<noteq> {} \<and> ?A \<le> Field r" using Case 1 by blast
      (*  *)
  have 3: "False \<notin> g`(underS r ?a)"
  proof
    assume "False \<in> g`(underS r ?a)"
    then obtain b where "b \<in> underS r ?a" and 31: "g b = False" by auto
    hence 32: "(b,?a) \<in> r \<and> b \<noteq> ?a"
      by (auto simp add: underS_def)
    hence "b \<in> Field r" unfolding Field_def by auto
    with 31 have "b \<in> ?A" by auto
    hence "(?a,b) \<in> r" using wo_rel.minim_least 2 Well by fastforce
        (* again: why worked without type annotations? *)
    with 32 Antisym show False
      by (auto simp add: antisym_def)
  qed
  have temp: "?a \<in> ?A"
    using Well 2 wo_rel.minim_in[of r ?A] by auto
  hence 4: "?a \<in> Field r" by auto
      (*   *)
  have 5: "g ?a = False" using temp by blast
      (*  *)
  have 6: "f`(underS r ?a) = Field r'"
    using MAIN1[of ?a] 3 5 by blast
      (*  *)
  have 7: "\<forall>b \<in> underS r ?a. bij_betw f (under r b) (under r' (f b))"
  proof
    fix b assume as: "b \<in> underS r ?a"
    moreover
    have "wo_rel.ofilter r (underS r ?a)"
      using Well by (auto simp add: wo_rel.underS_ofilter)
    ultimately
    have "False \<notin> g`(under r b)" using 3 Well by (subst (asm) wo_rel.ofilter_def) fast+
    moreover have "b \<in> Field r"
      unfolding Field_def using as by (auto simp add: underS_def)
    ultimately
    show "bij_betw f (under r b) (under r' (f b))"
      using MAIN2 by auto
  qed
    (*  *)
  have "embed r' r (inv_into (underS r ?a) f)"
    using WELL WELL' 7 4 6 inv_into_underS_embed[of r ?a f r'] by auto
  thus ?thesis
    unfolding embed_def by blast
qed

theorem wellorders_totally_ordered:
  fixes r ::"'a rel"  and r'::"'a' rel"
  assumes WELL: "Well_order r" and WELL': "Well_order r'"
  shows "(\<exists>f. embed r r' f) \<or> (\<exists>f'. embed r' r f')"
proof-
  (* Preliminary facts *)
  have Well: "wo_rel r" using WELL unfolding wo_rel_def .
  hence Refl: "Refl r" using wo_rel.REFL[of r] by auto
  have Trans: "trans r" using Well wo_rel.TRANS[of r] by auto
  have Well': "wo_rel r'" using WELL' unfolding wo_rel_def .
      (* Main proof *)
  obtain H where H_def: "H =
  (\<lambda>h a. if False \<notin> (snd \<circ> h)`(underS r a) \<and> (fst \<circ> h)`(underS r a) \<noteq> Field r'
                then (wo_rel.suc r' ((fst \<circ> h)`(underS r a)), True)
                else (undefined, False))" by blast
  have Adm: "wo_rel.adm_wo r H"
    using Well
  proof(unfold wo_rel.adm_wo_def, clarify)
    fix h1::"'a \<Rightarrow> 'a' * bool" and h2::"'a \<Rightarrow> 'a' * bool" and x
    assume "\<forall>y\<in>underS r x. h1 y = h2 y"
    hence "\<forall>y\<in>underS r x. (fst \<circ> h1) y = (fst \<circ> h2) y \<and>
                          (snd \<circ> h1) y = (snd \<circ> h2) y" by auto
    hence "(fst \<circ> h1)`(underS r x) = (fst \<circ> h2)`(underS r x) \<and>
           (snd \<circ> h1)`(underS r x) = (snd \<circ> h2)`(underS r x)"
      by (auto simp add: image_def)
    thus "H h1 x = H h2 x" by (simp add: H_def del: not_False_in_image_Ball)
  qed
    (* More constant definitions:  *)
  obtain h::"'a \<Rightarrow> 'a' * bool" and f::"'a \<Rightarrow> 'a'" and g::"'a \<Rightarrow> bool"
    where h_def: "h = wo_rel.worec r H" and
      f_def: "f = fst \<circ> h" and g_def: "g = snd \<circ> h" by blast
  obtain test where test_def:
    "test = (\<lambda> a. False \<notin> (g`(underS r a)) \<and> f`(underS r a) \<noteq> Field r')" by blast
      (*  *)
  have *: "\<And> a. h a  = H h a"
    using Adm Well wo_rel.worec_fixpoint[of r H] by (simp add: h_def)
  have Main1:
    "\<And> a. (test a \<longrightarrow> f a = wo_rel.suc r' (f`(underS r a)) \<and> g a = True) \<and>
         (\<not>(test a) \<longrightarrow> g a = False)"
  proof-  (* How can I prove this withou fixing a? *)
    fix a show "(test a \<longrightarrow> f a = wo_rel.suc r' (f`(underS r a)) \<and> g a = True) \<and>
                (\<not>(test a) \<longrightarrow> g a = False)"
      using *[of a] test_def f_def g_def H_def by auto
  qed
    (*  *)
  let ?phi = "\<lambda> a. a \<in> Field r \<and> False \<notin> g`(under r a) \<longrightarrow>
                   bij_betw f (under r a) (under r' (f a))"
  have Main2: "\<And> a. ?phi a"
  proof-
    fix a show "?phi a"
    proof(rule wo_rel.well_order_induct[of r ?phi],
        simp only: Well, clarify)
      fix a
      assume IH: "\<forall>b. b \<noteq> a \<and> (b,a) \<in> r \<longrightarrow> ?phi b" and
        *: "a \<in> Field r" and
        **: "False \<notin> g`(under r a)"
      have 1: "\<forall>b \<in> underS r a. bij_betw f (under r b) (under r' (f b))"
      proof(clarify)
        fix b assume ***: "b \<in> underS r a"
        hence 0: "(b,a) \<in> r \<and> b \<noteq> a" unfolding underS_def by auto
        moreover have "b \<in> Field r"
          using *** underS_Field[of r a] by auto
        moreover have "False \<notin> g`(under r b)"
          using 0 ** Trans under_incr[of r b a] by auto
        ultimately show "bij_betw f (under r b) (under r' (f b))"
          using IH by auto
      qed
        (*  *)
      have 21: "False \<notin> g`(underS r a)"
        using ** underS_subset_under[of r a] by auto
      have 22: "g`(under r a) \<le> {True}" using ** by auto
      moreover have 23: "a \<in> under r a"
        using Refl * by (auto simp add: Refl_under_in)
      ultimately have 24: "g a = True" by blast
      have 2: "f`(underS r a) \<noteq> Field r'"
      proof
        assume "f`(underS r a) = Field r'"
        hence "g a = False" using Main1 test_def by blast
        with 24 show False using ** by blast
      qed
        (*  *)
      have 3: "f a = wo_rel.suc r' (f`(underS r a))"
        using 21 2 Main1 test_def by blast
          (*  *)
      show "bij_betw f (under r a) (under r' (f a))"
        using WELL  WELL' 1 2 3 *
          wellorders_totally_ordered_aux[of r r' a f] by auto
    qed
  qed
    (*  *)
  let ?chi = "(\<lambda> a. a \<in> Field r \<and> False \<in> g`(under r a))"
  show ?thesis
  proof(cases "\<exists>a. ?chi a")
    assume "\<not> (\<exists>a. ?chi a)"
    hence "\<forall>a \<in> Field r.  bij_betw f (under r a) (under r' (f a))"
      using Main2 by blast
    thus ?thesis unfolding embed_def by blast
  next
    assume "\<exists>a. ?chi a"
    then obtain a where "?chi a" by blast
    hence "\<exists>f'. embed r' r f'"
      using wellorders_totally_ordered_aux2[of r r' g f a]
        WELL WELL' Main1 Main2 test_def by fast
    thus ?thesis by blast
  qed
qed


subsection \<open>Uniqueness of embeddings\<close>

text\<open>Here we show a fact complementary to the one from the previous subsection -- namely,
that between any two well-orders there is {\em at most} one embedding, and is the one
definable by the expected well-order recursive equation.  As a consequence, any two
embeddings of opposite directions are mutually inverse.\<close>

lemma embed_determined:
  assumes WELL: "Well_order r" and WELL': "Well_order r'" and
    EMB: "embed r r' f" and IN: "a \<in> Field r"
  shows "f a = wo_rel.suc r' (f`(underS r a))"
proof-
  have "bij_betw f (underS r a) (underS r' (f a))"
    using assms by (auto simp add: embed_underS)
  hence "f`(underS r a) = underS r' (f a)"
    by (auto simp add: bij_betw_def)
  moreover
  {have "f a \<in> Field r'" using IN
      using EMB WELL embed_Field[of r r' f] by auto
    hence "f a = wo_rel.suc r' (underS r' (f a))"
      using WELL' by (auto simp add: wo_rel_def wo_rel.suc_underS)
  }
  ultimately show ?thesis by simp
qed

lemma embed_unique:
  assumes WELL: "Well_order r" and WELL': "Well_order r'" and
    EMBf: "embed r r' f" and EMBg: "embed r r' g"
  shows "a \<in> Field r \<longrightarrow> f a = g a"
proof(rule wo_rel.well_order_induct[of r], auto simp add: WELL wo_rel_def)
  fix a
  assume IH: "\<forall>b. b \<noteq> a \<and> (b,a) \<in> r \<longrightarrow> b \<in> Field r \<longrightarrow> f b = g b" and
    *: "a \<in> Field r"
  hence "\<forall>b \<in> underS r a. f b = g b"
    unfolding underS_def by (auto simp add: Field_def)
  hence "f`(underS r a) = g`(underS r a)" by force
  thus "f a = g a"
    using assms * embed_determined[of r r' f a] embed_determined[of r r' g a] by auto
qed

lemma embed_bothWays_inverse:
  assumes WELL: "Well_order r" and WELL': "Well_order r'" and
    EMB: "embed r r' f" and EMB': "embed r' r f'"
  shows "(\<forall>a \<in> Field r. f'(f a) = a) \<and> (\<forall>a' \<in> Field r'. f(f' a') = a')"
proof-
  have "embed r r (f' \<circ> f)" using assms
    by(auto simp add: comp_embed)
  moreover have "embed r r id" using assms
    by (auto simp add: id_embed)
  ultimately have "\<forall>a \<in> Field r. f'(f a) = a"
    using assms embed_unique[of r r "f' \<circ> f" id] id_def by auto
  moreover
  {have "embed r' r' (f \<circ> f')" using assms
      by(auto simp add: comp_embed)
    moreover have "embed r' r' id" using assms
      by (auto simp add: id_embed)
    ultimately have "\<forall>a' \<in> Field r'. f(f' a') = a'"
      using assms embed_unique[of r' r' "f \<circ> f'" id] id_def by auto
  }
  ultimately show ?thesis by blast
qed

lemma embed_bothWays_bij_betw:
  assumes WELL: "Well_order r" and WELL': "Well_order r'" and
    EMB: "embed r r' f" and EMB': "embed r' r g"
  shows "bij_betw f (Field r) (Field r')"
proof-
  let ?A = "Field r"  let ?A' = "Field r'"
  have "embed r r (g \<circ> f) \<and> embed r' r' (f \<circ> g)"
    using assms by (auto simp add: comp_embed)
  hence 1: "(\<forall>a \<in> ?A. g(f a) = a) \<and> (\<forall>a' \<in> ?A'. f(g a') = a')"
    using WELL id_embed[of r] embed_unique[of r r "g \<circ> f" id]
      WELL' id_embed[of r'] embed_unique[of r' r' "f \<circ> g" id]
      id_def by auto
  have 2: "(\<forall>a \<in> ?A. f a \<in> ?A') \<and> (\<forall>a' \<in> ?A'. g a' \<in> ?A)"
    using assms embed_Field[of r r' f] embed_Field[of r' r g] by blast
      (*  *)
  show ?thesis
  proof(unfold bij_betw_def inj_on_def, auto simp add: 2)
    fix a b assume *: "a \<in> ?A" "b \<in> ?A" and **: "f a = f b"
    have "a = g(f a) \<and> b = g(f b)" using * 1 by auto
    with ** show "a = b" by auto
  next
    fix a' assume *: "a' \<in> ?A'"
    hence "g a' \<in> ?A \<and> f(g a') = a'" using 1 2 by auto
    thus "a' \<in> f ` ?A" by force
  qed
qed

lemma embed_bothWays_iso:
  assumes WELL: "Well_order r"  and WELL': "Well_order r'" and
    EMB: "embed r r' f" and EMB': "embed r' r g"
  shows "iso r r' f"
  unfolding iso_def using assms by (auto simp add: embed_bothWays_bij_betw)


subsection \<open>More properties of embeddings, strict embeddings and isomorphisms\<close>

lemma embed_bothWays_Field_bij_betw:
  assumes WELL: "Well_order r" and WELL': "Well_order r'" and
    EMB: "embed r r' f" and EMB': "embed r' r f'"
  shows "bij_betw f (Field r) (Field r')"
proof-
  have "(\<forall>a \<in> Field r. f'(f a) = a) \<and> (\<forall>a' \<in> Field r'. f(f' a') = a')"
    using assms by (auto simp add: embed_bothWays_inverse)
  moreover
  have "f`(Field r) \<le> Field r' \<and> f' ` (Field r') \<le> Field r"
    using assms by (auto simp add: embed_Field)
  ultimately
  show ?thesis using bij_betw_byWitness[of "Field r" f' f "Field r'"] by auto
qed

lemma embedS_comp_embed:
  assumes WELL: "Well_order r" and WELL': "Well_order r'"
    and  EMB: "embedS r r' f" and EMB': "embed r' r'' f'"
  shows "embedS r r'' (f' \<circ> f)"
proof-
  let ?g = "(f' \<circ> f)"  let ?h = "inv_into (Field r) ?g"
  have 1: "embed r r' f \<and> \<not> (bij_betw f (Field r) (Field r'))"
    using EMB by (auto simp add: embedS_def)
  hence 2: "embed r r'' ?g"
    using  EMB' comp_embed[of r r' f r'' f'] by auto
  moreover
  {assume "bij_betw ?g (Field r) (Field r'')"
    hence "embed r'' r ?h" using 2 
      by (auto simp add: inv_into_Field_embed_bij_betw)
    hence "embed r' r (?h \<circ> f')" using EMB'
      by (auto simp add: comp_embed)
    hence "bij_betw f (Field r) (Field r')" using WELL WELL' 1
      by (auto simp add: embed_bothWays_Field_bij_betw)
    with 1 have False by blast
  }
  ultimately show ?thesis unfolding embedS_def by auto
qed

lemma embed_comp_embedS:
  assumes WELL: "Well_order r" and WELL': "Well_order r'" 
    and  EMB: "embed r r' f" and EMB': "embedS r' r'' f'"
  shows "embedS r r'' (f' \<circ> f)"
proof-
  let ?g = "(f' \<circ> f)"  let ?h = "inv_into (Field r) ?g"
  have 1: "embed r' r'' f' \<and> \<not> (bij_betw f' (Field r') (Field r''))"
    using EMB' by (auto simp add: embedS_def)
  hence 2: "embed r r'' ?g"
    using WELL EMB comp_embed[of r r' f r'' f'] by auto
  moreover have \<section>: "f' ` Field r' \<subseteq> Field r''"
    by (simp add: "1" embed_Field)
  {assume \<section>: "bij_betw ?g (Field r) (Field r'')"
    hence "embed r'' r ?h" using 2 WELL
      by (auto simp add: inv_into_Field_embed_bij_betw)
    hence "embed r' r (inv_into (Field r) ?g \<circ> f')"
      using "1" BNF_Wellorder_Embedding.comp_embed WELL' by blast
    then have "bij_betw f' (Field r') (Field r'')"
      using EMB WELL WELL' \<section> bij_betw_comp_iff by (blast intro: embed_bothWays_Field_bij_betw)
    with 1 have False by blast
  }
  ultimately show ?thesis unfolding embedS_def by auto
qed

lemma embed_comp_iso:
  assumes EMB: "embed r r' f" and EMB': "iso r' r'' f'"
  shows "embed r r'' (f' \<circ> f)" using assms unfolding iso_def
  by (auto simp add: comp_embed)

lemma iso_comp_embed:
  assumes EMB: "iso r r' f" and EMB': "embed r' r'' f'"
  shows "embed r r'' (f' \<circ> f)"
  using assms unfolding iso_def by (auto simp add: comp_embed)

lemma embedS_comp_iso:
  assumes EMB: "embedS r r' f" and EMB': "iso r' r'' f'"
  shows "embedS r r'' (f' \<circ> f)"
proof -
  have \<section>: "embed r r' f \<and> \<not> bij_betw f (Field r) (Field r')"
    using EMB embedS_def by blast
  then have "embed r r'' (f' \<circ> f)"
    using embed_comp_iso EMB' by blast
  then have "f ` Field r \<subseteq> Field r'"
    by (simp add: embed_Field \<section>)
  then have "\<not> bij_betw (f' \<circ> f) (Field r) (Field r'')"
    using "\<section>" EMB' by (auto simp: bij_betw_comp_iff2 iso_def)
  then show ?thesis
    by (simp add: \<open>embed r r'' (f' \<circ> f)\<close> embedS_def)
qed

lemma iso_comp_embedS:
  assumes WELL: "Well_order r" and WELL': "Well_order r'"
    and  EMB: "iso r r' f" and EMB': "embedS r' r'' f'"
  shows "embedS r r'' (f' \<circ> f)"
  using assms unfolding iso_def by (auto simp add: embed_comp_embedS)

lemma embedS_Field:
  assumes WELL: "Well_order r" and EMB: "embedS r r' f"
  shows "f ` (Field r) < Field r'"
proof-
  have "f`(Field r) \<le> Field r'" using assms
    by (auto simp add: embed_Field embedS_def)
  moreover
  {have "inj_on f (Field r)" using assms
      by (auto simp add: embedS_def embed_inj_on)
    hence "f`(Field r) \<noteq> Field r'" using EMB
      by (auto simp add: embedS_def bij_betw_def)
  }
  ultimately show ?thesis by blast
qed

lemma embedS_iff:
  assumes WELL: "Well_order r" and ISO: "embed r r' f"
  shows "embedS r r' f = (f ` (Field r) < Field r')"
proof
  assume "embedS r r' f"
  thus "f ` Field r \<subset> Field r'"
    using WELL by (auto simp add: embedS_Field)
next
  assume "f ` Field r \<subset> Field r'"
  hence "\<not> bij_betw f (Field r) (Field r')"
    unfolding bij_betw_def by blast
  thus "embedS r r' f" unfolding embedS_def
    using ISO by auto
qed

lemma iso_Field: "iso r r' f \<Longrightarrow> f ` (Field r) = Field r'"
  by (auto simp add: iso_def bij_betw_def)

lemma iso_iff:
  assumes "Well_order r"
  shows "iso r r' f = (embed r r' f \<and> f ` (Field r) = Field r')"
proof
  assume "iso r r' f"
  thus "embed r r' f \<and> f ` (Field r) = Field r'"
    by (auto simp add: iso_Field iso_def)
next
  assume *: "embed r r' f \<and> f ` Field r = Field r'"
  hence "inj_on f (Field r)" using assms by (auto simp add: embed_inj_on)
  with * have "bij_betw f (Field r) (Field r')"
    unfolding bij_betw_def by simp
  with * show "iso r r' f" unfolding iso_def by auto
qed

lemma iso_iff2: "iso r r' f \<longleftrightarrow>
                 bij_betw f (Field r) (Field r') \<and> 
                 (\<forall>a \<in> Field r. \<forall>b \<in> Field r. (a, b) \<in> r \<longleftrightarrow> (f a, f b) \<in> r')"
  (is "?lhs = ?rhs")
proof
  assume L: ?lhs
  then have "bij_betw f (Field r) (Field r')" and emb: "embed r r' f"
    by (auto simp: bij_betw_def iso_def)
  then obtain g where g: "\<And>x. x \<in> Field r \<Longrightarrow> g (f x) = x"
    by (auto simp: bij_betw_iff_bijections)
  moreover
  have "(a, b) \<in> r" if "a \<in> Field r" "b \<in> Field r" "(f a, f b) \<in> r'" for a b 
    using that emb g g [OF FieldI1] \<comment>\<open>yes it's weird\<close>
    by (force simp add: embed_def under_def bij_betw_iff_bijections)
  ultimately show ?rhs
    using L by (auto simp: compat_def iso_def dest: embed_compat)
next
  assume R: ?rhs
  then show ?lhs
    apply (clarsimp simp add: iso_def embed_def under_def bij_betw_iff_bijections)
    apply (rule_tac x="g" in exI)
    apply (fastforce simp add: intro: FieldI1)+
    done
qed

lemma iso_iff3:
  assumes WELL: "Well_order r" and WELL': "Well_order r'"
  shows "iso r r' f = (bij_betw f (Field r) (Field r') \<and> compat r r' f)"
proof
  assume "iso r r' f"
  thus "bij_betw f (Field r) (Field r') \<and> compat r r' f"
    unfolding compat_def using WELL by (auto simp add: iso_iff2 Field_def)
next
  have Well: "wo_rel r \<and> wo_rel r'" using WELL WELL'
    by (auto simp add: wo_rel_def)
  assume *: "bij_betw f (Field r) (Field r') \<and> compat r r' f"
  thus "iso r r' f"
    unfolding "compat_def" using assms
  proof(auto simp add: iso_iff2)
    fix a b assume **: "a \<in> Field r" "b \<in> Field r" and
      ***: "(f a, f b) \<in> r'"
    {assume "(b,a) \<in> r \<or> b = a"
      hence "(b,a) \<in> r"using Well ** wo_rel.REFL[of r] refl_on_def[of _ r] by blast
      hence "(f b, f a) \<in> r'" using * unfolding compat_def by auto
      hence "f a = f b"
        using Well *** wo_rel.ANTISYM[of r'] antisym_def[of r'] by blast
      hence "a = b" using * ** unfolding bij_betw_def inj_on_def by auto
      hence "(a,b) \<in> r" using Well ** wo_rel.REFL[of r] refl_on_def[of _ r] by blast
    }
    thus "(a,b) \<in> r"
      using Well ** wo_rel.TOTAL[of r] total_on_def[of _ r] by blast
  qed
qed

lemma iso_imp_inj_on:
  assumes "iso r r' f" shows "inj_on f (Field r)" 
  using assms unfolding iso_iff2 bij_betw_def by blast

lemma iso_backward_Field:
  assumes "x \<in> Field r'" "iso r r' f" 
  shows "inv_into (Field r) f x \<in> Field r"
  using assms iso_Field by (blast intro!: inv_into_into)

lemma iso_backward:
  assumes "(x,y) \<in> r'" and iso: "iso r r' f" 
  shows "(inv_into (Field r) f x, inv_into (Field r) f y) \<in> r"
proof -
  have \<section>: "\<And>x. (\<exists>xa\<in>Field r. x = f xa) = (x \<in> Field r')"
    using assms iso_Field [OF iso] by (force simp add: )
  have "x \<in> Field r'" "y \<in> Field r'" 
    using assms by (auto simp: Field_def)
  with \<section> [of x] \<section> [of y] assms show ?thesis
    by (auto simp add: iso_iff2 bij_betw_inv_into_left)
qed

lemma iso_forward:
  assumes "(x,y) \<in> r" "iso r r' f" shows "(f x,f y) \<in> r'" 
  using assms by (auto simp: Field_def iso_iff2)

lemma iso_trans:
  assumes "trans r" and iso: "iso r r' f" shows "trans r'"
  unfolding trans_def
proof clarify
  fix x y z
  assume xyz: "(x, y) \<in> r'" "(y, z) \<in> r'"
  then have *: "(inv_into (Field r) f x, inv_into (Field r) f y) \<in> r" 
    "(inv_into (Field r) f y, inv_into (Field r) f z) \<in> r" 
    using iso_backward [OF _ iso] by blast+
  then have "inv_into (Field r) f x \<in> Field r" "inv_into (Field r) f y \<in> Field r"
    by (auto simp: Field_def)
  with * have "(inv_into (Field r) f x, inv_into (Field r) f z) \<in> r"
    using assms(1) by (blast intro: transD)
  then have "(f (inv_into (Field r) f x), f (inv_into (Field r) f z)) \<in> r'"
    by (blast intro: iso iso_forward)
  moreover have "x \<in> f ` Field r" "z \<in> f ` Field r"
    using xyz iso iso_Field by (blast intro: FieldI1 FieldI2)+
  ultimately show "(x, z) \<in> r'"
    by (simp add: f_inv_into_f) 
qed

lemma iso_Total:
  assumes "Total r" and iso: "iso r r' f" shows "Total r'"
  unfolding total_on_def
proof clarify
  fix x y
  assume xy: "x \<in> Field r'" "y \<in> Field r'" "x \<noteq> y" "(y,x) \<notin> r'"
  then have \<section>: "inv_into (Field r) f x \<in> Field r" "inv_into (Field r) f y \<in> Field r"
    using iso_backward_Field [OF _ iso] by auto
  moreover have "x \<in> f ` Field r" "y \<in> f ` Field r"
    using xy iso iso_Field by (blast intro: FieldI1 FieldI2)+
  ultimately have False if "inv_into (Field r) f x = inv_into (Field r) f y"
    using inv_into_injective [OF that] \<open>x \<noteq> y\<close> by simp
  then have "(inv_into (Field r) f x, inv_into (Field r) f y) \<in> r \<or> (inv_into (Field r) f y, inv_into (Field r) f x) \<in> r"
    using assms \<section> by (auto simp: total_on_def)
  then show "(x, y) \<in> r'"
    using assms xy by (auto simp: iso_Field f_inv_into_f dest!: iso_forward [OF _ iso])
qed

lemma iso_wf:
  assumes "wf r" and iso: "iso r r' f" shows "wf r'"
proof -
  have "bij_betw f (Field r) (Field r')"
    and iff: "(\<forall>a \<in> Field r. \<forall>b \<in> Field r. (a, b) \<in> r \<longleftrightarrow> (f a, f b) \<in> r')"
    using assms by (auto simp: iso_iff2)
  show ?thesis
  proof (rule wfI_min)
    fix x::'b and Q
    assume "x \<in> Q"
    let ?g = "inv_into (Field r) f"
    obtain z0 where "z0 \<in> ?g ` Q"
      using \<open>x \<in> Q\<close> by blast 
    then obtain z where z: "z \<in> ?g ` Q" and "\<And>x y. \<lbrakk>(y, z) \<in> r; x \<in> Q\<rbrakk> \<Longrightarrow> y \<noteq> ?g x"
      by (rule wfE_min [OF \<open>wf r\<close>]) auto
    then have "\<forall>y. (y, inv_into Q ?g z) \<in> r' \<longrightarrow> y \<notin> Q"
      by (clarsimp simp: f_inv_into_f[OF z] z dest!: iso_backward [OF _ iso]) blast
    moreover have "inv_into Q ?g z \<in> Q"
      by (simp add: inv_into_into z)
    ultimately show "\<exists>z\<in>Q. \<forall>y. (y, z) \<in> r' \<longrightarrow> y \<notin> Q" ..
  qed
qed

end
