(*  Title:      HOL/Ordinals_and_Cardinals/Wellorder_Embedding_Base.thy
    Author:     Andrei Popescu, TU Muenchen
    Copyright   2012

Well-order embeddings (base).
*)

header {* Well-Order Embeddings (Base) *}

theory Wellorder_Embedding_Base
imports "~~/src/HOL/Library/Zorn" Fun_More_Base Wellorder_Relation_Base
begin


text{* In this section, we introduce well-order {\em embeddings} and {\em isomorphisms} and
prove their basic properties.  The notion of embedding is considered from the point
of view of the theory of ordinals, and therefore requires the source to be injected
as an {\em initial segment} (i.e., {\em order filter}) of the target.  A main result
of this section is the existence of embeddings (in one direction or another) between
any two well-orders, having as a consequence the fact that, given any two sets on
any two types, one is smaller than (i.e., can be injected into) the other. *}


subsection {* Auxiliaries *}

lemma UNION_inj_on_ofilter:
assumes WELL: "Well_order r" and
        OF: "\<And> i. i \<in> I \<Longrightarrow> wo_rel.ofilter r (A i)" and
       INJ: "\<And> i. i \<in> I \<Longrightarrow> inj_on f (A i)"
shows "inj_on f (\<Union> i \<in> I. A i)"
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
        BIJ: "bij_betw f (rel.underS r a) (rel.underS r' (f a))"
shows "bij_betw f (rel.under r a) (rel.under r' (f a))"
proof-
  have "a \<notin> rel.underS r a \<and> f a \<notin> rel.underS r' (f a)"
  unfolding rel.underS_def by auto
  moreover
  {have "Refl r \<and> Refl r'" using WELL WELL'
   by (auto simp add: order_on_defs)
   hence "rel.under r a = rel.underS r a \<union> {a} \<and>
          rel.under r' (f a) = rel.underS r' (f a) \<union> {f a}"
   using IN IN' by(auto simp add: rel.Refl_under_underS)
  }
  ultimately show ?thesis
  using BIJ notIn_Un_bij_betw[of a "rel.underS r a" f "rel.underS r' (f a)"] by auto
qed



subsection {* (Well-order) embeddings, strict embeddings, isomorphisms and order-compatible
functions  *}


text{* Standardly, a function is an embedding of a well-order in another if it injectively and
order-compatibly maps the former into an order filter of the latter.
Here we opt for a more succinct definition (operator @{text "embed"}),
asking that, for any element in the source, the function should be a bijection
between the set of strict lower bounds of that element
and the set of strict lower bounds of its image.  (Later we prove equivalence with
the standard definition -- lemma @{text "embed_iff_compat_inj_on_ofilter"}.)
A {\em strict embedding} (operator @{text "embedS"})  is a non-bijective embedding
and an isomorphism (operator @{text "iso"}) is a bijective embedding.   *}


definition embed :: "'a rel \<Rightarrow> 'a' rel \<Rightarrow> ('a \<Rightarrow> 'a') \<Rightarrow> bool"
where
"embed r r' f \<equiv> \<forall>a \<in> Field r. bij_betw f (rel.under r a) (rel.under r' (f a))"


lemmas embed_defs = embed_def embed_def[abs_def]


text {* Strict embeddings: *}

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


lemma embed_in_Field:
assumes WELL: "Well_order r" and
        EMB: "embed r r' f" and IN: "a \<in> Field r"
shows "f a \<in> Field r'"
proof-
  have Well: "wo_rel r"
  using WELL by (auto simp add: wo_rel_def)
  hence 1: "Refl r"
  by (auto simp add: wo_rel.REFL)
  hence "a \<in> rel.under r a" using IN rel.Refl_under_in by fastforce
  hence "f a \<in> rel.under r' (f a)"
  using EMB IN by (auto simp add: embed_def bij_betw_def)
  thus ?thesis unfolding Field_def
  by (auto simp: rel.under_def)
qed


lemma comp_embed:
assumes WELL: "Well_order r" and
        EMB: "embed r r' f" and EMB': "embed r' r'' f'"
shows "embed r r'' (f' o f)"
proof(unfold embed_def, auto)
  fix a assume *: "a \<in> Field r"
  hence "bij_betw f (rel.under r a) (rel.under r' (f a))"
  using embed_def[of r] EMB by auto
  moreover
  {have "f a \<in> Field r'"
   using EMB WELL * by (auto simp add: embed_in_Field)
   hence "bij_betw f' (rel.under r' (f a)) (rel.under r'' (f' (f a)))"
   using embed_def[of r'] EMB' by auto
  }
  ultimately
  show "bij_betw (f' \<circ> f) (rel.under r a) (rel.under r'' (f'(f a)))"
  by(auto simp add: bij_betw_trans)
qed


lemma comp_iso:
assumes WELL: "Well_order r" and
        EMB: "iso r r' f" and EMB': "iso r' r'' f'"
shows "iso r r'' (f' o f)"
using assms unfolding iso_def
by (auto simp add: comp_embed bij_betw_trans)


text{* That @{text "embedS"} is also preserved by function composition shall be proved only later.  *}


lemma embed_Field:
"\<lbrakk>Well_order r; embed r r' f\<rbrakk> \<Longrightarrow> f`(Field r) \<le> Field r'"
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
    assume *: "a \<in> A" and **: "b' \<in> rel.under r' (f a)"
    hence "a \<in> Field r" using 0 by auto
    hence "bij_betw f (rel.under r a) (rel.under r' (f a))"
    using * EMB by (auto simp add: embed_def)
    hence "f`(rel.under r a) = rel.under r' (f a)"
    by (simp add: bij_betw_def)
    with ** image_def[of f "rel.under r a"] obtain b where
    1: "b \<in> rel.under r a \<and> b' = f b" by blast
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


lemma embed_compat:
assumes EMB: "embed r r' f"
shows "compat r r' f"
proof(unfold compat_def, clarify)
  fix a b
  assume *: "(a,b) \<in> r"
  hence 1: "b \<in> Field r" using Field_def[of r] by blast
  have "a \<in> rel.under r b"
  using * rel.under_def[of r] by simp
  hence "f a \<in> rel.under r' (f b)"
  using EMB embed_def[of r r' f]
        bij_betw_def[of f "rel.under r b" "rel.under r' (f b)"]
        image_def[of f "rel.under r b"] 1 by auto
  thus "(f a, f b) \<in> r'"
  by (auto simp add: rel.under_def)
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
   hence "a \<in> rel.under r b \<and> b \<in> rel.under r b"
   using Refl by(auto simp add: rel.under_def refl_on_def)
   hence "a = b"
   using EMB 1 ***
   by (auto simp add: embed_def bij_betw_def inj_on_def)
  }
  moreover
  {assume "(b,a) \<in> r"
   hence "a \<in> rel.under r a \<and> b \<in> rel.under r a"
   using Refl by(auto simp add: rel.under_def refl_on_def)
   hence "a = b"
   using EMB 1 ***
   by (auto simp add: embed_def bij_betw_def inj_on_def)
  }
  ultimately
  show "a = b" using Total 1
  by (auto simp add: total_on_def)
qed


lemma embed_underS:
assumes WELL: "Well_order r" and WELL: "Well_order r'" and
        EMB: "embed r r' f" and IN: "a \<in> Field r"
shows "bij_betw f (rel.underS r a) (rel.underS r' (f a))"
proof-
  have "bij_betw f (rel.under r a) (rel.under r' (f a))"
  using assms by (auto simp add: embed_def)
  moreover
  {have "f a \<in> Field r'" using assms  embed_Field[of r r' f] by auto
   hence "rel.under r a = rel.underS r a \<union> {a} \<and>
          rel.under r' (f a) = rel.underS r' (f a) \<union> {f a}"
   using assms by (auto simp add: order_on_defs rel.Refl_under_underS)
  }
  moreover
  {have "a \<notin> rel.underS r a \<and> f a \<notin> rel.underS r' (f a)"
   unfolding rel.underS_def by blast
  }
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
  hence 2: "rel.under r' (f a) \<le> f`(Field r)"
  using Well' *** wo_rel.ofilter_def[of r' "f`(Field r)"] by fastforce
  (* Main proof *)
  show "bij_betw f (rel.under r a) (rel.under r' (f a))"
  proof(unfold bij_betw_def, auto)
    show  "inj_on f (rel.under r a)"
    using *
    by (auto simp add: rel.under_Field subset_inj_on)
  next
    fix b assume "b \<in> rel.under r a"
    thus "f b \<in> rel.under r' (f a)"
    unfolding rel.under_def using **
    by (auto simp add: compat_def)
  next
    fix b' assume *****: "b' \<in> rel.under r' (f a)"
    hence "b' \<in> f`(Field r)"
    using 2 by auto
    with Field_def[of r] obtain b where
    3: "b \<in> Field r" and 4: "b' = f b" by auto
    have "(b,a): r"
    proof-
      {assume "(a,b) \<in> r"
       with ** 4 have "(f a, b'): r'"
       by (auto simp add: compat_def)
       with ***** Antisym' have "f a = b'"
       by(auto simp add: rel.under_def antisym_def)
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
    with 4 show  "b' \<in> f`(rel.under r a)"
    unfolding rel.under_def by auto
  qed
qed


lemma inv_into_ofilter_embed:
assumes WELL: "Well_order r" and OF: "wo_rel.ofilter r A" and
        BIJ: "\<forall>b \<in> A. bij_betw f (rel.under r b) (rel.under r' (f b))" and
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
     hence "b1 \<in> rel.under r b2 \<and> b2 \<in> rel.under r b2"
     unfolding rel.under_def using 11 Refl
     by (auto simp add: refl_on_def)
     hence "b1 = b2" using BIJ * ** ***
     by (auto simp add: bij_betw_def inj_on_def)
    }
    moreover
     {assume "(b2,b1) \<in> r"
     hence "b1 \<in> rel.under r b1 \<and> b2 \<in> rel.under r b1"
     unfolding rel.under_def using 11 Refl
     by (auto simp add: refl_on_def)
     hence "b1 = b2" using BIJ * ** ***
     by (auto simp add: bij_betw_def inj_on_def)
    }
    ultimately
    show "b1 = b2"
    using Total by (auto simp add: total_on_def)
  qed
  (*  *)
  let ?f' = "(inv_into A f)"
  (*  *)
  have 2: "\<forall>b \<in> A. bij_betw ?f' (rel.under r' (f b)) (rel.under r b)"
  proof(clarify)
    fix b assume *: "b \<in> A"
    hence "rel.under r b \<le> A"
    using Well OF by(auto simp add: wo_rel.ofilter_def)
    moreover
    have "f ` (rel.under r b) = rel.under r' (f b)"
    using * BIJ by (auto simp add: bij_betw_def)
    ultimately
    show "bij_betw ?f' (rel.under r' (f b)) (rel.under r b)"
    using 1 by (auto simp add: bij_betw_inv_into_subset)
  qed
  (*  *)
  have 3: "\<forall>b' \<in> Field r'. bij_betw ?f' (rel.under r' b') (rel.under r (?f' b'))"
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
    show  "bij_betw ?f' (rel.under r' b') (rel.under r (?f' b'))"
    using 2 by auto
  qed
  (*  *)
  thus ?thesis unfolding embed_def .
qed


lemma inv_into_underS_embed:
assumes WELL: "Well_order r" and
        BIJ: "\<forall>b \<in> rel.underS r a. bij_betw f (rel.under r b) (rel.under r' (f b))" and
        IN: "a \<in> Field r" and
        IMAGE: "f ` (rel.underS r a) = Field r'"
shows "embed r' r (inv_into (rel.underS r a) f)"
using assms
by(auto simp add: wo_rel_def wo_rel.underS_ofilter inv_into_ofilter_embed)


lemma inv_into_Field_embed:
assumes WELL: "Well_order r" and EMB: "embed r r' f" and
        IMAGE: "Field r' \<le> f ` (Field r)"
shows "embed r' r (inv_into (Field r) f)"
proof-
  have "(\<forall>b \<in> Field r. bij_betw f (rel.under r b) (rel.under r' (f b)))"
  using EMB by (auto simp add: embed_def)
  moreover
  have "f ` (Field r) \<le> Field r'"
  using EMB WELL by (auto simp add: embed_Field)
  ultimately
  show ?thesis using assms
  by(auto simp add: wo_rel_def wo_rel.Field_ofilter inv_into_ofilter_embed)
qed


lemma inv_into_Field_embed_bij_betw:
assumes WELL: "Well_order r" and
        EMB: "embed r r' f" and BIJ: "bij_betw f (Field r) (Field r')"
shows "embed r' r (inv_into (Field r) f)"
proof-
  have "Field r' \<le> f ` (Field r)"
  using BIJ by (auto simp add: bij_betw_def)
  thus ?thesis using assms
  by(auto simp add: inv_into_Field_embed)
qed





subsection {* Given any two well-orders, one can be embedded in the other *}


text{* Here is an overview of the proof of of this fact, stated in theorem
@{text "wellorders_totally_ordered"}:

   Fix the well-orders @{text "r::'a rel"} and @{text "r'::'a' rel"}.
   Attempt to define an embedding @{text "f::'a \<Rightarrow> 'a'"} from @{text "r"} to @{text "r'"} in the
   natural way by well-order recursion ("hoping" that @{text "Field r"} turns out to be smaller
   than @{text "Field r'"}), but also record, at the recursive step, in a function
   @{text "g::'a \<Rightarrow> bool"}, the extra information of whether @{text "Field r'"}
   gets exhausted or not.

   If @{text "Field r'"} does not get exhausted, then @{text "Field r"} is indeed smaller
   and @{text "f"} is the desired embedding from @{text "r"} to @{text "r'"}
   (lemma @{text "wellorders_totally_ordered_aux"}).

   Otherwise, it means that @{text "Field r'"} is the smaller one, and the inverse of
   (the "good" segment of) @{text "f"} is the desired embedding from @{text "r'"} to @{text "r"}
   (lemma @{text "wellorders_totally_ordered_aux2"}).
*}


lemma wellorders_totally_ordered_aux:
fixes r ::"'a rel"  and r'::"'a' rel" and
      f :: "'a \<Rightarrow> 'a'" and a::'a
assumes WELL: "Well_order r" and WELL': "Well_order r'" and IN: "a \<in> Field r" and
        IH: "\<forall>b \<in> rel.underS r a. bij_betw f (rel.under r b) (rel.under r' (f b))" and
        NOT: "f ` (rel.underS r a) \<noteq> Field r'" and SUC: "f a = wo_rel.suc r' (f`(rel.underS r a))"
shows "bij_betw f (rel.under r a) (rel.under r' (f a))"
proof-
  (* Preliminary facts *)
  have Well: "wo_rel r" using WELL unfolding wo_rel_def .
  hence Refl: "Refl r" using wo_rel.REFL[of r] by auto
  have Trans: "trans r" using Well wo_rel.TRANS[of r] by auto
  have Well': "wo_rel r'" using WELL' unfolding wo_rel_def .
  have OF: "wo_rel.ofilter r (rel.underS r a)"
  by (auto simp add: Well wo_rel.underS_ofilter)
  hence UN: "rel.underS r a = (\<Union>  b \<in> rel.underS r a. rel.under r b)"
  using Well wo_rel.ofilter_under_UNION[of r "rel.underS r a"] by blast
  (* Gather facts about elements of rel.underS r a *)
  {fix b assume *: "b \<in> rel.underS r a"
   hence t0: "(b,a) \<in> r \<and> b \<noteq> a" unfolding rel.underS_def by auto
   have t1: "b \<in> Field r"
   using * rel.underS_Field[of r a] by auto
   have t2: "f`(rel.under r b) = rel.under r' (f b)"
   using IH * by (auto simp add: bij_betw_def)
   hence t3: "wo_rel.ofilter r' (f`(rel.under r b))"
   using Well' by (auto simp add: wo_rel.under_ofilter)
   have "f`(rel.under r b) \<le> Field r'"
   using t2 by (auto simp add: rel.under_Field)
   moreover
   have "b \<in> rel.under r b"
   using t1 by(auto simp add: Refl rel.Refl_under_in)
   ultimately
   have t4:  "f b \<in> Field r'" by auto
   have "f`(rel.under r b) = rel.under r' (f b) \<and>
         wo_rel.ofilter r' (f`(rel.under r b)) \<and>
         f b \<in> Field r'"
   using t2 t3 t4 by auto
  }
  hence bFact:
  "\<forall>b \<in> rel.underS r a. f`(rel.under r b) = rel.under r' (f b) \<and>
                       wo_rel.ofilter r' (f`(rel.under r b)) \<and>
                       f b \<in> Field r'" by blast
  (*  *)
  have subField: "f`(rel.underS r a) \<le> Field r'"
  using bFact by blast
  (*  *)
  have OF': "wo_rel.ofilter r' (f`(rel.underS r a))"
  proof-
    have "f`(rel.underS r a) = f`(\<Union>  b \<in> rel.underS r a. rel.under r b)"
    using UN by auto
    also have "\<dots> = (\<Union>  b \<in> rel.underS r a. f`(rel.under r b))" by blast
    also have "\<dots> = (\<Union>  b \<in> rel.underS r a. (rel.under r' (f b)))"
    using bFact by auto
    finally
    have "f`(rel.underS r a) = (\<Union>  b \<in> rel.underS r a. (rel.under r' (f b)))" .
    thus ?thesis
    using Well' bFact
          wo_rel.ofilter_UNION[of r' "rel.underS r a" "\<lambda> b. rel.under r' (f b)"] by fastforce
  qed
  (*  *)
  have "f`(rel.underS r a) \<union> rel.AboveS r' (f`(rel.underS r a)) = Field r'"
  using Well' OF' by (auto simp add: wo_rel.ofilter_AboveS_Field)
  hence NE: "rel.AboveS r' (f`(rel.underS r a)) \<noteq> {}"
  using subField NOT by blast
  (* Main proof *)
  have INCL1: "f`(rel.underS r a) \<le> rel.underS r' (f a) "
  proof(auto)
    fix b assume *: "b \<in> rel.underS r a"
    have "f b \<noteq> f a \<and> (f b, f a) \<in> r'"
    using subField Well' SUC NE *
          wo_rel.suc_greater[of r' "f`(rel.underS r a)" "f b"] by auto
    thus "f b \<in> rel.underS r' (f a)"
    unfolding rel.underS_def by simp
  qed
  (*  *)
  have INCL2: "rel.underS r' (f a) \<le> f`(rel.underS r a)"
  proof
    fix b' assume "b' \<in> rel.underS r' (f a)"
    hence "b' \<noteq> f a \<and> (b', f a) \<in> r'"
    unfolding rel.underS_def by simp
    thus "b' \<in> f`(rel.underS r a)"
    using Well' SUC NE OF'
          wo_rel.suc_ofilter_in[of r' "f ` rel.underS r a" b'] by auto
  qed
  (*  *)
  have INJ: "inj_on f (rel.underS r a)"
  proof-
    have "\<forall>b \<in> rel.underS r a. inj_on f (rel.under r b)"
    using IH by (auto simp add: bij_betw_def)
    moreover
    have "\<forall>b. wo_rel.ofilter r (rel.under r b)"
    using Well by (auto simp add: wo_rel.under_ofilter)
    ultimately show  ?thesis
    using WELL bFact UN
          UNION_inj_on_ofilter[of r "rel.underS r a" "\<lambda>b. rel.under r b" f]
    by auto
  qed
  (*  *)
  have BIJ: "bij_betw f (rel.underS r a) (rel.underS r' (f a))"
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
  "\<And> a. (False \<notin> g`(rel.underS r a) \<and> f`(rel.underS r a) \<noteq> Field r'
          \<longrightarrow> f a = wo_rel.suc r' (f`(rel.underS r a)) \<and> g a = True)
         \<and>
         (\<not>(False \<notin> (g`(rel.underS r a)) \<and> f`(rel.underS r a) \<noteq> Field r')
          \<longrightarrow> g a = False)" and
MAIN2: "\<And> a. a \<in> Field r \<and> False \<notin> g`(rel.under r a) \<longrightarrow>
              bij_betw f (rel.under r a) (rel.under r' (f a))" and
Case: "a \<in> Field r \<and> False \<in> g`(rel.under r a)"
shows "\<exists>f'. embed r' r f'"
proof-
  have Well: "wo_rel r" using WELL unfolding wo_rel_def .
  hence Refl: "Refl r" using wo_rel.REFL[of r] by auto
  have Trans: "trans r" using Well wo_rel.TRANS[of r] by auto
  have Antisym: "antisym r" using Well wo_rel.ANTISYM[of r] by auto
  have Well': "wo_rel r'" using WELL' unfolding wo_rel_def .
  (*  *)
  have 0: "rel.under r a = rel.underS r a \<union> {a}"
  using Refl Case by(auto simp add: rel.Refl_under_underS)
  (*  *)
  have 1: "g a = False"
  proof-
    {assume "g a \<noteq> False"
     with 0 Case have "False \<in> g`(rel.underS r a)" by blast
     with MAIN1 have "g a = False" by blast}
    thus ?thesis by blast
  qed
  let ?A = "{a \<in> Field r. g a = False}"
  let ?a = "(wo_rel.minim r ?A)"
  (*  *)
  have 2: "?A \<noteq> {} \<and> ?A \<le> Field r" using Case 1 by blast
  (*  *)
  have 3: "False \<notin> g`(rel.underS r ?a)"
  proof
    assume "False \<in> g`(rel.underS r ?a)"
    then obtain b where "b \<in> rel.underS r ?a" and 31: "g b = False" by auto
    hence 32: "(b,?a) \<in> r \<and> b \<noteq> ?a"
    by (auto simp add: rel.underS_def)
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
  have 6: "f`(rel.underS r ?a) = Field r'"
  using MAIN1[of ?a] 3 5 by blast
  (*  *)
  have 7: "\<forall>b \<in> rel.underS r ?a. bij_betw f (rel.under r b) (rel.under r' (f b))"
  proof
    fix b assume as: "b \<in> rel.underS r ?a"
    moreover
    have "wo_rel.ofilter r (rel.underS r ?a)"
    using Well by (auto simp add: wo_rel.underS_ofilter)
    ultimately
    have "False \<notin> g`(rel.under r b)" using 3 Well by (auto simp add: wo_rel.ofilter_def)
    moreover have "b \<in> Field r"
    unfolding Field_def using as by (auto simp add: rel.underS_def)
    ultimately
    show "bij_betw f (rel.under r b) (rel.under r' (f b))"
    using MAIN2 by auto
  qed
  (*  *)
  have "embed r' r (inv_into (rel.underS r ?a) f)"
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
  (\<lambda>h a. if False \<notin> (snd o h)`(rel.underS r a) \<and> (fst o h)`(rel.underS r a) \<noteq> Field r'
                then (wo_rel.suc r' ((fst o h)`(rel.underS r a)), True)
                else (undefined, False))" by blast
  have Adm: "wo_rel.adm_wo r H"
  using Well
  proof(unfold wo_rel.adm_wo_def, clarify)
    fix h1::"'a \<Rightarrow> 'a' * bool" and h2::"'a \<Rightarrow> 'a' * bool" and x
    assume "\<forall>y\<in>rel.underS r x. h1 y = h2 y"
    hence "\<forall>y\<in>rel.underS r x. (fst o h1) y = (fst o h2) y \<and>
                          (snd o h1) y = (snd o h2) y" by auto
    hence "(fst o h1)`(rel.underS r x) = (fst o h2)`(rel.underS r x) \<and>
           (snd o h1)`(rel.underS r x) = (snd o h2)`(rel.underS r x)"
    by (auto simp add: image_def)
    thus "H h1 x = H h2 x" by (simp add: H_def)
  qed
  (* More constant definitions:  *)
  obtain h::"'a \<Rightarrow> 'a' * bool" and f::"'a \<Rightarrow> 'a'" and g::"'a \<Rightarrow> bool"
  where h_def: "h = wo_rel.worec r H" and
        f_def: "f = fst o h" and g_def: "g = snd o h" by blast
  obtain test where test_def:
  "test = (\<lambda> a. False \<notin> (g`(rel.underS r a)) \<and> f`(rel.underS r a) \<noteq> Field r')" by blast
  (*  *)
  have *: "\<And> a. h a  = H h a"
  using Adm Well wo_rel.worec_fixpoint[of r H] by (simp add: h_def)
  have Main1:
  "\<And> a. (test a \<longrightarrow> f a = wo_rel.suc r' (f`(rel.underS r a)) \<and> g a = True) \<and>
         (\<not>(test a) \<longrightarrow> g a = False)"
  proof-  (* How can I prove this withou fixing a? *)
    fix a show "(test a \<longrightarrow> f a = wo_rel.suc r' (f`(rel.underS r a)) \<and> g a = True) \<and>
                (\<not>(test a) \<longrightarrow> g a = False)"
    using *[of a] test_def f_def g_def H_def by auto
  qed
  (*  *)
  let ?phi = "\<lambda> a. a \<in> Field r \<and> False \<notin> g`(rel.under r a) \<longrightarrow>
                   bij_betw f (rel.under r a) (rel.under r' (f a))"
  have Main2: "\<And> a. ?phi a"
  proof-
    fix a show "?phi a"
    proof(rule wo_rel.well_order_induct[of r ?phi],
          simp only: Well, clarify)
      fix a
      assume IH: "\<forall>b. b \<noteq> a \<and> (b,a) \<in> r \<longrightarrow> ?phi b" and
             *: "a \<in> Field r" and
             **: "False \<notin> g`(rel.under r a)"
      have 1: "\<forall>b \<in> rel.underS r a. bij_betw f (rel.under r b) (rel.under r' (f b))"
      proof(clarify)
        fix b assume ***: "b \<in> rel.underS r a"
        hence 0: "(b,a) \<in> r \<and> b \<noteq> a" unfolding rel.underS_def by auto
        moreover have "b \<in> Field r"
        using *** rel.underS_Field[of r a] by auto
        moreover have "False \<notin> g`(rel.under r b)"
        using 0 ** Trans rel.under_incr[of r b a] by auto
        ultimately show "bij_betw f (rel.under r b) (rel.under r' (f b))"
        using IH by auto
      qed
      (*  *)
      have 21: "False \<notin> g`(rel.underS r a)"
      using ** rel.underS_subset_under[of r a] by auto
      have 22: "g`(rel.under r a) \<le> {True}" using ** by auto
      moreover have 23: "a \<in> rel.under r a"
      using Refl * by (auto simp add: rel.Refl_under_in)
      ultimately have 24: "g a = True" by blast
      have 2: "f`(rel.underS r a) \<noteq> Field r'"
      proof
        assume "f`(rel.underS r a) = Field r'"
        hence "g a = False" using Main1 test_def by blast
        with 24 show False using ** by blast
      qed
      (*  *)
      have 3: "f a = wo_rel.suc r' (f`(rel.underS r a))"
      using 21 2 Main1 test_def by blast
      (*  *)
      show "bij_betw f (rel.under r a) (rel.under r' (f a))"
      using WELL  WELL' 1 2 3 *
            wellorders_totally_ordered_aux[of r r' a f] by auto
    qed
  qed
  (*  *)
  let ?chi = "(\<lambda> a. a \<in> Field r \<and> False \<in> g`(rel.under r a))"
  show ?thesis
  proof(cases "\<exists>a. ?chi a")
    assume "\<not> (\<exists>a. ?chi a)"
    hence "\<forall>a \<in> Field r.  bij_betw f (rel.under r a) (rel.under r' (f a))"
    using Main2 by blast
    thus ?thesis unfolding embed_def by blast
  next
    assume "\<exists>a. ?chi a"
    then obtain a where "?chi a" by blast
    hence "\<exists>f'. embed r' r f'"
    using wellorders_totally_ordered_aux2[of r r' g f a]
          WELL WELL' Main1 Main2 test_def by blast
    thus ?thesis by blast
  qed
qed


subsection {* Uniqueness of embeddings  *}


text{* Here we show a fact complementary to the one from the previous subsection -- namely,
that between any two well-orders there is {\em at most} one embedding, and is the one
definable by the expected well-order recursive equation.  As a consequence, any two
embeddings of opposite directions are mutually inverse. *}


lemma embed_determined:
assumes WELL: "Well_order r" and WELL': "Well_order r'" and
        EMB: "embed r r' f" and IN: "a \<in> Field r"
shows "f a = wo_rel.suc r' (f`(rel.underS r a))"
proof-
  have "bij_betw f (rel.underS r a) (rel.underS r' (f a))"
  using assms by (auto simp add: embed_underS)
  hence "f`(rel.underS r a) = rel.underS r' (f a)"
  by (auto simp add: bij_betw_def)
  moreover
  {have "f a \<in> Field r'" using IN
   using EMB WELL embed_Field[of r r' f] by auto
   hence "f a = wo_rel.suc r' (rel.underS r' (f a))"
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
  assume IH: "\<forall>b. b \<noteq> a \<and> (b,a): r \<longrightarrow> b \<in> Field r \<longrightarrow> f b = g b" and
         *: "a \<in> Field r"
  hence "\<forall>b \<in> rel.underS r a. f b = g b"
  unfolding rel.underS_def by (auto simp add: Field_def)
  hence "f`(rel.underS r a) = g`(rel.underS r a)" by force
  thus "f a = g a"
  using assms * embed_determined[of r r' f a] embed_determined[of r r' g a] by auto
qed


lemma embed_bothWays_inverse:
assumes WELL: "Well_order r" and WELL': "Well_order r'" and
        EMB: "embed r r' f" and EMB': "embed r' r f'"
shows "(\<forall>a \<in> Field r. f'(f a) = a) \<and> (\<forall>a' \<in> Field r'. f(f' a') = a')"
proof-
  have "embed r r (f' o f)" using assms
  by(auto simp add: comp_embed)
  moreover have "embed r r id" using assms
  by (auto simp add: id_embed)
  ultimately have "\<forall>a \<in> Field r. f'(f a) = a"
  using assms embed_unique[of r r "f' o f" id] id_def by auto
  moreover
  {have "embed r' r' (f o f')" using assms
   by(auto simp add: comp_embed)
   moreover have "embed r' r' id" using assms
   by (auto simp add: id_embed)
   ultimately have "\<forall>a' \<in> Field r'. f(f' a') = a'"
   using assms embed_unique[of r' r' "f o f'" id] id_def by auto
  }
  ultimately show ?thesis by blast
qed


lemma embed_bothWays_bij_betw:
assumes WELL: "Well_order r" and WELL': "Well_order r'" and
        EMB: "embed r r' f" and EMB': "embed r' r g"
shows "bij_betw f (Field r) (Field r')"
proof-
  let ?A = "Field r"  let ?A' = "Field r'"
  have "embed r r (g o f) \<and> embed r' r' (f o g)"
  using assms by (auto simp add: comp_embed)
  hence 1: "(\<forall>a \<in> ?A. g(f a) = a) \<and> (\<forall>a' \<in> ?A'. f(g a') = a')"
  using WELL id_embed[of r] embed_unique[of r r "g o f" id]
        WELL' id_embed[of r'] embed_unique[of r' r' "f o g" id]
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


subsection {* More properties of embeddings, strict embeddings and isomorphisms  *}


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
assumes WELL: "Well_order r" and WELL': "Well_order r'" and WELL'': "Well_order r''"
        and  EMB: "embedS r r' f" and EMB': "embed r' r'' f'"
shows "embedS r r'' (f' o f)"
proof-
  let ?g = "(f' o f)"  let ?h = "inv_into (Field r) ?g"
  have 1: "embed r r' f \<and> \<not> (bij_betw f (Field r) (Field r'))"
  using EMB by (auto simp add: embedS_def)
  hence 2: "embed r r'' ?g"
  using WELL EMB' comp_embed[of r r' f r'' f'] by auto
  moreover
  {assume "bij_betw ?g (Field r) (Field r'')"
   hence "embed r'' r ?h" using 2 WELL
   by (auto simp add: inv_into_Field_embed_bij_betw)
   hence "embed r' r (?h o f')" using WELL' EMB'
   by (auto simp add: comp_embed)
   hence "bij_betw f (Field r) (Field r')" using WELL WELL' 1
   by (auto simp add: embed_bothWays_Field_bij_betw)
   with 1 have False by blast
  }
  ultimately show ?thesis unfolding embedS_def by auto
qed


lemma embed_comp_embedS:
assumes WELL: "Well_order r" and WELL': "Well_order r'" and WELL'': "Well_order r''"
        and  EMB: "embed r r' f" and EMB': "embedS r' r'' f'"
shows "embedS r r'' (f' o f)"
proof-
  let ?g = "(f' o f)"  let ?h = "inv_into (Field r) ?g"
  have 1: "embed r' r'' f' \<and> \<not> (bij_betw f' (Field r') (Field r''))"
  using EMB' by (auto simp add: embedS_def)
  hence 2: "embed r r'' ?g"
  using WELL EMB comp_embed[of r r' f r'' f'] by auto
  moreover
  {assume "bij_betw ?g (Field r) (Field r'')"
   hence "embed r'' r ?h" using 2 WELL
   by (auto simp add: inv_into_Field_embed_bij_betw)
   hence "embed r'' r' (f o ?h)" using WELL'' EMB
   by (auto simp add: comp_embed)
   hence "bij_betw f' (Field r') (Field r'')" using WELL' WELL'' 1
   by (auto simp add: embed_bothWays_Field_bij_betw)
   with 1 have False by blast
  }
  ultimately show ?thesis unfolding embedS_def by auto
qed


lemma embed_comp_iso:
assumes WELL: "Well_order r" and WELL': "Well_order r'" and WELL'': "Well_order r''"
        and  EMB: "embed r r' f" and EMB': "iso r' r'' f'"
shows "embed r r'' (f' o f)"
using assms unfolding iso_def
by (auto simp add: comp_embed)


lemma iso_comp_embed:
assumes WELL: "Well_order r" and WELL': "Well_order r'" and WELL'': "Well_order r''"
        and  EMB: "iso r r' f" and EMB': "embed r' r'' f'"
shows "embed r r'' (f' o f)"
using assms unfolding iso_def
by (auto simp add: comp_embed)


lemma embedS_comp_iso:
assumes WELL: "Well_order r" and WELL': "Well_order r'" and WELL'': "Well_order r''"
        and  EMB: "embedS r r' f" and EMB': "iso r' r'' f'"
shows "embedS r r'' (f' o f)"
using assms unfolding iso_def
by (auto simp add: embedS_comp_embed)


lemma iso_comp_embedS:
assumes WELL: "Well_order r" and WELL': "Well_order r'" and WELL'': "Well_order r''"
        and  EMB: "iso r r' f" and EMB': "embedS r' r'' f'"
shows "embedS r r'' (f' o f)"
using assms unfolding iso_def  using embed_comp_embedS
by (auto simp add: embed_comp_embedS)


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


lemma iso_Field:
"iso r r' f \<Longrightarrow> f ` (Field r) = Field r'"
using assms by (auto simp add: iso_def bij_betw_def)


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


lemma iso_iff2:
assumes "Well_order r"
shows "iso r r' f = (bij_betw f (Field r) (Field r') \<and>
                     (\<forall>a \<in> Field r. \<forall>b \<in> Field r.
                         (((a,b) \<in> r) = ((f a, f b) \<in> r'))))"
using assms
proof(auto simp add: iso_def)
  fix a b
  assume "embed r r' f"
  hence "compat r r' f" using embed_compat[of r] by auto
  moreover assume "(a,b) \<in> r"
  ultimately show "(f a, f b) \<in> r'" using compat_def[of r] by auto
next
  let ?f' = "inv_into (Field r) f"
  assume "embed r r' f" and 1: "bij_betw f (Field r) (Field r')"
  hence "embed r' r ?f'" using assms
  by (auto simp add: inv_into_Field_embed_bij_betw)
  hence 2: "compat r' r ?f'" using embed_compat[of r'] by auto
  fix a b assume *: "a \<in> Field r" "b \<in> Field r" and **: "(f a,f b) \<in> r'"
  hence "?f'(f a) = a \<and> ?f'(f b) = b" using 1
  by (auto simp add: bij_betw_inv_into_left)
  thus "(a,b) \<in> r" using ** 2 compat_def[of r' r ?f'] by fastforce
next
  assume *: "bij_betw f (Field r) (Field r')" and
         **: "\<forall>a\<in>Field r. \<forall>b\<in>Field r. ((a, b) \<in> r) = ((f a, f b) \<in> r')"
  have 1: "\<And> a. rel.under r a \<le> Field r \<and> rel.under r' (f a) \<le> Field r'"
  by (auto simp add: rel.under_Field)
  have 2: "inj_on f (Field r)" using * by (auto simp add: bij_betw_def)
  {fix a assume ***: "a \<in> Field r"
   have "bij_betw f (rel.under r a) (rel.under r' (f a))"
   proof(unfold bij_betw_def, auto)
     show "inj_on f (rel.under r a)"
     using 1 2 by (auto simp add: subset_inj_on)
   next
     fix b assume "b \<in> rel.under r a"
     hence "a \<in> Field r \<and> b \<in> Field r \<and> (b,a) \<in> r"
     unfolding rel.under_def by (auto simp add: Field_def Range_def Domain_def)
     with 1 ** show "f b \<in> rel.under r' (f a)"
     unfolding rel.under_def by auto
   next
     fix b' assume "b' \<in> rel.under r' (f a)"
     hence 3: "(b',f a) \<in> r'" unfolding rel.under_def by simp
     hence "b' \<in> Field r'" unfolding Field_def by auto
     with * obtain b where "b \<in> Field r \<and> f b = b'"
     unfolding bij_betw_def by force
     with 3 ** ***
     show "b' \<in> f ` (rel.under r a)" unfolding rel.under_def by blast
   qed
  }
  thus "embed r r' f" unfolding embed_def using * by auto
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
     hence "(b,a): r"using Well ** wo_rel.REFL[of r] refl_on_def[of _ r] by blast
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



end
