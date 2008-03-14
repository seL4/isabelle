(*  ID          : $Id$
    Author      : Tobias Nipkow

Orders as relations with implicit base set, their Field
*)

header {* Orders as Relations *}

theory Order_Relation
imports ATP_Linkup Hilbert_Choice
begin

definition "Refl r \<equiv> \<forall>x \<in> Field r. (x,x) \<in> r"
definition "Preorder r \<equiv> Refl r \<and> trans r"
definition "Partial_order r \<equiv> Preorder r \<and> antisym r"
definition "Total r \<equiv> \<forall>x\<in>Field r.\<forall>y\<in>Field r. x\<noteq>y \<longrightarrow> (x,y)\<in>r \<or> (y,x)\<in>r"
definition "Linear_order r \<equiv> Partial_order r \<and> Total r"
definition "Well_order r \<equiv> Linear_order r \<and> wf(r - Id)"

lemmas Order_defs =
  Preorder_def Partial_order_def Linear_order_def Well_order_def

lemma Refl_empty[simp]: "Refl {}"
by(simp add:Refl_def)

lemma Preorder_empty[simp]: "Preorder {}"
by(simp add:Preorder_def trans_def)

lemma Partial_order_empty[simp]: "Partial_order {}"
by(simp add:Partial_order_def)

lemma Total_empty[simp]: "Total {}"
by(simp add:Total_def)

lemma Linear_order_empty[simp]: "Linear_order {}"
by(simp add:Linear_order_def)

lemma Well_order_empty[simp]: "Well_order {}"
by(simp add:Well_order_def)

lemma Refl_converse[simp]: "Refl(r^-1) = Refl r"
by(simp add:Refl_def)

lemma Preorder_converse[simp]: "Preorder (r^-1) = Preorder r"
by (simp add:Preorder_def)

lemma Partial_order_converse[simp]: "Partial_order (r^-1) = Partial_order r"
by (simp add: Partial_order_def)

lemma Total_converse[simp]: "Total (r^-1) = Total r"
by (auto simp: Total_def)

lemma Linear_order_converse[simp]: "Linear_order (r^-1) = Linear_order r"
by (simp add: Linear_order_def)

lemma subset_Image_Image_iff:
  "\<lbrakk> Preorder r; A \<subseteq> Field r; B \<subseteq> Field r\<rbrakk> \<Longrightarrow>
   r `` A \<subseteq> r `` B \<longleftrightarrow> (\<forall>a\<in>A.\<exists>b\<in>B. (b,a):r)"
apply(auto simp add:subset_def Preorder_def Refl_def Image_def)
apply metis
by(metis trans_def)

lemma subset_Image1_Image1_iff:
  "\<lbrakk> Preorder r; a : Field r; b : Field r\<rbrakk> \<Longrightarrow> r `` {a} \<subseteq> r `` {b} \<longleftrightarrow> (b,a):r"
by(simp add:subset_Image_Image_iff)

lemma Refl_antisym_eq_Image1_Image1_iff:
  "\<lbrakk>Refl r; antisym r; a:Field r; b:Field r\<rbrakk> \<Longrightarrow> r `` {a} = r `` {b} \<longleftrightarrow> a=b"
by(simp add:Preorder_def expand_set_eq Partial_order_def antisym_def Refl_def)
  metis

lemma Partial_order_eq_Image1_Image1_iff:
  "\<lbrakk>Partial_order r; a:Field r; b:Field r\<rbrakk> \<Longrightarrow> r `` {a} = r `` {b} \<longleftrightarrow> a=b"
by(auto simp:Preorder_def Partial_order_def Refl_antisym_eq_Image1_Image1_iff)

end
