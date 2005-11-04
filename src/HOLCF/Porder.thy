(*  Title:      HOLCF/Porder.thy
    ID:         $Id$
    Author:     Franz Regensburger
*)

header {* Partial orders *}

theory Porder
imports Main
begin

subsection {* Type class for partial orders *}

	-- {* introduce a (syntactic) class for the constant @{text "<<"} *}
axclass sq_ord < type

	-- {* characteristic constant @{text "<<"} for po *}
consts
  "<<"          :: "['a,'a::sq_ord] => bool"        (infixl "<<" 55)

syntax (xsymbols)
  "<<"       :: "['a,'a::sq_ord] => bool"        (infixl "\<sqsubseteq>" 55)

axclass po < sq_ord
        -- {* class axioms: *}
  refl_less [iff]: "x \<sqsubseteq> x"        
  antisym_less:    "\<lbrakk>x \<sqsubseteq> y; y \<sqsubseteq> x\<rbrakk> \<Longrightarrow> x = y"    
  trans_less:      "\<lbrakk>x \<sqsubseteq> y; y \<sqsubseteq> z\<rbrakk> \<Longrightarrow> x \<sqsubseteq> z"

text {* minimal fixes least element *}

lemma minimal2UU[OF allI] : "\<forall>x::'a::po. uu \<sqsubseteq> x \<Longrightarrow> uu = (THE u. \<forall>y. u \<sqsubseteq> y)"
by (blast intro: theI2 antisym_less)

text {* the reverse law of anti-symmetry of @{term "op <<"} *}

lemma antisym_less_inverse: "(x::'a::po) = y \<Longrightarrow> x \<sqsubseteq> y \<and> y \<sqsubseteq> x"
by simp

lemma box_less: "\<lbrakk>(a::'a::po) \<sqsubseteq> b; c \<sqsubseteq> a; b \<sqsubseteq> d\<rbrakk> \<Longrightarrow> c \<sqsubseteq> d"
by (rule trans_less [OF trans_less])

lemma po_eq_conv: "((x::'a::po) = y) = (x \<sqsubseteq> y \<and> y \<sqsubseteq> x)"
by (fast elim!: antisym_less_inverse intro!: antisym_less)

lemma rev_trans_less: "\<lbrakk>(y::'a::po) \<sqsubseteq> z; x \<sqsubseteq> y\<rbrakk> \<Longrightarrow> x \<sqsubseteq> z"
by (rule trans_less)

subsection {* Chains and least upper bounds *}

constdefs  

  -- {* class definitions *}
  is_ub :: "['a set, 'a::po] \<Rightarrow> bool"       (infixl "<|" 55)
  "S <| x \<equiv> \<forall>y. y \<in> S \<longrightarrow> y \<sqsubseteq> x"

  is_lub :: "['a set, 'a::po] \<Rightarrow> bool"       (infixl "<<|" 55)
  "S <<| x \<equiv> S <| x \<and> (\<forall>u. S <| u \<longrightarrow> x \<sqsubseteq> u)"

  -- {* Arbitrary chains are total orders *}
  tord :: "'a::po set \<Rightarrow> bool"
  "tord S \<equiv> \<forall>x y. x \<in> S \<and> y \<in> S \<longrightarrow> (x \<sqsubseteq> y \<or> y \<sqsubseteq> x)"

  -- {* Here we use countable chains and I prefer to code them as functions! *}
  chain :: "(nat \<Rightarrow> 'a::po) \<Rightarrow> bool"
  "chain F \<equiv> \<forall>i. F i \<sqsubseteq> F (Suc i)"

  -- {* finite chains, needed for monotony of continuous functions *}
  max_in_chain :: "[nat, nat \<Rightarrow> 'a::po] \<Rightarrow> bool"
  "max_in_chain i C \<equiv> \<forall>j. i \<le> j \<longrightarrow> C i = C j" 

  finite_chain :: "(nat \<Rightarrow> 'a::po) \<Rightarrow> bool"
  "finite_chain C \<equiv> chain(C) \<and> (\<exists>i. max_in_chain i C)"

  lub :: "'a set \<Rightarrow> 'a::po"
  "lub S \<equiv> THE x. S <<| x"

syntax
  "@LUB"	:: "('b \<Rightarrow> 'a) \<Rightarrow> 'a"	(binder "LUB " 10)

syntax (xsymbols)
  "LUB "	:: "[idts, 'a] \<Rightarrow> 'a"		("(3\<Squnion>_./ _)" [0,10] 10)

translations
  "\<Squnion>n. t" == "lub(range(\<lambda>n. t))"

text {* lubs are unique *}

lemma unique_lub: "\<lbrakk>S <<| x; S <<| y\<rbrakk> \<Longrightarrow> x = y"
apply (unfold is_lub_def is_ub_def)
apply (blast intro: antisym_less)
done

text {* chains are monotone functions *}

lemma chain_mono [rule_format]: "chain F \<Longrightarrow> x < y \<longrightarrow> F x \<sqsubseteq> F y"
apply (unfold chain_def)
apply (induct_tac y)
apply simp
apply (blast elim: less_SucE intro: trans_less)
done

lemma chain_mono3: "\<lbrakk>chain F; x \<le> y\<rbrakk> \<Longrightarrow> F x \<sqsubseteq> F y"
apply (drule le_imp_less_or_eq)
apply (blast intro: chain_mono)
done

text {* The range of a chain is a totally ordered *}

lemma chain_tord: "chain F \<Longrightarrow> tord (range F)"
apply (unfold tord_def, clarify)
apply (rule nat_less_cases)
apply (fast intro: chain_mono)+
done

text {* technical lemmas about @{term lub} and @{term is_lub} *}

lemmas lub = lub_def [THEN meta_eq_to_obj_eq, standard]

lemma lubI: "M <<| x \<Longrightarrow> M <<| lub M"
apply (unfold lub_def)
apply (rule theI)
apply assumption
apply (erule (1) unique_lub)
done

lemma thelubI: "M <<| l \<Longrightarrow> lub M = l"
by (rule unique_lub [OF lubI])

lemma lub_singleton [simp]: "lub {x} = x"
by (simp add: thelubI is_lub_def is_ub_def)

text {* access to some definition as inference rule *}

lemma is_lubD1: "S <<| x \<Longrightarrow> S <| x"
by (unfold is_lub_def, simp)

lemma is_lub_lub: "\<lbrakk>S <<| x; S <| u\<rbrakk> \<Longrightarrow> x \<sqsubseteq> u"
by (unfold is_lub_def, simp)

lemma is_lubI: "\<lbrakk>S <| x; \<And>u. S <| u \<Longrightarrow> x \<sqsubseteq> u\<rbrakk> \<Longrightarrow> S <<| x"
by (unfold is_lub_def, fast)

lemma chainE: "chain F \<Longrightarrow> F i \<sqsubseteq> F (Suc i)"
by (unfold chain_def, simp)

lemma chainI: "(\<And>i. F i \<sqsubseteq> F (Suc i)) \<Longrightarrow> chain F"
by (unfold chain_def, simp)

lemma chain_shift: "chain Y \<Longrightarrow> chain (\<lambda>i. Y (i + j))"
apply (rule chainI)
apply simp
apply (erule chainE)
done

text {* technical lemmas about (least) upper bounds of chains *}

lemma ub_rangeD: "range S <| x \<Longrightarrow> S i \<sqsubseteq> x"
by (unfold is_ub_def, simp)

lemma ub_rangeI: "(\<And>i. S i \<sqsubseteq> x) \<Longrightarrow> range S <| x"
by (unfold is_ub_def, fast)

lemma is_ub_lub: "range S <<| x \<Longrightarrow> S i \<sqsubseteq> x"
by (rule is_lubD1 [THEN ub_rangeD])

lemma is_ub_range_shift:
  "chain S \<Longrightarrow> range (\<lambda>i. S (i + j)) <| x = range S <| x"
apply (rule iffI)
apply (rule ub_rangeI)
apply (rule_tac y="S (i + j)" in trans_less)
apply (erule chain_mono3)
apply (rule le_add1)
apply (erule ub_rangeD)
apply (rule ub_rangeI)
apply (erule ub_rangeD)
done

lemma is_lub_range_shift:
  "chain S \<Longrightarrow> range (\<lambda>i. S (i + j)) <<| x = range S <<| x"
by (simp add: is_lub_def is_ub_range_shift)

text {* results about finite chains *}

lemma lub_finch1: "\<lbrakk>chain C; max_in_chain i C\<rbrakk> \<Longrightarrow> range C <<| C i"
apply (unfold max_in_chain_def)
apply (rule is_lubI)
apply (rule ub_rangeI, rename_tac j)
apply (rule_tac x=i and y=j in linorder_le_cases)
apply simp
apply (erule (1) chain_mono3)
apply (erule ub_rangeD)
done

lemma lub_finch2: 
        "finite_chain C \<Longrightarrow> range C <<| C (LEAST i. max_in_chain i C)"
apply (unfold finite_chain_def)
apply (erule conjE)
apply (erule LeastI2_ex)
apply (erule (1) lub_finch1)
done

lemma bin_chain: "x \<sqsubseteq> y \<Longrightarrow> chain (\<lambda>i. if i=0 then x else y)"
by (rule chainI, simp)

lemma bin_chainmax:
  "x \<sqsubseteq> y \<Longrightarrow> max_in_chain (Suc 0) (\<lambda>i. if i=0 then x else y)"
by (unfold max_in_chain_def, simp)

lemma lub_bin_chain:
  "x \<sqsubseteq> y \<Longrightarrow> range (\<lambda>i::nat. if i=0 then x else y) <<| y"
apply (frule bin_chain)
apply (drule bin_chainmax)
apply (drule (1) lub_finch1)
apply simp
done

text {* the maximal element in a chain is its lub *}

lemma lub_chain_maxelem: "\<lbrakk>Y i = c; \<forall>i. Y i \<sqsubseteq> c\<rbrakk> \<Longrightarrow> lub (range Y) = c"
by (blast dest: ub_rangeD intro: thelubI is_lubI ub_rangeI)

text {* the lub of a constant chain is the constant *}

lemma chain_const [simp]: "chain (\<lambda>i. c)"
by (simp add: chainI)

lemma lub_const: "range (\<lambda>x. c) <<| c"
by (blast dest: ub_rangeD intro: is_lubI ub_rangeI)

lemma thelub_const [simp]: "(\<Squnion>i. c) = c"
by (rule lub_const [THEN thelubI])

end
