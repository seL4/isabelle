(*  Title:      CCL/Hered.thy
    Author:     Martin Coen
    Copyright   1993  University of Cambridge
*)

section {* Hereditary Termination -- cf. Martin Lo\"f *}

theory Hered
imports Type
begin

text {*
  Note that this is based on an untyped equality and so @{text "lam
  x. b(x)"} is only hereditarily terminating if @{text "ALL x. b(x)"}
  is.  Not so useful for functions!
*}

definition HTTgen :: "i set \<Rightarrow> i set" where
  "HTTgen(R) ==
    {t. t=true | t=false | (EX a b. t= <a, b> \<and> a : R \<and> b : R) |
      (EX f. t = lam x. f(x) \<and> (ALL x. f(x) : R))}"

definition HTT :: "i set"
  where "HTT == gfp(HTTgen)"


subsection {* Hereditary Termination *}

lemma HTTgen_mono: "mono(\<lambda>X. HTTgen(X))"
  apply (unfold HTTgen_def)
  apply (rule monoI)
  apply blast
  done

lemma HTTgenXH: 
  "t : HTTgen(A) \<longleftrightarrow> t=true | t=false | (EX a b. t=<a,b> \<and> a : A \<and> b : A) |  
                                        (EX f. t=lam x. f(x) \<and> (ALL x. f(x) : A))"
  apply (unfold HTTgen_def)
  apply blast
  done

lemma HTTXH: 
  "t : HTT \<longleftrightarrow> t=true | t=false | (EX a b. t=<a,b> \<and> a : HTT \<and> b : HTT) |  
                                   (EX f. t=lam x. f(x) \<and> (ALL x. f(x) : HTT))"
  apply (rule HTTgen_mono [THEN HTT_def [THEN def_gfp_Tarski], THEN XHlemma1, unfolded HTTgen_def])
  apply blast
  done


subsection {* Introduction Rules for HTT *}

lemma HTT_bot: "\<not> bot : HTT"
  by (blast dest: HTTXH [THEN iffD1])

lemma HTT_true: "true : HTT"
  by (blast intro: HTTXH [THEN iffD2])

lemma HTT_false: "false : HTT"
  by (blast intro: HTTXH [THEN iffD2])

lemma HTT_pair: "<a,b> : HTT \<longleftrightarrow> a : HTT \<and> b : HTT"
  apply (rule HTTXH [THEN iff_trans])
  apply blast
  done

lemma HTT_lam: "lam x. f(x) : HTT \<longleftrightarrow> (ALL x. f(x) : HTT)"
  apply (rule HTTXH [THEN iff_trans])
  apply auto
  done

lemmas HTT_rews1 = HTT_bot HTT_true HTT_false HTT_pair HTT_lam

lemma HTT_rews2:
  "one : HTT"
  "inl(a) : HTT \<longleftrightarrow> a : HTT"
  "inr(b) : HTT \<longleftrightarrow> b : HTT"
  "zero : HTT"
  "succ(n) : HTT \<longleftrightarrow> n : HTT"
  "[] : HTT"
  "x$xs : HTT \<longleftrightarrow> x : HTT \<and> xs : HTT"
  by (simp_all add: data_defs HTT_rews1)

lemmas HTT_rews = HTT_rews1 HTT_rews2


subsection {* Coinduction for HTT *}

lemma HTT_coinduct: "\<lbrakk>t : R; R <= HTTgen(R)\<rbrakk> \<Longrightarrow> t : HTT"
  apply (erule HTT_def [THEN def_coinduct])
  apply assumption
  done

lemma HTT_coinduct3: "\<lbrakk>t : R; R <= HTTgen(lfp(\<lambda>x. HTTgen(x) Un R Un HTT))\<rbrakk> \<Longrightarrow> t : HTT"
  apply (erule HTTgen_mono [THEN [3] HTT_def [THEN def_coinduct3]])
  apply assumption
  done

lemma HTTgenIs:
  "true : HTTgen(R)"
  "false : HTTgen(R)"
  "\<lbrakk>a : R; b : R\<rbrakk> \<Longrightarrow> <a,b> : HTTgen(R)"
  "\<And>b. (\<And>x. b(x) : R) \<Longrightarrow> lam x. b(x) : HTTgen(R)"
  "one : HTTgen(R)"
  "a : lfp(\<lambda>x. HTTgen(x) Un R Un HTT) \<Longrightarrow> inl(a) : HTTgen(lfp(\<lambda>x. HTTgen(x) Un R Un HTT))"
  "b : lfp(\<lambda>x. HTTgen(x) Un R Un HTT) \<Longrightarrow> inr(b) : HTTgen(lfp(\<lambda>x. HTTgen(x) Un R Un HTT))"
  "zero : HTTgen(lfp(\<lambda>x. HTTgen(x) Un R Un HTT))"
  "n : lfp(\<lambda>x. HTTgen(x) Un R Un HTT) \<Longrightarrow> succ(n) : HTTgen(lfp(\<lambda>x. HTTgen(x) Un R Un HTT))"
  "[] : HTTgen(lfp(\<lambda>x. HTTgen(x) Un R Un HTT))"
  "\<lbrakk>h : lfp(\<lambda>x. HTTgen(x) Un R Un HTT); t : lfp(\<lambda>x. HTTgen(x) Un R Un HTT)\<rbrakk> \<Longrightarrow>
    h$t : HTTgen(lfp(\<lambda>x. HTTgen(x) Un R Un HTT))"
  unfolding data_defs by (genIs HTTgenXH HTTgen_mono)+


subsection {* Formation Rules for Types *}

lemma UnitF: "Unit <= HTT"
  by (simp add: subsetXH UnitXH HTT_rews)

lemma BoolF: "Bool <= HTT"
  by (fastforce simp: subsetXH BoolXH iff: HTT_rews)

lemma PlusF: "\<lbrakk>A <= HTT; B <= HTT\<rbrakk> \<Longrightarrow> A + B  <= HTT"
  by (fastforce simp: subsetXH PlusXH iff: HTT_rews)

lemma SigmaF: "\<lbrakk>A <= HTT; \<And>x. x:A \<Longrightarrow> B(x) <= HTT\<rbrakk> \<Longrightarrow> SUM x:A. B(x) <= HTT"
  by (fastforce simp: subsetXH SgXH HTT_rews)


(*** Formation Rules for Recursive types - using coinduction these only need ***)
(***                                          exhaution rule for type-former ***)

(*Proof by induction - needs induction rule for type*)
lemma "Nat <= HTT"
  apply (simp add: subsetXH)
  apply clarify
  apply (erule Nat_ind)
   apply (fastforce iff: HTT_rews)+
  done

lemma NatF: "Nat <= HTT"
  apply clarify
  apply (erule HTT_coinduct3)
  apply (fast intro: HTTgenIs elim!: HTTgen_mono [THEN ci3_RI] dest: NatXH [THEN iffD1])
  done

lemma ListF: "A <= HTT \<Longrightarrow> List(A) <= HTT"
  apply clarify
  apply (erule HTT_coinduct3)
  apply (fast intro!: HTTgenIs elim!: HTTgen_mono [THEN ci3_RI]
    subsetD [THEN HTTgen_mono [THEN ci3_AI]]
    dest: ListXH [THEN iffD1])
  done

lemma ListsF: "A <= HTT \<Longrightarrow> Lists(A) <= HTT"
  apply clarify
  apply (erule HTT_coinduct3)
  apply (fast intro!: HTTgenIs elim!: HTTgen_mono [THEN ci3_RI]
    subsetD [THEN HTTgen_mono [THEN ci3_AI]] dest: ListsXH [THEN iffD1])
  done

lemma IListsF: "A <= HTT \<Longrightarrow> ILists(A) <= HTT"
  apply clarify
  apply (erule HTT_coinduct3)
  apply (fast intro!: HTTgenIs elim!: HTTgen_mono [THEN ci3_RI]
    subsetD [THEN HTTgen_mono [THEN ci3_AI]] dest: IListsXH [THEN iffD1])
  done

end
