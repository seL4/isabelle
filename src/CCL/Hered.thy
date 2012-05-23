(*  Title:      CCL/Hered.thy
    Author:     Martin Coen
    Copyright   1993  University of Cambridge
*)

header {* Hereditary Termination -- cf. Martin Lo\"f *}

theory Hered
imports Type
begin

text {*
  Note that this is based on an untyped equality and so @{text "lam
  x. b(x)"} is only hereditarily terminating if @{text "ALL x. b(x)"}
  is.  Not so useful for functions!
*}

definition HTTgen :: "i set => i set" where
  "HTTgen(R) ==
    {t. t=true | t=false | (EX a b. t= <a, b> & a : R & b : R) |
      (EX f. t = lam x. f(x) & (ALL x. f(x) : R))}"

definition HTT :: "i set"
  where "HTT == gfp(HTTgen)"


subsection {* Hereditary Termination *}

lemma HTTgen_mono: "mono(%X. HTTgen(X))"
  apply (unfold HTTgen_def)
  apply (rule monoI)
  apply blast
  done

lemma HTTgenXH: 
  "t : HTTgen(A) <-> t=true | t=false | (EX a b. t=<a,b> & a : A & b : A) |  
                                        (EX f. t=lam x. f(x) & (ALL x. f(x) : A))"
  apply (unfold HTTgen_def)
  apply blast
  done

lemma HTTXH: 
  "t : HTT <-> t=true | t=false | (EX a b. t=<a,b> & a : HTT & b : HTT) |  
                                   (EX f. t=lam x. f(x) & (ALL x. f(x) : HTT))"
  apply (rule HTTgen_mono [THEN HTT_def [THEN def_gfp_Tarski], THEN XHlemma1, unfolded HTTgen_def])
  apply blast
  done


subsection {* Introduction Rules for HTT *}

lemma HTT_bot: "~ bot : HTT"
  by (blast dest: HTTXH [THEN iffD1])

lemma HTT_true: "true : HTT"
  by (blast intro: HTTXH [THEN iffD2])

lemma HTT_false: "false : HTT"
  by (blast intro: HTTXH [THEN iffD2])

lemma HTT_pair: "<a,b> : HTT <->  a : HTT  & b : HTT"
  apply (rule HTTXH [THEN iff_trans])
  apply blast
  done

lemma HTT_lam: "lam x. f(x) : HTT <-> (ALL x. f(x) : HTT)"
  apply (rule HTTXH [THEN iff_trans])
  apply auto
  done

lemmas HTT_rews1 = HTT_bot HTT_true HTT_false HTT_pair HTT_lam

lemma HTT_rews2:
  "one : HTT"
  "inl(a) : HTT <-> a : HTT"
  "inr(b) : HTT <-> b : HTT"
  "zero : HTT"
  "succ(n) : HTT <-> n : HTT"
  "[] : HTT"
  "x$xs : HTT <-> x : HTT & xs : HTT"
  by (simp_all add: data_defs HTT_rews1)

lemmas HTT_rews = HTT_rews1 HTT_rews2


subsection {* Coinduction for HTT *}

lemma HTT_coinduct: "[|  t : R;  R <= HTTgen(R) |] ==> t : HTT"
  apply (erule HTT_def [THEN def_coinduct])
  apply assumption
  done

lemma HTT_coinduct3:
  "[|  t : R;   R <= HTTgen(lfp(%x. HTTgen(x) Un R Un HTT)) |] ==> t : HTT"
  apply (erule HTTgen_mono [THEN [3] HTT_def [THEN def_coinduct3]])
  apply assumption
  done

lemma HTTgenIs:
  "true : HTTgen(R)"
  "false : HTTgen(R)"
  "[| a : R;  b : R |] ==> <a,b> : HTTgen(R)"
  "!!b. [| !!x. b(x) : R |] ==> lam x. b(x) : HTTgen(R)"
  "one : HTTgen(R)"
  "a : lfp(%x. HTTgen(x) Un R Un HTT) ==> inl(a) : HTTgen(lfp(%x. HTTgen(x) Un R Un HTT))"
  "b : lfp(%x. HTTgen(x) Un R Un HTT) ==> inr(b) : HTTgen(lfp(%x. HTTgen(x) Un R Un HTT))"
  "zero : HTTgen(lfp(%x. HTTgen(x) Un R Un HTT))"
  "n : lfp(%x. HTTgen(x) Un R Un HTT) ==> succ(n) : HTTgen(lfp(%x. HTTgen(x) Un R Un HTT))"
  "[] : HTTgen(lfp(%x. HTTgen(x) Un R Un HTT))"
  "[| h : lfp(%x. HTTgen(x) Un R Un HTT); t : lfp(%x. HTTgen(x) Un R Un HTT) |] ==>
    h$t : HTTgen(lfp(%x. HTTgen(x) Un R Un HTT))"
  unfolding data_defs by (genIs HTTgenXH HTTgen_mono)+


subsection {* Formation Rules for Types *}

lemma UnitF: "Unit <= HTT"
  by (simp add: subsetXH UnitXH HTT_rews)

lemma BoolF: "Bool <= HTT"
  by (fastforce simp: subsetXH BoolXH iff: HTT_rews)

lemma PlusF: "[| A <= HTT;  B <= HTT |] ==> A + B  <= HTT"
  by (fastforce simp: subsetXH PlusXH iff: HTT_rews)

lemma SigmaF: "[| A <= HTT;  !!x. x:A ==> B(x) <= HTT |] ==> SUM x:A. B(x) <= HTT"
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

lemma ListF: "A <= HTT ==> List(A) <= HTT"
  apply clarify
  apply (erule HTT_coinduct3)
  apply (fast intro!: HTTgenIs elim!: HTTgen_mono [THEN ci3_RI]
    subsetD [THEN HTTgen_mono [THEN ci3_AI]]
    dest: ListXH [THEN iffD1])
  done

lemma ListsF: "A <= HTT ==> Lists(A) <= HTT"
  apply clarify
  apply (erule HTT_coinduct3)
  apply (fast intro!: HTTgenIs elim!: HTTgen_mono [THEN ci3_RI]
    subsetD [THEN HTTgen_mono [THEN ci3_AI]] dest: ListsXH [THEN iffD1])
  done

lemma IListsF: "A <= HTT ==> ILists(A) <= HTT"
  apply clarify
  apply (erule HTT_coinduct3)
  apply (fast intro!: HTTgenIs elim!: HTTgen_mono [THEN ci3_RI]
    subsetD [THEN HTTgen_mono [THEN ci3_AI]] dest: IListsXH [THEN iffD1])
  done

end
