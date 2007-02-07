(*  Title:      HOL/FixedPoint.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Author:     Stefan Berghofer, TU Muenchen
    Copyright   1992  University of Cambridge
*)

header{* Fixed Points and the Knaster-Tarski Theorem*}

theory FixedPoint
imports Product_Type LOrder
begin

subsection {* Complete lattices *}
(*FIXME Meet \<rightarrow> Inf *)
consts
  Meet :: "'a::order set \<Rightarrow> 'a"
  Sup :: "'a::order set \<Rightarrow> 'a"

defs Sup_def: "Sup A == Meet {b. \<forall>a \<in> A. a <= b}"

definition
  SUP :: "('a \<Rightarrow> 'b::order) \<Rightarrow> 'b"  (binder "SUP " 10) where
  "SUP x. f x == Sup (f ` UNIV)"

(*
abbreviation
  bot :: "'a::order" where
  "bot == Sup {}"
*)
axclass comp_lat < order
  Meet_lower: "x \<in> A \<Longrightarrow> Meet A <= x"
  Meet_greatest: "(\<And>x. x \<in> A \<Longrightarrow> z <= x) \<Longrightarrow> z <= Meet A"

theorem Sup_upper: "(x::'a::comp_lat) \<in> A \<Longrightarrow> x <= Sup A"
  by (auto simp: Sup_def intro: Meet_greatest)

theorem Sup_least: "(\<And>x::'a::comp_lat. x \<in> A \<Longrightarrow> x <= z) \<Longrightarrow> Sup A <= z"
  by (auto simp: Sup_def intro: Meet_lower)

text {* A complete lattice is a lattice *}

lemma is_meet_Meet: "is_meet (\<lambda>(x::'a::comp_lat) y. Meet {x, y})"
  by (auto simp: is_meet_def intro: Meet_lower Meet_greatest)

lemma is_join_Sup: "is_join (\<lambda>(x::'a::comp_lat) y. Sup {x, y})"
  by (auto simp: is_join_def intro: Sup_upper Sup_least)

instance comp_lat < lorder
proof
  from is_meet_Meet show "\<exists>m::'a\<Rightarrow>'a\<Rightarrow>'a. is_meet m" by iprover
  from is_join_Sup show "\<exists>j::'a\<Rightarrow>'a\<Rightarrow>'a. is_join j" by iprover
qed

subsubsection {* Properties *}

lemma mono_join: "mono f \<Longrightarrow> join (f A) (f B) <= f (join A B)"
  by (auto simp add: mono_def)

lemma mono_meet: "mono f \<Longrightarrow> f (meet A B) <= meet (f A) (f B)"
  by (auto simp add: mono_def)

lemma Sup_insert[simp]: "Sup (insert (a::'a::comp_lat) A) = join a (Sup A)"
apply(simp add:Sup_def)
apply(rule order_antisym)
 apply(rule Meet_lower)
 apply(clarsimp)
 apply(rule le_joinI2)
 apply(rule Meet_greatest)
 apply blast
apply simp
apply rule
 apply(rule Meet_greatest)apply blast
apply(rule Meet_greatest)
apply(rule Meet_lower)
apply blast
done

lemma bot_least[simp]: "Sup{} \<le> (x::'a::comp_lat)"
apply(simp add: Sup_def)
apply(rule Meet_lower)
apply blast
done
(*
lemma Meet_singleton[simp]: "Meet{a} = (a::'a::comp_lat)"
apply(rule order_antisym)
 apply(simp add: Meet_lower)
apply(rule Meet_greatest)
apply(simp)
done
*)
lemma le_SupI: "(l::'a::comp_lat) : M \<Longrightarrow> l \<le> Sup M"
apply(simp add:Sup_def)
apply(rule Meet_greatest)
apply(simp)
done

lemma le_SUPI: "(l::'a::comp_lat) = M i \<Longrightarrow> l \<le> (SUP i. M i)"
apply(simp add:SUP_def)
apply(blast intro:le_SupI)
done

lemma Sup_leI: "(!!x. x:M \<Longrightarrow> x \<le> u) \<Longrightarrow> Sup M \<le> (u::'a::comp_lat)"
apply(simp add:Sup_def)
apply(rule Meet_lower)
apply(blast)
done


lemma SUP_leI: "(!!i. M i \<le> u) \<Longrightarrow> (SUP i. M i) \<le> (u::'a::comp_lat)"
apply(simp add:SUP_def)
apply(blast intro!:Sup_leI)
done

lemma SUP_const[simp]: "(SUP i. M) = (M::'a::comp_lat)"
by(simp add:SUP_def image_constant_conv join_absorp1)


subsection {* Some instances of the type class of complete lattices *}

subsubsection {* Booleans *}

defs Meet_bool_def: "Meet A == ALL x:A. x"

instance bool :: comp_lat
  apply intro_classes
  apply (unfold Meet_bool_def)
  apply (iprover intro!: le_boolI elim: ballE)
  apply (iprover intro!: ballI le_boolI elim: ballE le_boolE)
  done

theorem meet_bool_eq: "meet P Q = (P \<and> Q)"
  apply (rule order_antisym)
  apply (rule le_boolI)
  apply (rule conjI)
  apply (rule le_boolE)
  apply (rule meet_left_le)
  apply assumption+
  apply (rule le_boolE)
  apply (rule meet_right_le)
  apply assumption+
  apply (rule le_meetI)
  apply (rule le_boolI)
  apply (erule conjunct1)
  apply (rule le_boolI)
  apply (erule conjunct2)
  done

theorem join_bool_eq: "join P Q = (P \<or> Q)"
  apply (rule order_antisym)
  apply (rule join_leI)
  apply (rule le_boolI)
  apply (erule disjI1)
  apply (rule le_boolI)
  apply (erule disjI2)
  apply (rule le_boolI)
  apply (erule disjE)
  apply (rule le_boolE)
  apply (rule join_left_le)
  apply assumption+
  apply (rule le_boolE)
  apply (rule join_right_le)
  apply assumption+
  done

theorem Sup_bool_eq: "Sup A = (EX x:A. x)"
  apply (rule order_antisym)
  apply (rule Sup_least)
  apply (rule le_boolI)
  apply (erule bexI, assumption)
  apply (rule le_boolI)
  apply (erule bexE)
  apply (rule le_boolE)
  apply (rule Sup_upper)
  apply assumption+
  done

subsubsection {* Functions *}

text {*
Handy introduction and elimination rules for @{text "\<le>"}
on unary and binary predicates
*}

lemma predicate1I [Pure.intro!, intro!]:
  assumes PQ: "\<And>x. P x \<Longrightarrow> Q x"
  shows "P \<le> Q"
  apply (rule le_funI)
  apply (rule le_boolI)
  apply (rule PQ)
  apply assumption
  done

lemma predicate1D [Pure.dest, dest]: "P \<le> Q \<Longrightarrow> P x \<Longrightarrow> Q x"
  apply (erule le_funE)
  apply (erule le_boolE)
  apply assumption+
  done

lemma predicate2I [Pure.intro!, intro!]:
  assumes PQ: "\<And>x y. P x y \<Longrightarrow> Q x y"
  shows "P \<le> Q"
  apply (rule le_funI)+
  apply (rule le_boolI)
  apply (rule PQ)
  apply assumption
  done

lemma predicate2D [Pure.dest, dest]: "P \<le> Q \<Longrightarrow> P x y \<Longrightarrow> Q x y"
  apply (erule le_funE)+
  apply (erule le_boolE)
  apply assumption+
  done

lemma rev_predicate1D: "P x ==> P <= Q ==> Q x"
  by (rule predicate1D)

lemma rev_predicate2D: "P x y ==> P <= Q ==> Q x y"
  by (rule predicate2D)

defs Meet_fun_def: "Meet A == (\<lambda>x. Meet {y. EX f:A. y = f x})"

instance "fun" :: (type, comp_lat) comp_lat
  apply intro_classes
  apply (unfold Meet_fun_def)
  apply (rule le_funI)
  apply (rule Meet_lower)
  apply (rule CollectI)
  apply (rule bexI)
  apply (rule refl)
  apply assumption
  apply (rule le_funI)
  apply (rule Meet_greatest)
  apply (erule CollectE)
  apply (erule bexE)
  apply (iprover elim: le_funE)
  done

theorem meet_fun_eq: "meet f g = (\<lambda>x. meet (f x) (g x))"
  apply (rule order_antisym)
  apply (rule le_funI)
  apply (rule le_meetI)
  apply (rule le_funD [OF meet_left_le])
  apply (rule le_funD [OF meet_right_le])
  apply (rule le_meetI)
  apply (rule le_funI)
  apply (rule meet_left_le)
  apply (rule le_funI)
  apply (rule meet_right_le)
  done

theorem join_fun_eq: "join f g = (\<lambda>x. join (f x) (g x))"
  apply (rule order_antisym)
  apply (rule join_leI)
  apply (rule le_funI)
  apply (rule join_left_le)
  apply (rule le_funI)
  apply (rule join_right_le)
  apply (rule le_funI)
  apply (rule join_leI)
  apply (rule le_funD [OF join_left_le])
  apply (rule le_funD [OF join_right_le])
  done

theorem Sup_fun_eq: "Sup A = (\<lambda>x. Sup {y::'a::comp_lat. EX f:A. y = f x})"
  apply (rule order_antisym)
  apply (rule Sup_least)
  apply (rule le_funI)
  apply (rule Sup_upper)
  apply fast
  apply (rule le_funI)
  apply (rule Sup_least)
  apply (erule CollectE)
  apply (erule bexE)
  apply (drule le_funD [OF Sup_upper])
  apply simp
  done

subsubsection {* Sets *}

defs Meet_set_def: "Meet S == \<Inter>S"

instance set :: (type) comp_lat
  by intro_classes (auto simp add: Meet_set_def)

theorem meet_set_eq: "meet A B = A \<inter> B"
  apply (rule subset_antisym)
  apply (rule Int_greatest)
  apply (rule meet_left_le)
  apply (rule meet_right_le)
  apply (rule le_meetI)
  apply (rule Int_lower1)
  apply (rule Int_lower2)
  done

theorem join_set_eq: "join A B = A \<union> B"
  apply (rule subset_antisym)
  apply (rule join_leI)
  apply (rule Un_upper1)
  apply (rule Un_upper2)
  apply (rule Un_least)
  apply (rule join_left_le)
  apply (rule join_right_le)
  done

theorem Sup_set_eq: "Sup S = \<Union>S"
  apply (rule subset_antisym)
  apply (rule Sup_least)
  apply (erule Union_upper)
  apply (rule Union_least)
  apply (erule Sup_upper)
  done


subsection {* Least and greatest fixed points *}

constdefs
  lfp :: "(('a::comp_lat) => 'a) => 'a"
  "lfp f == Meet {u. f u <= u}"    --{*least fixed point*}

  gfp :: "(('a::comp_lat) => 'a) => 'a"
  "gfp f == Sup {u. u <= f u}"    --{*greatest fixed point*}


subsection{*Proof of Knaster-Tarski Theorem using @{term lfp}*}


text{*@{term "lfp f"} is the least upper bound of 
      the set @{term "{u. f(u) \<le> u}"} *}

lemma lfp_lowerbound: "f A \<le> A ==> lfp f \<le> A"
  by (auto simp add: lfp_def intro: Meet_lower)

lemma lfp_greatest: "(!!u. f u \<le> u ==> A \<le> u) ==> A \<le> lfp f"
  by (auto simp add: lfp_def intro: Meet_greatest)

lemma lfp_lemma2: "mono f ==> f (lfp f) \<le> lfp f"
  by (iprover intro: lfp_greatest order_trans monoD lfp_lowerbound)

lemma lfp_lemma3: "mono f ==> lfp f \<le> f (lfp f)"
  by (iprover intro: lfp_lemma2 monoD lfp_lowerbound)

lemma lfp_unfold: "mono f ==> lfp f = f (lfp f)"
  by (iprover intro: order_antisym lfp_lemma2 lfp_lemma3)

subsection{*General induction rules for least fixed points*}

theorem lfp_induct:
  assumes mono: "mono f" and ind: "f (meet (lfp f) P) <= P"
  shows "lfp f <= P"
proof -
  have "meet (lfp f) P <= lfp f" by (rule meet_left_le)
  with mono have "f (meet (lfp f) P) <= f (lfp f)" ..
  also from mono have "f (lfp f) = lfp f" by (rule lfp_unfold [symmetric])
  finally have "f (meet (lfp f) P) <= lfp f" .
  from this and ind have "f (meet (lfp f) P) <= meet (lfp f) P" by (rule le_meetI)
  hence "lfp f <= meet (lfp f) P" by (rule lfp_lowerbound)
  also have "meet (lfp f) P <= P" by (rule meet_right_le)
  finally show ?thesis .
qed

lemma lfp_induct_set:
  assumes lfp: "a: lfp(f)"
      and mono: "mono(f)"
      and indhyp: "!!x. [| x: f(lfp(f) Int {x. P(x)}) |] ==> P(x)"
  shows "P(a)"
  by (rule lfp_induct [THEN subsetD, THEN CollectD, OF mono _ lfp])
    (auto simp: meet_set_eq intro: indhyp)


text{*Version of induction for binary relations*}
lemmas lfp_induct2 =  lfp_induct_set [of "(a,b)", split_format (complete)]


lemma lfp_ordinal_induct: 
  assumes mono: "mono f"
  shows "[| !!S. P S ==> P(f S); !!M. !S:M. P S ==> P(Union M) |] 
         ==> P(lfp f)"
apply(subgoal_tac "lfp f = Union{S. S \<subseteq> lfp f & P S}")
 apply (erule ssubst, simp) 
apply(subgoal_tac "Union{S. S \<subseteq> lfp f & P S} \<subseteq> lfp f")
 prefer 2 apply blast
apply(rule equalityI)
 prefer 2 apply assumption
apply(drule mono [THEN monoD])
apply (cut_tac mono [THEN lfp_unfold], simp)
apply (rule lfp_lowerbound, auto) 
done


text{*Definition forms of @{text lfp_unfold} and @{text lfp_induct}, 
    to control unfolding*}

lemma def_lfp_unfold: "[| h==lfp(f);  mono(f) |] ==> h = f(h)"
by (auto intro!: lfp_unfold)

lemma def_lfp_induct: 
    "[| A == lfp(f); mono(f);
        f (meet A P) \<le> P
     |] ==> A \<le> P"
  by (blast intro: lfp_induct)

lemma def_lfp_induct_set: 
    "[| A == lfp(f);  mono(f);   a:A;                    
        !!x. [| x: f(A Int {x. P(x)}) |] ==> P(x)         
     |] ==> P(a)"
  by (blast intro: lfp_induct_set)

(*Monotonicity of lfp!*)
lemma lfp_mono: "(!!Z. f Z \<le> g Z) ==> lfp f \<le> lfp g"
  by (rule lfp_lowerbound [THEN lfp_greatest], blast intro: order_trans)


subsection{*Proof of Knaster-Tarski Theorem using @{term gfp}*}


text{*@{term "gfp f"} is the greatest lower bound of 
      the set @{term "{u. u \<le> f(u)}"} *}

lemma gfp_upperbound: "X \<le> f X ==> X \<le> gfp f"
  by (auto simp add: gfp_def intro: Sup_upper)

lemma gfp_least: "(!!u. u \<le> f u ==> u \<le> X) ==> gfp f \<le> X"
  by (auto simp add: gfp_def intro: Sup_least)

lemma gfp_lemma2: "mono f ==> gfp f \<le> f (gfp f)"
  by (iprover intro: gfp_least order_trans monoD gfp_upperbound)

lemma gfp_lemma3: "mono f ==> f (gfp f) \<le> gfp f"
  by (iprover intro: gfp_lemma2 monoD gfp_upperbound)

lemma gfp_unfold: "mono f ==> gfp f = f (gfp f)"
  by (iprover intro: order_antisym gfp_lemma2 gfp_lemma3)

subsection{*Coinduction rules for greatest fixed points*}

text{*weak version*}
lemma weak_coinduct: "[| a: X;  X \<subseteq> f(X) |] ==> a : gfp(f)"
by (rule gfp_upperbound [THEN subsetD], auto)

lemma weak_coinduct_image: "!!X. [| a : X; g`X \<subseteq> f (g`X) |] ==> g a : gfp f"
apply (erule gfp_upperbound [THEN subsetD])
apply (erule imageI)
done

lemma coinduct_lemma:
     "[| X \<le> f (join X (gfp f));  mono f |] ==> join X (gfp f) \<le> f (join X (gfp f))"
  apply (frule gfp_lemma2)
  apply (drule mono_join)
  apply (rule join_leI)
  apply assumption
  apply (rule order_trans)
  apply (rule order_trans)
  apply assumption
  apply (rule join_right_le)
  apply assumption
  done

text{*strong version, thanks to Coen and Frost*}
lemma coinduct_set: "[| mono(f);  a: X;  X \<subseteq> f(X Un gfp(f)) |] ==> a : gfp(f)"
by (blast intro: weak_coinduct [OF _ coinduct_lemma, simplified join_set_eq])

lemma coinduct: "[| mono(f); X \<le> f (join X (gfp f)) |] ==> X \<le> gfp(f)"
  apply (rule order_trans)
  apply (rule join_left_le)
  apply (erule gfp_upperbound [OF coinduct_lemma])
  apply assumption
  done

lemma gfp_fun_UnI2: "[| mono(f);  a: gfp(f) |] ==> a: f(X Un gfp(f))"
by (blast dest: gfp_lemma2 mono_Un)

subsection{*Even Stronger Coinduction Rule, by Martin Coen*}

text{* Weakens the condition @{term "X \<subseteq> f(X)"} to one expressed using both
  @{term lfp} and @{term gfp}*}

lemma coinduct3_mono_lemma: "mono(f) ==> mono(%x. f(x) Un X Un B)"
by (iprover intro: subset_refl monoI Un_mono monoD)

lemma coinduct3_lemma:
     "[| X \<subseteq> f(lfp(%x. f(x) Un X Un gfp(f)));  mono(f) |]
      ==> lfp(%x. f(x) Un X Un gfp(f)) \<subseteq> f(lfp(%x. f(x) Un X Un gfp(f)))"
apply (rule subset_trans)
apply (erule coinduct3_mono_lemma [THEN lfp_lemma3])
apply (rule Un_least [THEN Un_least])
apply (rule subset_refl, assumption)
apply (rule gfp_unfold [THEN equalityD1, THEN subset_trans], assumption)
apply (rule monoD, assumption)
apply (subst coinduct3_mono_lemma [THEN lfp_unfold], auto)
done

lemma coinduct3: 
  "[| mono(f);  a:X;  X \<subseteq> f(lfp(%x. f(x) Un X Un gfp(f))) |] ==> a : gfp(f)"
apply (rule coinduct3_lemma [THEN [2] weak_coinduct])
apply (rule coinduct3_mono_lemma [THEN lfp_unfold, THEN ssubst], auto)
done


text{*Definition forms of @{text gfp_unfold} and @{text coinduct}, 
    to control unfolding*}

lemma def_gfp_unfold: "[| A==gfp(f);  mono(f) |] ==> A = f(A)"
by (auto intro!: gfp_unfold)

lemma def_coinduct:
     "[| A==gfp(f);  mono(f);  X \<le> f(join X A) |] ==> X \<le> A"
by (iprover intro!: coinduct)

lemma def_coinduct_set:
     "[| A==gfp(f);  mono(f);  a:X;  X \<subseteq> f(X Un A) |] ==> a: A"
by (auto intro!: coinduct_set)

(*The version used in the induction/coinduction package*)
lemma def_Collect_coinduct:
    "[| A == gfp(%w. Collect(P(w)));  mono(%w. Collect(P(w)));   
        a: X;  !!z. z: X ==> P (X Un A) z |] ==>  
     a : A"
apply (erule def_coinduct_set, auto) 
done

lemma def_coinduct3:
    "[| A==gfp(f); mono(f);  a:X;  X \<subseteq> f(lfp(%x. f(x) Un X Un A)) |] ==> a: A"
by (auto intro!: coinduct3)

text{*Monotonicity of @{term gfp}!*}
lemma gfp_mono: "(!!Z. f Z \<le> g Z) ==> gfp f \<le> gfp g"
  by (rule gfp_upperbound [THEN gfp_least], blast intro: order_trans)



ML
{*
val lfp_def = thm "lfp_def";
val lfp_lowerbound = thm "lfp_lowerbound";
val lfp_greatest = thm "lfp_greatest";
val lfp_unfold = thm "lfp_unfold";
val lfp_induct = thm "lfp_induct";
val lfp_induct2 = thm "lfp_induct2";
val lfp_ordinal_induct = thm "lfp_ordinal_induct";
val def_lfp_unfold = thm "def_lfp_unfold";
val def_lfp_induct = thm "def_lfp_induct";
val def_lfp_induct_set = thm "def_lfp_induct_set";
val lfp_mono = thm "lfp_mono";
val gfp_def = thm "gfp_def";
val gfp_upperbound = thm "gfp_upperbound";
val gfp_least = thm "gfp_least";
val gfp_unfold = thm "gfp_unfold";
val weak_coinduct = thm "weak_coinduct";
val weak_coinduct_image = thm "weak_coinduct_image";
val coinduct = thm "coinduct";
val gfp_fun_UnI2 = thm "gfp_fun_UnI2";
val coinduct3 = thm "coinduct3";
val def_gfp_unfold = thm "def_gfp_unfold";
val def_coinduct = thm "def_coinduct";
val def_Collect_coinduct = thm "def_Collect_coinduct";
val def_coinduct3 = thm "def_coinduct3";
val gfp_mono = thm "gfp_mono";
val le_funI = thm "le_funI";
val le_boolI = thm "le_boolI";
val le_boolI' = thm "le_boolI'";
val meet_fun_eq = thm "meet_fun_eq";
val meet_bool_eq = thm "meet_bool_eq";
val le_funE = thm "le_funE";
val le_funD = thm "le_funD";
val le_boolE = thm "le_boolE";
val le_boolD = thm "le_boolD";
val le_bool_def = thm "le_bool_def";
val le_fun_def = thm "le_fun_def";
*}

end
