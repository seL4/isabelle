(*  Title:      HOL/FixedPoint.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Author:     Stefan Berghofer, TU Muenchen
    Copyright   1992  University of Cambridge
*)

header {* Fixed Points and the Knaster-Tarski Theorem*}

theory FixedPoint
imports Product_Type
begin

subsection {* Complete lattices *}

class complete_lattice = lattice +
  fixes Inf :: "'a set \<Rightarrow> 'a"
  assumes Inf_lower: "x \<in> A \<Longrightarrow> Inf A \<sqsubseteq> x"
  assumes Inf_greatest: "(\<And>x. x \<in> A \<Longrightarrow> z \<sqsubseteq> x) \<Longrightarrow> z \<sqsubseteq> Inf A"

definition
  Sup :: "'a\<Colon>complete_lattice set \<Rightarrow> 'a" where
  "Sup A = Inf {b. \<forall>a \<in> A. a \<le> b}"

theorem Sup_upper: "(x::'a::complete_lattice) \<in> A \<Longrightarrow> x <= Sup A"
  by (auto simp: Sup_def intro: Inf_greatest)

theorem Sup_least: "(\<And>x::'a::complete_lattice. x \<in> A \<Longrightarrow> x <= z) \<Longrightarrow> Sup A <= z"
  by (auto simp: Sup_def intro: Inf_lower)

definition
  SUPR :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b::complete_lattice) \<Rightarrow> 'b" where
  "SUPR A f == Sup (f ` A)"

definition
  INFI :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b::complete_lattice) \<Rightarrow> 'b" where
  "INFI A f == Inf (f ` A)"

syntax
  "_SUP1"     :: "pttrns => 'b => 'b"           ("(3SUP _./ _)" [0, 10] 10)
  "_SUP"      :: "pttrn => 'a set => 'b => 'b"  ("(3SUP _:_./ _)" [0, 10] 10)
  "_INF1"     :: "pttrns => 'b => 'b"           ("(3INF _./ _)" [0, 10] 10)
  "_INF"      :: "pttrn => 'a set => 'b => 'b"  ("(3INF _:_./ _)" [0, 10] 10)

translations
  "SUP x y. B"   == "SUP x. SUP y. B"
  "SUP x. B"     == "CONST SUPR UNIV (%x. B)"
  "SUP x. B"     == "SUP x:UNIV. B"
  "SUP x:A. B"   == "CONST SUPR A (%x. B)"
  "INF x y. B"   == "INF x. INF y. B"
  "INF x. B"     == "CONST INFI UNIV (%x. B)"
  "INF x. B"     == "INF x:UNIV. B"
  "INF x:A. B"   == "CONST INFI A (%x. B)"

(* To avoid eta-contraction of body: *)
print_translation {*
let
  fun btr' syn (A :: Abs abs :: ts) =
    let val (x,t) = atomic_abs_tr' abs
    in list_comb (Syntax.const syn $ x $ A $ t, ts) end
  val const_syntax_name = Sign.const_syntax_name @{theory} o fst o dest_Const
in
[(const_syntax_name @{term SUPR}, btr' "_SUP"),(const_syntax_name @{term "INFI"}, btr' "_INF")]
end
*}

lemma le_SUPI: "i : A \<Longrightarrow> M i \<le> (SUP i:A. M i)"
  by (auto simp add: SUPR_def intro: Sup_upper)

lemma SUP_leI: "(\<And>i. i : A \<Longrightarrow> M i \<le> u) \<Longrightarrow> (SUP i:A. M i) \<le> u"
  by (auto simp add: SUPR_def intro: Sup_least)

lemma INF_leI: "i : A \<Longrightarrow> (INF i:A. M i) \<le> M i"
  by (auto simp add: INFI_def intro: Inf_lower)

lemma le_INFI: "(\<And>i. i : A \<Longrightarrow> u \<le> M i) \<Longrightarrow> u \<le> (INF i:A. M i)"
  by (auto simp add: INFI_def intro: Inf_greatest)

text {* A complete lattice is a lattice *}


subsubsection {* Properties *}

lemma mono_inf: "mono f \<Longrightarrow> f (inf A B) <= inf (f A) (f B)"
  by (auto simp add: mono_def)

lemma mono_sup: "mono f \<Longrightarrow> sup (f A) (f B) <= f (sup A B)"
  by (auto simp add: mono_def)

lemma Sup_insert[simp]: "Sup (insert (a::'a::complete_lattice) A) = sup a (Sup A)"
  apply (rule order_antisym)
  apply (rule Sup_least)
  apply (erule insertE)
  apply (rule le_supI1)
  apply simp
  apply (rule le_supI2)
  apply (erule Sup_upper)
  apply (rule le_supI)
  apply (rule Sup_upper)
  apply simp
  apply (rule Sup_least)
  apply (rule Sup_upper)
  apply simp
  done

lemma Inf_insert[simp]: "Inf (insert (a::'a::complete_lattice) A) = inf a (Inf A)"
  apply (rule order_antisym)
  apply (rule le_infI)
  apply (rule Inf_lower)
  apply simp
  apply (rule Inf_greatest)
  apply (rule Inf_lower)
  apply simp
  apply (rule Inf_greatest)
  apply (erule insertE)
  apply (rule le_infI1)
  apply simp
  apply (rule le_infI2)
  apply (erule Inf_lower)
  done

lemma bot_least[simp]: "Sup{} \<le> (x::'a::complete_lattice)"
  by (rule Sup_least) simp

lemma top_greatest[simp]: "(x::'a::complete_lattice) \<le> Inf{}"
  by (rule Inf_greatest) simp

lemma SUP_const[simp]: "A \<noteq> {} \<Longrightarrow> (SUP i:A. M) = M"
  by (auto intro: order_antisym SUP_leI le_SUPI)

lemma INF_const[simp]: "A \<noteq> {} \<Longrightarrow> (INF i:A. M) = M"
  by (auto intro: order_antisym INF_leI le_INFI)


subsection {* Some instances of the type class of complete lattices *}

subsubsection {* Booleans *}

instance bool :: complete_lattice
  Inf_bool_def: "Inf A \<equiv> \<forall>x\<in>A. x"
  apply intro_classes
  apply (unfold Inf_bool_def)
  apply (iprover intro!: le_boolI elim: ballE)
  apply (iprover intro!: ballI le_boolI elim: ballE le_boolE)
  done

theorem Sup_bool_eq: "Sup A \<longleftrightarrow> (\<exists>x\<in>A. x)"
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

instance "fun" :: (type, complete_lattice) complete_lattice
  Inf_fun_def: "Inf A \<equiv> (\<lambda>x. Inf {y. \<exists>f\<in>A. y = f x})"
  apply intro_classes
  apply (unfold Inf_fun_def)
  apply (rule le_funI)
  apply (rule Inf_lower)
  apply (rule CollectI)
  apply (rule bexI)
  apply (rule refl)
  apply assumption
  apply (rule le_funI)
  apply (rule Inf_greatest)
  apply (erule CollectE)
  apply (erule bexE)
  apply (iprover elim: le_funE)
  done

theorem Sup_fun_eq: "Sup A = (\<lambda>x. Sup {y. \<exists>f\<in>A. y = f x})"
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

instance set :: (type) complete_lattice
  Inf_set_def: "Inf S \<equiv> \<Inter>S"
  by intro_classes (auto simp add: Inf_set_def)

theorem Sup_set_eq: "Sup S = \<Union>S"
  apply (rule subset_antisym)
  apply (rule Sup_least)
  apply (erule Union_upper)
  apply (rule Union_least)
  apply (erule Sup_upper)
  done


subsection {* Least and greatest fixed points *}

definition
  lfp :: "('a\<Colon>complete_lattice \<Rightarrow> 'a) \<Rightarrow> 'a" where
  "lfp f = Inf {u. f u \<le> u}"    --{*least fixed point*}

definition
  gfp :: "('a\<Colon>complete_lattice \<Rightarrow> 'a) \<Rightarrow> 'a" where
  "gfp f = Sup {u. u \<le> f u}"    --{*greatest fixed point*}


subsection{*Proof of Knaster-Tarski Theorem using @{term lfp}*}

text{*@{term "lfp f"} is the least upper bound of 
      the set @{term "{u. f(u) \<le> u}"} *}

lemma lfp_lowerbound: "f A \<le> A ==> lfp f \<le> A"
  by (auto simp add: lfp_def intro: Inf_lower)

lemma lfp_greatest: "(!!u. f u \<le> u ==> A \<le> u) ==> A \<le> lfp f"
  by (auto simp add: lfp_def intro: Inf_greatest)

lemma lfp_lemma2: "mono f ==> f (lfp f) \<le> lfp f"
  by (iprover intro: lfp_greatest order_trans monoD lfp_lowerbound)

lemma lfp_lemma3: "mono f ==> lfp f \<le> f (lfp f)"
  by (iprover intro: lfp_lemma2 monoD lfp_lowerbound)

lemma lfp_unfold: "mono f ==> lfp f = f (lfp f)"
  by (iprover intro: order_antisym lfp_lemma2 lfp_lemma3)

lemma lfp_const: "lfp (\<lambda>x. t) = t"
  by (rule lfp_unfold) (simp add:mono_def)

subsection{*General induction rules for least fixed points*}

theorem lfp_induct:
  assumes mono: "mono f" and ind: "f (inf (lfp f) P) <= P"
  shows "lfp f <= P"
proof -
  have "inf (lfp f) P <= lfp f" by (rule inf_le1)
  with mono have "f (inf (lfp f) P) <= f (lfp f)" ..
  also from mono have "f (lfp f) = lfp f" by (rule lfp_unfold [symmetric])
  finally have "f (inf (lfp f) P) <= lfp f" .
  from this and ind have "f (inf (lfp f) P) <= inf (lfp f) P" by (rule le_infI)
  hence "lfp f <= inf (lfp f) P" by (rule lfp_lowerbound)
  also have "inf (lfp f) P <= P" by (rule inf_le2)
  finally show ?thesis .
qed

lemma lfp_induct_set:
  assumes lfp: "a: lfp(f)"
      and mono: "mono(f)"
      and indhyp: "!!x. [| x: f(lfp(f) Int {x. P(x)}) |] ==> P(x)"
  shows "P(a)"
  by (rule lfp_induct [THEN subsetD, THEN CollectD, OF mono _ lfp])
    (auto simp: inf_set_eq intro: indhyp)

text {* Version of induction for binary relations *}
lemmas lfp_induct2 =  lfp_induct_set [of "(a, b)", split_format (complete)]

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
        f (inf A P) \<le> P
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
     "[| X \<le> f (sup X (gfp f));  mono f |] ==> sup X (gfp f) \<le> f (sup X (gfp f))"
  apply (frule gfp_lemma2)
  apply (drule mono_sup)
  apply (rule le_supI)
  apply assumption
  apply (rule order_trans)
  apply (rule order_trans)
  apply assumption
  apply (rule sup_ge2)
  apply assumption
  done

text{*strong version, thanks to Coen and Frost*}
lemma coinduct_set: "[| mono(f);  a: X;  X \<subseteq> f(X Un gfp(f)) |] ==> a : gfp(f)"
by (blast intro: weak_coinduct [OF _ coinduct_lemma, simplified sup_set_eq])

lemma coinduct: "[| mono(f); X \<le> f (sup X (gfp f)) |] ==> X \<le> gfp(f)"
  apply (rule order_trans)
  apply (rule sup_ge1)
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
     "[| A==gfp(f);  mono(f);  X \<le> f(sup X A) |] ==> X \<le> A"
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
val inf_fun_eq = thm "inf_fun_eq";
val inf_bool_eq = thm "inf_bool_eq";
val le_funE = thm "le_funE";
val le_funD = thm "le_funD";
val le_boolE = thm "le_boolE";
val le_boolD = thm "le_boolD";
val le_bool_def = thm "le_bool_def";
val le_fun_def = thm "le_fun_def";
*}

end
