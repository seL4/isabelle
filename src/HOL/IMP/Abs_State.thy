(* Author: Tobias Nipkow *)

theory Abs_State
imports Abs_Int0
begin

subsubsection "Set-based lattices"


class L =
fixes L :: "vname set \<Rightarrow> 'a set"


instantiation acom :: (L)L
begin

definition L_acom where
"L X = {C. vars(strip C) \<subseteq> X \<and> (\<forall>a \<in> set(annos C). a \<in> L X)}"

instance ..

end


instantiation option :: (L)L
begin

definition L_option where
"L X = {opt. case opt of None \<Rightarrow> True | Some x \<Rightarrow> x \<in> L X}"

lemma L_option_simps[simp]: "None \<in> L X" "(Some x \<in> L X) = (x \<in> L X)"
by(simp_all add: L_option_def)

instance ..

end

class semilatticeL = order + sup + L +
fixes Top :: "vname set \<Rightarrow> 'a"
assumes sup_ge1 [simp]: "x \<in> L X \<Longrightarrow> y \<in> L X \<Longrightarrow> x \<le> x \<squnion> y"
and sup_ge2 [simp]: "x \<in> L X \<Longrightarrow> y \<in> L X \<Longrightarrow> y \<le> x \<squnion> y"
and sup_least[simp]: "x \<le> z \<Longrightarrow> y \<le> z \<Longrightarrow> x \<squnion> y \<le> z"
and Top[simp]: "x \<in> L X \<Longrightarrow> x \<le> Top X"
and Top_in_L[simp]: "Top X \<in> L X"
and sup_in_L[simp]: "x \<in> L X \<Longrightarrow> y \<in> L X \<Longrightarrow> x \<squnion> y \<in> L X"

notation (input) Top ("\<top>\<^bsub>_\<^esub>")
notation (latex output) Top ("\<top>\<^bsub>\<^raw:\isa{>_\<^raw:}>\<^esub>")

instantiation option :: (semilatticeL)semilatticeL
begin

definition Top_option where "Top c = Some(Top c)"

instance proof
  case goal1 thus ?case by(cases x, simp, cases y, simp_all)
next
  case goal2 thus ?case by(cases y, simp, cases x, simp_all)
next
  case goal3 thus ?case by(cases z, simp, cases y, simp, cases x, simp_all)
next
  case goal4 thus ?case by(cases x, simp_all add: Top_option_def)
next
  case goal5 thus ?case by(simp add: Top_option_def)
next
  case goal6 thus ?case by(simp add: L_option_def split: option.splits)
qed

end


subsection "Abstract State with Computable Ordering"

hide_type  st  --"to avoid long names"

text{* A concrete type of state with computable @{text"\<le>"}: *}

fun st :: "(vname \<Rightarrow> 'a) * vname set \<Rightarrow> bool" where
"st (f,X) = (\<forall>x. x \<notin> X \<longrightarrow> f x = undefined)"

typedef 'a st = "{p :: (vname \<Rightarrow> 'a) * vname set. st p}"
proof
  show "(\<lambda>x. undefined,{}) \<in> {p. st p}" by simp
qed

setup_lifting type_definition_st

lift_definition St :: "(vname \<Rightarrow> 'a) \<Rightarrow> vname set \<Rightarrow> 'a st" is
  "\<lambda>f X. (\<lambda>x. if x \<in> X then f x else undefined, X)"
by(simp)

lift_definition update :: "'a st \<Rightarrow> vname \<Rightarrow> 'a \<Rightarrow> 'a st" is
  "\<lambda>(f,X) x a. (f(x := a), insert x X)"
by(auto)

lift_definition "fun" :: "'a st \<Rightarrow> vname \<Rightarrow> 'a" is fst ..

lift_definition dom :: "'a st \<Rightarrow> vname set" is snd ..

lemma dom_St[simp]: "dom(St f X) = X"
by(simp add: St.rep_eq dom.rep_eq)

lemma fun_St[simp]: "fun(St f X) = (\<lambda>x. if x \<in> X then f x else undefined)"
by(simp add: St.rep_eq fun.rep_eq)

definition show_st :: "'a st \<Rightarrow> (vname * 'a)set" where
"show_st S = (\<lambda>x. (x, fun S x)) ` dom S"

definition "show_acom = map_acom (Option.map show_st)"
definition "show_acom_opt = Option.map show_acom"

lemma fun_update[simp]: "fun (update S x y) = (fun S)(x:=y)"
by transfer auto

lemma dom_update[simp]: "dom (update S x y) = insert x (dom S)"
by transfer auto

definition \<gamma>_st :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'a st \<Rightarrow> (vname \<Rightarrow> 'b) set" where
"\<gamma>_st \<gamma> F = {f. \<forall>x\<in>dom  F. f x \<in> \<gamma>(fun F x)}"

lemma ext_st: "dom F = dom G \<Longrightarrow> \<forall>x \<in> dom G. fun F x = fun G x \<Longrightarrow> F=G"
apply(induct F rule:Abs_st_induct)
apply(induct G rule:Abs_st_induct)
apply (auto simp:Abs_st_inject fun_def dom_def Abs_st_inverse simp del: st.simps)
apply(rule ext)
apply auto
done

instantiation st :: (order) order
begin

definition less_eq_st :: "'a st \<Rightarrow> 'a st \<Rightarrow> bool" where
"F \<le> (G::'a st) = (dom F = dom G \<and> (\<forall>x \<in> dom F. fun F x \<le> fun G x))"

definition less_st where "F < (G::'a st) = (F \<le> G \<and> \<not> G \<le> F)"

instance
proof
  case goal1 show ?case by(rule less_st_def)
next
  case goal2 show ?case by(auto simp: less_eq_st_def)
next
  case goal3 thus ?case by(fastforce simp: less_eq_st_def)
next
  case goal4 thus ?case by (metis less_eq_st_def antisym ext_st)
qed

end

instantiation st :: (sup) sup
begin

definition sup_st :: "'a st \<Rightarrow> 'a st \<Rightarrow> 'a st" where
"F \<squnion> (G::'a st) = St (\<lambda>x. fun F x \<squnion> fun G x) (dom F)"

instance ..

end

instantiation st :: (type) L
begin

definition L_st :: "vname set \<Rightarrow> 'a st set" where
"L(X::vname set) = {F. dom F = X}"

instance ..

end

instantiation st :: (semilattice) semilatticeL
begin

definition Top_st :: "vname set \<Rightarrow> 'a st" where "Top(X) = St (\<lambda>x. \<top>) X"

instance
proof qed(auto simp add: less_eq_st_def sup_st_def Top_st_def L_st_def)

end


text{* Trick to make code generator happy. *}
lemma [code]: "L = (L :: _ \<Rightarrow> _ st set)"
by(rule refl)
(* L is not used in the code but is part of a type class that is used.
   Hence the code generator wants to build a dictionary with L in it.
   But L is not executable. This looping defn makes it look as if it were. *)


lemma mono_fun: "F \<le> G \<Longrightarrow> x : dom F \<Longrightarrow> fun F x \<le> fun G x"
by(auto simp: less_eq_st_def)

lemma mono_update[simp]:
  "a1 \<le> a2 \<Longrightarrow> S1 \<le> S2 \<Longrightarrow> update S1 x a1 \<le> update S2 x a2"
by(auto simp add: less_eq_st_def)


locale Gamma = Val_abs where \<gamma>=\<gamma> for \<gamma> :: "'av::semilattice \<Rightarrow> val set"
begin

abbreviation \<gamma>\<^isub>s :: "'av st \<Rightarrow> state set"
where "\<gamma>\<^isub>s == \<gamma>_st \<gamma>"

abbreviation \<gamma>\<^isub>o :: "'av st option \<Rightarrow> state set"
where "\<gamma>\<^isub>o == \<gamma>_option \<gamma>\<^isub>s"

abbreviation \<gamma>\<^isub>c :: "'av st option acom \<Rightarrow> state set acom"
where "\<gamma>\<^isub>c == map_acom \<gamma>\<^isub>o"

lemma gamma_s_Top[simp]: "\<gamma>\<^isub>s (Top X) = UNIV"
by(auto simp: Top_st_def \<gamma>_st_def)

lemma gamma_o_Top[simp]: "\<gamma>\<^isub>o (Top X) = UNIV"
by (simp add: Top_option_def)

lemma mono_gamma_s: "f \<le> g \<Longrightarrow> \<gamma>\<^isub>s f \<subseteq> \<gamma>\<^isub>s g"
apply(simp add:\<gamma>_st_def subset_iff less_eq_st_def split: if_splits)
by (metis mono_gamma subsetD)

lemma mono_gamma_o:
  "S1 \<le> S2 \<Longrightarrow> \<gamma>\<^isub>o S1 \<subseteq> \<gamma>\<^isub>o S2"
by(induction S1 S2 rule: less_eq_option.induct)(simp_all add: mono_gamma_s)

lemma mono_gamma_c: "C1 \<le> C2 \<Longrightarrow> \<gamma>\<^isub>c C1 \<le> \<gamma>\<^isub>c C2"
by (induction C1 C2 rule: less_eq_acom.induct) (simp_all add:mono_gamma_o)

lemma in_gamma_option_iff:
  "x : \<gamma>_option r u \<longleftrightarrow> (\<exists>u'. u = Some u' \<and> x : r u')"
by (cases u) auto

end

end
