(* Author: Tobias Nipkow *)

subsection "Computable State"

theory Abs_State
imports Abs_Int0
begin

type_synonym 'a st_rep = "(vname * 'a) list"

fun fun_rep :: "('a::top) st_rep \<Rightarrow> vname \<Rightarrow> 'a" where
"fun_rep [] = (\<lambda>x. \<top>)" |
"fun_rep ((x,a)#ps) = (fun_rep ps) (x := a)"

lemma fun_rep_map_of[code]: \<comment> \<open>original def is too slow\<close>
  "fun_rep ps = (%x. case map_of ps x of None \<Rightarrow> \<top> | Some a \<Rightarrow> a)"
by(induction ps rule: fun_rep.induct) auto

definition eq_st :: "('a::top) st_rep \<Rightarrow> 'a st_rep \<Rightarrow> bool" where
"eq_st S1 S2 = (fun_rep S1 = fun_rep S2)"

hide_type st  \<comment> \<open>hide previous def to avoid long names\<close>
declare [[typedef_overloaded]] \<comment> \<open>allow quotient types to depend on classes\<close>

quotient_type 'a st = "('a::top) st_rep" / eq_st
morphisms rep_st St
by (metis eq_st_def equivpI reflpI sympI transpI)

lift_definition update :: "('a::top) st \<Rightarrow> vname \<Rightarrow> 'a \<Rightarrow> 'a st"
  is "\<lambda>ps x a. (x,a)#ps"
by(auto simp: eq_st_def)

lift_definition "fun" :: "('a::top) st \<Rightarrow> vname \<Rightarrow> 'a" is fun_rep
by(simp add: eq_st_def)

definition show_st :: "vname set \<Rightarrow> ('a::top) st \<Rightarrow> (vname * 'a)set" where
"show_st X S = (\<lambda>x. (x, fun S x)) ` X"

definition "show_acom C = map_acom (map_option (show_st (vars(strip C)))) C"
definition "show_acom_opt = map_option show_acom"

lemma fun_update[simp]: "fun (update S x y) = (fun S)(x:=y)"
by transfer auto

definition \<gamma>_st :: "(('a::top) \<Rightarrow> 'b set) \<Rightarrow> 'a st \<Rightarrow> (vname \<Rightarrow> 'b) set" where
"\<gamma>_st \<gamma> F = {f. \<forall>x. f x \<in> \<gamma>(fun F x)}"

instantiation st :: (order_top) order
begin

definition less_eq_st_rep :: "'a st_rep \<Rightarrow> 'a st_rep \<Rightarrow> bool" where
"less_eq_st_rep ps1 ps2 =
  ((\<forall>x \<in> set(map fst ps1) \<union> set(map fst ps2). fun_rep ps1 x \<le> fun_rep ps2 x))"

lemma less_eq_st_rep_iff:
  "less_eq_st_rep r1 r2 = (\<forall>x. fun_rep r1 x \<le> fun_rep r2 x)"
apply(auto simp: less_eq_st_rep_def fun_rep_map_of split: option.split)
apply (metis Un_iff map_of_eq_None_iff option.distinct(1))
apply (metis Un_iff map_of_eq_None_iff option.distinct(1))
done

corollary less_eq_st_rep_iff_fun:
  "less_eq_st_rep r1 r2 = (fun_rep r1 \<le> fun_rep r2)"
by (metis less_eq_st_rep_iff le_fun_def)

lift_definition less_eq_st :: "'a st \<Rightarrow> 'a st \<Rightarrow> bool" is less_eq_st_rep
by(auto simp add: eq_st_def less_eq_st_rep_iff)

definition less_st where "F < (G::'a st) = (F \<le> G \<and> \<not> G \<le> F)"

instance
proof (standard, goal_cases)
  case 1 show ?case by(rule less_st_def)
next
  case 2 show ?case by transfer (auto simp: less_eq_st_rep_def)
next
  case 3 thus ?case by transfer (metis less_eq_st_rep_iff order_trans)
next
  case 4 thus ?case
    by transfer (metis less_eq_st_rep_iff eq_st_def fun_eq_iff antisym)
qed

end

lemma le_st_iff: "(F \<le> G) = (\<forall>x. fun F x \<le> fun G x)"
by transfer (rule less_eq_st_rep_iff)

fun map2_st_rep :: "('a::top \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a st_rep \<Rightarrow> 'a st_rep \<Rightarrow> 'a st_rep" where
"map2_st_rep f [] ps2 = map (%(x,y). (x, f \<top> y)) ps2" |
"map2_st_rep f ((x,y)#ps1) ps2 =
  (let y2 = fun_rep ps2 x
   in (x,f y y2) # map2_st_rep f ps1 ps2)"

lemma fun_rep_map2_rep[simp]: "f \<top> \<top> = \<top> \<Longrightarrow>
  fun_rep (map2_st_rep f ps1 ps2) = (\<lambda>x. f (fun_rep ps1 x) (fun_rep ps2 x))"
apply(induction f ps1 ps2 rule: map2_st_rep.induct)
apply(simp add: fun_rep_map_of map_of_map fun_eq_iff split: option.split)
apply(fastforce simp: fun_rep_map_of fun_eq_iff split:option.splits)
done

instantiation st :: (semilattice_sup_top) semilattice_sup_top
begin

lift_definition sup_st :: "'a st \<Rightarrow> 'a st \<Rightarrow> 'a st" is "map2_st_rep (\<squnion>)"
by (simp add: eq_st_def)

lift_definition top_st :: "'a st" is "[]" .

instance
proof (standard, goal_cases)
  case 1 show ?case by transfer (simp add:less_eq_st_rep_iff)
next
  case 2 show ?case by transfer (simp add:less_eq_st_rep_iff)
next
  case 3 thus ?case by transfer (simp add:less_eq_st_rep_iff)
next
  case 4 show ?case by transfer (simp add:less_eq_st_rep_iff fun_rep_map_of)
qed

end

lemma fun_top: "fun \<top> = (\<lambda>x. \<top>)"
by transfer simp

lemma mono_update[simp]:
  "a1 \<le> a2 \<Longrightarrow> S1 \<le> S2 \<Longrightarrow> update S1 x a1 \<le> update S2 x a2"
by transfer (auto simp add: less_eq_st_rep_def)

lemma mono_fun: "S1 \<le> S2 \<Longrightarrow> fun S1 x \<le> fun S2 x"
by transfer (simp add: less_eq_st_rep_iff)

locale Gamma_semilattice = Val_semilattice where \<gamma>=\<gamma>
  for \<gamma> :: "'av::semilattice_sup_top \<Rightarrow> val set"
begin

abbreviation \<gamma>\<^sub>s :: "'av st \<Rightarrow> state set"
where "\<gamma>\<^sub>s == \<gamma>_st \<gamma>"

abbreviation \<gamma>\<^sub>o :: "'av st option \<Rightarrow> state set"
where "\<gamma>\<^sub>o == \<gamma>_option \<gamma>\<^sub>s"

abbreviation \<gamma>\<^sub>c :: "'av st option acom \<Rightarrow> state set acom"
where "\<gamma>\<^sub>c == map_acom \<gamma>\<^sub>o"

lemma gamma_s_top[simp]: "\<gamma>\<^sub>s \<top> = UNIV"
by(auto simp: \<gamma>_st_def fun_top)

lemma gamma_o_Top[simp]: "\<gamma>\<^sub>o \<top> = UNIV"
by (simp add: top_option_def)

lemma mono_gamma_s: "f \<le> g \<Longrightarrow> \<gamma>\<^sub>s f \<subseteq> \<gamma>\<^sub>s g"
by(simp add:\<gamma>_st_def le_st_iff subset_iff) (metis mono_gamma subsetD)

lemma mono_gamma_o:
  "S1 \<le> S2 \<Longrightarrow> \<gamma>\<^sub>o S1 \<subseteq> \<gamma>\<^sub>o S2"
by(induction S1 S2 rule: less_eq_option.induct)(simp_all add: mono_gamma_s)

lemma mono_gamma_c: "C1 \<le> C2 \<Longrightarrow> \<gamma>\<^sub>c C1 \<le> \<gamma>\<^sub>c C2"
by (simp add: less_eq_acom_def mono_gamma_o size_annos anno_map_acom size_annos_same[of C1 C2])

lemma in_gamma_option_iff:
  "x \<in> \<gamma>_option r u \<longleftrightarrow> (\<exists>u'. u = Some u' \<and> x \<in> r u')"
by (cases u) auto

end

end
