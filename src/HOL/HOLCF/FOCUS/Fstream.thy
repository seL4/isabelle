(*  Title:      HOL/HOLCF/FOCUS/Fstream.thy
    Author:     David von Oheimb, TU Muenchen

FOCUS streams (with lifted elements).

TODO: integrate Fstreams.thy
*)

section \<open>FOCUS flat streams\<close>

theory Fstream
imports "HOLCF-Library.Stream"
begin

default_sort type

type_synonym 'a fstream = "'a lift stream"

definition
  fscons        :: "'a     \<Rightarrow> 'a fstream \<rightarrow> 'a fstream" where
  "fscons a = (\<Lambda> s. Def a && s)"

definition
  fsfilter      :: "'a set \<Rightarrow> 'a fstream \<rightarrow> 'a fstream" where
  "fsfilter A = (sfilter\<cdot>(flift2 (\<lambda>x. x\<in>A)))"

abbreviation
  emptystream   :: "'a fstream"                          (\<open><>\<close>) where
  "<> == \<bottom>"

abbreviation
  fscons'       :: "'a \<Rightarrow> 'a fstream \<Rightarrow> 'a fstream"       (\<open>(\<open>notation=\<open>infix \<leadsto>\<close>\<close>_\<leadsto>_)\<close> [66,65] 65) where
  "a\<leadsto>s == fscons a\<cdot>s"

abbreviation
  fsfilter'     :: "'a set \<Rightarrow> 'a fstream \<Rightarrow> 'a fstream"   (\<open>(\<open>notation=\<open>infix \<copyright>\<close>\<close>_\<copyright>_)\<close> [64,63] 63) where
  "A\<copyright>s == fsfilter A\<cdot>s"

notation (ASCII)
  fscons'  (\<open>(\<open>notation=\<open>infix ~>\<close>\<close>_~>_)\<close> [66,65] 65) and
  fsfilter'  (\<open>(\<open>notation=\<open>infix (C)\<close>\<close>_'(C')_)\<close> [64,63] 63)


lemma Def_maximal: "a = Def d \<Longrightarrow> a\<sqsubseteq>b \<Longrightarrow> b = Def d"
by simp


section "fscons"

lemma fscons_def2: "a~>s = Def a && s"
apply (unfold fscons_def)
apply (simp)
done

lemma fstream_exhaust: "x = UU \<or> (\<exists>a y. x = a~> y)"
apply (simp add: fscons_def2)
apply (cut_tac stream.nchotomy)
apply (fast dest: not_Undef_is_Def [THEN iffD1])
done

lemma fstream_cases: "[| x = UU ==> P; !!a y. x = a~> y ==> P |] ==> P"
apply (cut_tac fstream_exhaust)
apply (erule disjE)
apply fast
apply fast
done

lemma fstream_exhaust_eq: "(x \<noteq> UU) = (\<exists>a y. x = a~> y)"
apply (simp add: fscons_def2 stream_exhaust_eq)
apply (fast dest: not_Undef_is_Def [THEN iffD1] elim: DefE)
done


lemma fscons_not_empty [simp]: "a~> s \<noteq> <>"
by (simp add: fscons_def2)


lemma fscons_inject [simp]: "(a~> s = b~> t) = (a = b \<and> s = t)"
by (simp add: fscons_def2)

lemma fstream_prefix: "a~> s << t ==> \<exists>tt. t = a~> tt \<and> s << tt"
apply (cases t)
apply (cut_tac fscons_not_empty)
apply (fast dest: bottomI)
apply (simp add: fscons_def2)
done

lemma fstream_prefix' [simp]:
        "x << a~> z = (x = <> \<or> (\<exists>y. x = a~> y \<and> y << z))"
apply (simp add: fscons_def2 lift.distinct(2) [THEN stream_prefix'])
apply (safe)
apply (erule_tac [!] contrapos_np)
prefer 2 apply (fast elim: DefE)
apply (rule lift.exhaust)
apply (erule (1) notE)
apply (safe)
apply (drule Def_below_Def [THEN iffD1])
apply fast
done

(* ------------------------------------------------------------------------- *)

section "ft & rt"

lemmas ft_empty = stream.sel_rews (1)
lemma ft_fscons [simp]: "ft\<cdot>(m~> s) = Def m"
by (simp add: fscons_def)

lemmas rt_empty = stream.sel_rews (2)
lemma rt_fscons [simp]: "rt\<cdot>(m~> s) = s"
by (simp add: fscons_def)

lemma ft_eq [simp]: "(ft\<cdot>s = Def a) = (\<exists>t. s = a~> t)"
apply (unfold fscons_def)
apply (simp)
apply (safe)
apply (erule subst)
apply (rule exI)
apply (rule surjectiv_scons [symmetric])
apply (simp)
done

lemma surjective_fscons_lemma: "(d\<leadsto>y = x) = (ft\<cdot>x = Def d & rt\<cdot>x = y)"
by auto

lemma surjective_fscons: "ft\<cdot>x = Def d \<Longrightarrow> d\<leadsto>rt\<cdot>x = x"
by (simp add: surjective_fscons_lemma)


(* ------------------------------------------------------------------------- *)

section "take"

lemma fstream_take_Suc [simp]:
        "stream_take (Suc n)\<cdot>(a~> s) = a~> stream_take n\<cdot>s"
by (simp add: fscons_def)


(* ------------------------------------------------------------------------- *)

section "slen"

lemma slen_fscons: "#(m~> s) = eSuc (#s)"
by (simp add: fscons_def)

lemma slen_fscons_eq:
        "(enat (Suc n) < #x) = (\<exists>a y. x = a~> y \<and> enat n < #y)"
apply (simp add: fscons_def2 slen_scons_eq)
apply (fast dest: not_Undef_is_Def [THEN iffD1] elim: DefE)
done

lemma slen_fscons_eq_rev:
        "(#x < enat (Suc (Suc n))) = (\<forall>a y. x \<noteq> a~> y \<or> #y < enat (Suc n))"
apply (simp add: fscons_def2 slen_scons_eq_rev)
apply (tactic \<open>step_tac (put_claset HOL_cs \<^context> addSEs @{thms DefE}) 1\<close>)
apply (tactic \<open>step_tac (put_claset HOL_cs \<^context> addSEs @{thms DefE}) 1\<close>)
apply (tactic \<open>step_tac (put_claset HOL_cs \<^context> addSEs @{thms DefE}) 1\<close>)
apply (tactic \<open>step_tac (put_claset HOL_cs \<^context> addSEs @{thms DefE}) 1\<close>)
apply (tactic \<open>step_tac (put_claset HOL_cs \<^context> addSEs @{thms DefE}) 1\<close>)
apply (tactic \<open>step_tac (put_claset HOL_cs \<^context> addSEs @{thms DefE}) 1\<close>)
apply (erule contrapos_np)
apply (fast dest: not_Undef_is_Def [THEN iffD1] elim: DefE)
done

lemma slen_fscons_less_eq:
        "(#(a~> y) < enat (Suc (Suc n))) = (#y < enat (Suc n))"
apply (subst slen_fscons_eq_rev)
apply (fast dest!: fscons_inject [THEN iffD1])
done


(* ------------------------------------------------------------------------- *)

section "induction"

lemma fstream_ind:
        "[| adm P; P <>; !!a s. P s ==> P (a~> s) |] ==> P x"
apply (erule stream.induct)
apply (assumption)
apply (unfold fscons_def2)
apply (fast dest: not_Undef_is_Def [THEN iffD1])
done

lemma fstream_ind2:
  "[| adm P; P UU; !!a. P (a~> UU); !!a b s. P s ==> P (a~> b~> s) |] ==> P x"
apply (erule stream_ind2)
apply (assumption)
apply (unfold fscons_def2)
apply (fast dest: not_Undef_is_Def [THEN iffD1])
apply (fast dest: not_Undef_is_Def [THEN iffD1])
done


(* ------------------------------------------------------------------------- *)

section "fsfilter"

lemma fsfilter_empty: "A(C)UU = UU"
apply (unfold fsfilter_def)
apply (rule sfilter_empty)
done

lemma fsfilter_fscons:
        "A(C)x~> xs = (if x\<in>A then x~> (A(C)xs) else A(C)xs)"
apply (unfold fsfilter_def)
apply (simp add: fscons_def2 If_and_if)
done

lemma fsfilter_emptys: "{}(C)x = UU"
apply (rule_tac x="x" in fstream_ind)
apply (simp)
apply (rule fsfilter_empty)
apply (simp add: fsfilter_fscons)
done

lemma fsfilter_insert: "(insert a A)(C)a~> x = a~> ((insert a A)(C)x)"
by (simp add: fsfilter_fscons)

lemma fsfilter_single_in: "{a}(C)a~> x = a~> ({a}(C)x)"
by (rule fsfilter_insert)

lemma fsfilter_single_out: "b ~= a ==> {a}(C)b~> x = ({a}(C)x)"
by (simp add: fsfilter_fscons)

lemma fstream_lub_lemma1:
    "\<lbrakk>chain Y; (\<Squnion>i. Y i) = a\<leadsto>s\<rbrakk> \<Longrightarrow> \<exists>j t. Y j = a\<leadsto>t"
apply (case_tac "max_in_chain i Y")
apply  (drule (1) lub_finch1 [THEN lub_eqI, THEN sym])
apply  (force)
apply (unfold max_in_chain_def)
apply auto
apply (frule (1) chain_mono)
apply (rule_tac x="Y j" in fstream_cases)
apply  (force)
apply (drule_tac x="j" in is_ub_thelub)
apply (force)
done

lemma fstream_lub_lemma:
      "\<lbrakk>chain Y; (\<Squnion>i. Y i) = a\<leadsto>s\<rbrakk> \<Longrightarrow> (\<exists>j t. Y j = a\<leadsto>t) \<and> (\<exists>X. chain X \<and> (\<forall>i. \<exists>j. Y j = a\<leadsto>X i) \<and> (\<Squnion>i. X i) = s)"
apply (frule (1) fstream_lub_lemma1)
apply (clarsimp)
apply (rule_tac x="\<lambda>i. rt\<cdot>(Y(i+j))" in exI)
apply (rule conjI)
apply  (erule chain_shift [THEN chain_monofun])
apply safe
apply  (drule_tac i="j" and j="i+j" in chain_mono)
apply   (simp)
apply  (simp)
apply  (rule_tac x="i+j" in exI)
apply  (drule fstream_prefix)
apply  (clarsimp)
apply  (subst lub_APP)
apply   (rule chainI)
apply   (fast)
apply  (erule chain_shift)
apply (subst lub_const)
apply (subst lub_range_shift)
apply  (assumption)
apply (simp)
done

end
