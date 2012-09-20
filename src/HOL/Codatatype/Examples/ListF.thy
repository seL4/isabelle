(*  Title:      HOL/Codatatype/Examples/ListF.thy
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Andrei Popescu, TU Muenchen
    Copyright   2012

Finite lists.
*)

header {* Finite Lists *}

theory ListF
imports "../Codatatype"
begin

data_raw listF: 'list = "unit + 'a \<times> 'list"

definition "NilF = listF_fld (Inl ())"
definition "Conss a as \<equiv> listF_fld (Inr (a, as))"

lemma listF_map_NilF[simp]: "listF_map f NilF = NilF"
unfolding listF_map_def pre_listF_map_def NilF_def listF.fld_iters by simp

lemma listF_map_Conss[simp]:
  "listF_map f (Conss x xs) = Conss (f x) (listF_map f xs)"
unfolding listF_map_def pre_listF_map_def Conss_def listF.fld_iters by simp

lemma listF_set_NilF[simp]: "listF_set NilF = {}"
unfolding listF_set_def NilF_def listF.fld_iters pre_listF_set1_def pre_listF_set2_def
  sum_set_defs pre_listF_map_def collect_def[abs_def] by simp

lemma listF_set_Conss[simp]: "listF_set (Conss x xs) = {x} \<union> listF_set xs"
unfolding listF_set_def Conss_def listF.fld_iters pre_listF_set1_def pre_listF_set2_def
  sum_set_defs prod_set_defs pre_listF_map_def collect_def[abs_def] by simp

lemma iter_sum_case_NilF: "listF_fld_iter (sum_case f g) NilF = f ()"
unfolding NilF_def listF.fld_iters pre_listF_map_def by simp


lemma iter_sum_case_Conss:
  "listF_fld_iter (sum_case f g) (Conss y ys) = g (y, listF_fld_iter (sum_case f g) ys)"
unfolding Conss_def listF.fld_iters pre_listF_map_def by simp

(* familiar induction principle *)
lemma listF_induct:
  fixes xs :: "'a listF"
  assumes IB: "P NilF" and IH: "\<And>x xs. P xs \<Longrightarrow> P (Conss x xs)"
  shows "P xs"
proof (rule listF.fld_induct)
  fix xs :: "unit + 'a \<times> 'a listF"
  assume raw_IH: "\<And>a. a \<in> pre_listF_set2 xs \<Longrightarrow> P a"
  show "P (listF_fld xs)"
  proof (cases xs)
    case (Inl a) with IB show ?thesis unfolding NilF_def by simp
  next
    case (Inr b)
    then obtain y ys where yys: "listF_fld xs = Conss y ys"
      unfolding Conss_def listF.fld_inject by (blast intro: prod.exhaust)
    hence "ys \<in> pre_listF_set2 xs"
      unfolding pre_listF_set2_def Conss_def listF.fld_inject sum_set_defs prod_set_defs
        collect_def[abs_def] by simp
    with raw_IH have "P ys" by blast
    with IH have "P (Conss y ys)" by blast
    with yys show ?thesis by simp
  qed
qed

rep_datatype NilF Conss
by (blast intro: listF_induct) (auto simp add: NilF_def Conss_def listF.fld_inject)

definition Singll ("[[_]]") where
  [simp]: "Singll a \<equiv> Conss a NilF"

definition appendd (infixr "@@" 65) where
  "appendd \<equiv> listF_fld_iter (sum_case (\<lambda> _. id) (\<lambda> (a,f) bs. Conss a (f bs)))"

definition "lrev \<equiv> listF_fld_iter (sum_case (\<lambda> _. NilF) (\<lambda> (b,bs). bs @@ [[b]]))"

lemma lrev_NilF[simp]: "lrev NilF = NilF"
unfolding lrev_def by (simp add: iter_sum_case_NilF)

lemma lrev_Conss[simp]: "lrev (Conss y ys) = lrev ys @@ [[y]]"
unfolding lrev_def by (simp add: iter_sum_case_Conss)

lemma NilF_appendd[simp]: "NilF @@ ys = ys"
unfolding appendd_def by (simp add: iter_sum_case_NilF)

lemma Conss_append[simp]: "Conss x xs @@ ys = Conss x (xs @@ ys)"
unfolding appendd_def by (simp add: iter_sum_case_Conss)

lemma appendd_NilF[simp]: "xs @@ NilF = xs"
by (rule listF_induct) auto

lemma appendd_assoc[simp]: "(xs @@ ys) @@ zs = xs @@ ys @@ zs"
by (rule listF_induct) auto

lemma lrev_appendd[simp]: "lrev (xs @@ ys) = lrev ys @@ lrev xs"
by (rule listF_induct[of _ xs]) auto

lemma listF_map_appendd[simp]:
  "listF_map f (xs @@ ys) = listF_map f xs @@ listF_map f ys"
by (rule listF_induct[of _ xs]) auto

lemma lrev_listF_map[simp]: "lrev (listF_map f xs) = listF_map f (lrev xs)"
by (rule listF_induct[of _ xs]) auto

lemma lrev_lrev[simp]: "lrev (lrev as) = as"
by (rule listF_induct) auto

fun lengthh where
  "lengthh NilF = 0"
| "lengthh (Conss x xs) = Suc (lengthh xs)"

fun nthh where
  "nthh (Conss x xs) 0 = x"
| "nthh (Conss x xs) (Suc n) = nthh xs n"
| "nthh xs i = undefined"

lemma lengthh_listF_map[simp]: "lengthh (listF_map f xs) = lengthh xs"
by (rule listF_induct[of _ xs]) auto

lemma nthh_listF_map[simp]:
  "i < lengthh xs \<Longrightarrow> nthh (listF_map f xs) i = f (nthh xs i)"
by (induct rule: nthh.induct) auto

lemma nthh_listF_set[simp]: "i < lengthh xs \<Longrightarrow> nthh xs i \<in> listF_set xs"
by (induct rule: nthh.induct) auto

lemma NilF_iff[iff]: "(lengthh xs = 0) = (xs = NilF)"
by (induct xs) auto

lemma Conss_iff[iff]:
  "(lengthh xs = Suc n) = (\<exists>y ys. xs = Conss y ys \<and> lengthh ys = n)"
by (induct xs) auto

lemma Conss_iff'[iff]:
  "(Suc n = lengthh xs) = (\<exists>y ys. xs = Conss y ys \<and> lengthh ys = n)"
by (induct xs) (simp, simp, blast)

lemma listF_induct2: "\<lbrakk>lengthh xs = lengthh ys; P NilF NilF;
    \<And>x xs y ys. P xs ys \<Longrightarrow> P (Conss x xs) (Conss y ys)\<rbrakk> \<Longrightarrow> P xs ys"
by (induct xs arbitrary: ys rule: listF_induct) auto

fun zipp where
  "zipp NilF NilF = NilF"
| "zipp (Conss x xs) (Conss y ys) = Conss (x, y) (zipp xs ys)"
| "zipp xs ys = undefined"

lemma listF_map_fst_zip[simp]:
  "lengthh xs = lengthh ys \<Longrightarrow> listF_map fst (zipp xs ys) = xs"
by (erule listF_induct2) auto

lemma listF_map_snd_zip[simp]:
  "lengthh xs = lengthh ys \<Longrightarrow> listF_map snd (zipp xs ys) = ys"
by (erule listF_induct2) auto

lemma lengthh_zip[simp]:
  "lengthh xs = lengthh ys \<Longrightarrow> lengthh (zipp xs ys) = lengthh xs"
by (erule listF_induct2) auto

lemma nthh_zip[simp]:
  assumes *: "lengthh xs = lengthh ys"
  shows "i < lengthh xs \<Longrightarrow> nthh (zipp xs ys) i = (nthh xs i, nthh ys i)"
proof (induct arbitrary: i rule: listF_induct2[OF *])
  case (2 x xs y ys) thus ?case by (induct i) auto
qed simp

lemma list_set_nthh[simp]:
  "(x \<in> listF_set xs) \<Longrightarrow> (\<exists>i < lengthh xs. nthh xs i = x)"
by (induct xs) (auto, induct rule: nthh.induct, auto)

end
