(*  Title:      HOL/BNF_Examples/ListF.thy
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Andrei Popescu, TU Muenchen
    Copyright   2012

Finite lists.
*)

header {* Finite Lists *}

theory ListF
imports Main
begin

datatype_new 'a listF (map: mapF rel: relF) =
  NilF (defaults tlF: NilF) | Conss (hdF: 'a) (tlF: "'a listF")
datatype_new_compat listF

definition Singll ("[[_]]") where
  [simp]: "Singll a \<equiv> Conss a NilF"

primrec appendd (infixr "@@" 65) where
  "NilF @@ ys = ys"
| "Conss x xs @@ ys = Conss x (xs @@ ys)"

primrec lrev where
  "lrev NilF = NilF"
| "lrev (Conss y ys) = lrev ys @@ [[y]]"

lemma appendd_NilF[simp]: "xs @@ NilF = xs"
  by (induct xs) auto

lemma appendd_assoc[simp]: "(xs @@ ys) @@ zs = xs @@ ys @@ zs"
  by (induct xs) auto

lemma lrev_appendd[simp]: "lrev (xs @@ ys) = lrev ys @@ lrev xs"
  by (induct xs) auto

lemma listF_map_appendd[simp]:
  "mapF f (xs @@ ys) = mapF f xs @@ mapF f ys"
  by (induct xs) auto

lemma lrev_listF_map[simp]: "lrev (mapF f xs) = mapF f (lrev xs)"
  by (induct xs) auto

lemma lrev_lrev[simp]: "lrev (lrev xs) = xs"
  by (induct xs) auto

primrec lengthh where
  "lengthh NilF = 0"
| "lengthh (Conss x xs) = Suc (lengthh xs)"

fun nthh where
  "nthh (Conss x xs) 0 = x"
| "nthh (Conss x xs) (Suc n) = nthh xs n"
| "nthh xs i = undefined"

lemma lengthh_listF_map[simp]: "lengthh (mapF f xs) = lengthh xs"
  by (induct xs) auto

lemma nthh_listF_map[simp]:
  "i < lengthh xs \<Longrightarrow> nthh (mapF f xs) i = f (nthh xs i)"
  by (induct rule: nthh.induct) auto

lemma nthh_listF_set[simp]: "i < lengthh xs \<Longrightarrow> nthh xs i \<in> set_listF xs"
  by (induct rule: nthh.induct) auto

lemma NilF_iff[iff]: "(lengthh xs = 0) = (xs = NilF)"
  by (induct xs) auto

lemma Conss_iff[iff]:
  "(lengthh xs = Suc n) = (\<exists>y ys. xs = Conss y ys \<and> lengthh ys = n)"
  by (induct xs) auto

lemma Conss_iff'[iff]:
  "(Suc n = lengthh xs) = (\<exists>y ys. xs = Conss y ys \<and> lengthh ys = n)"
  by (induct xs) (simp, simp, blast)

lemma listF_induct2[consumes 1, case_names NilF Conss]: "\<lbrakk>lengthh xs = lengthh ys; P NilF NilF;
    \<And>x xs y ys. P xs ys \<Longrightarrow> P (Conss x xs) (Conss y ys)\<rbrakk> \<Longrightarrow> P xs ys"
    by (induct xs arbitrary: ys) auto

fun zipp where
  "zipp NilF NilF = NilF"
| "zipp (Conss x xs) (Conss y ys) = Conss (x, y) (zipp xs ys)"
| "zipp xs ys = undefined"

lemma listF_map_fst_zip[simp]:
  "lengthh xs = lengthh ys \<Longrightarrow> mapF fst (zipp xs ys) = xs"
  by (induct rule: listF_induct2) auto

lemma listF_map_snd_zip[simp]:
  "lengthh xs = lengthh ys \<Longrightarrow> mapF snd (zipp xs ys) = ys"
  by (induct rule: listF_induct2) auto

lemma lengthh_zip[simp]:
  "lengthh xs = lengthh ys \<Longrightarrow> lengthh (zipp xs ys) = lengthh xs"
  by (induct rule: listF_induct2) auto

lemma nthh_zip[simp]:
  assumes "lengthh xs = lengthh ys"
  shows "i < lengthh xs \<Longrightarrow> nthh (zipp xs ys) i = (nthh xs i, nthh ys i)"
using assms proof (induct arbitrary: i rule: listF_induct2)
  case (Conss x xs y ys) thus ?case by (induct i) auto
qed simp

lemma list_set_nthh[simp]:
  "(x \<in> set_listF xs) \<Longrightarrow> (\<exists>i < lengthh xs. nthh xs i = x)"
  by (induct xs) (auto, induct rule: nthh.induct, auto)

end
