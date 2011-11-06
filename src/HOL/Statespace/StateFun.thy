(*  Title:      HOL/Statespace/StateFun.thy
    Author:     Norbert Schirmer, TU Muenchen
*)

header {* State Space Representation as Function \label{sec:StateFun}*}

theory StateFun imports DistinctTreeProver 
begin


text {* The state space is represented as a function from names to
values. We neither fix the type of names nor the type of values. We
define lookup and update functions and provide simprocs that simplify
expressions containing these, similar to HOL-records.

The lookup and update function get constructor/destructor functions as
parameters. These are used to embed various HOL-types into the
abstract value type. Conceptually the abstract value type is a sum of
all types that we attempt to store in the state space.

The update is actually generalized to a map function. The map supplies
better compositionality, especially if you think of nested state
spaces.  *} 

definition K_statefun :: "'a \<Rightarrow> 'b \<Rightarrow> 'a" where "K_statefun c x \<equiv> c"

lemma K_statefun_apply [simp]: "K_statefun c x = c"
  by (simp add: K_statefun_def)

lemma K_statefun_comp [simp]: "(K_statefun c \<circ> f) = K_statefun c"
  by (rule ext) (simp add: comp_def)

lemma K_statefun_cong [cong]: "K_statefun c x = K_statefun c x"
  by (rule refl)

definition lookup :: "('v \<Rightarrow> 'a) \<Rightarrow> 'n \<Rightarrow> ('n \<Rightarrow> 'v) \<Rightarrow> 'a"
  where "lookup destr n s = destr (s n)"

definition update ::
  "('v \<Rightarrow> 'a1) \<Rightarrow> ('a2 \<Rightarrow> 'v) \<Rightarrow> 'n \<Rightarrow> ('a1 \<Rightarrow> 'a2) \<Rightarrow> ('n \<Rightarrow> 'v) \<Rightarrow> ('n \<Rightarrow> 'v)"
  where "update destr constr n f s = s(n := constr (f (destr (s n))))"

lemma lookup_update_same:
  "(\<And>v. destr (constr v) = v) \<Longrightarrow> lookup destr n (update destr constr n f s) = 
         f (destr (s n))"  
  by (simp add: lookup_def update_def)

lemma lookup_update_id_same:
  "lookup destr n (update destr' id n (K_statefun (lookup id n s')) s) =                  
     lookup destr n s'"  
  by (simp add: lookup_def update_def)

lemma lookup_update_other:
  "n\<noteq>m \<Longrightarrow> lookup destr n (update destr' constr m f s) = lookup destr n s"  
  by (simp add: lookup_def update_def)


lemma id_id_cancel: "id (id x) = x" 
  by (simp add: id_def)
  
lemma destr_contstr_comp_id: "(\<And>v. destr (constr v) = v) \<Longrightarrow> destr \<circ> constr = id"
  by (rule ext) simp



lemma block_conj_cong: "(P \<and> Q) = (P \<and> Q)"
  by simp

lemma conj1_False: "P \<equiv> False \<Longrightarrow> (P \<and> Q) \<equiv> False"
  by simp

lemma conj2_False: "Q \<equiv> False \<Longrightarrow> (P \<and> Q) \<equiv> False"
  by simp

lemma conj_True: "P \<equiv> True \<Longrightarrow> Q \<equiv> True \<Longrightarrow> (P \<and> Q) \<equiv> True"
  by simp

lemma conj_cong: "P \<equiv> P' \<Longrightarrow> Q \<equiv> Q' \<Longrightarrow> (P \<and> Q) \<equiv> (P' \<and> Q')"
  by simp


lemma update_apply: "(update destr constr n f s x) = 
     (if x=n then constr (f (destr (s n))) else s x)"
  by (simp add: update_def)

lemma ex_id: "\<exists>x. id x = y"
  by (simp add: id_def)

lemma swap_ex_eq: 
  "\<exists>s. f s = x \<equiv> True \<Longrightarrow>
   \<exists>s. x = f s \<equiv> True"
  apply (rule eq_reflection)
  apply auto
  done

lemmas meta_ext = eq_reflection [OF ext]

(* This lemma only works if the store is welltyped:
    "\<exists>x.  s ''n'' = (c x)" 
   or in general when c (d x) = x,
     (for example: c=id and d=id)
 *)
lemma "update d c n (K_statespace (lookup d n s)) s = s"
  apply (simp add: update_def lookup_def)
  apply (rule ext)
  apply simp
  oops

end