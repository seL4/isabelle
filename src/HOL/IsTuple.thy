(*  Title:      HOL/IsTuple.thy
    Author:     Thomas Sewell, NICTA
*)

header {* Operators on types isomorphic to tuples *}

theory IsTuple imports Product_Type

uses ("Tools/istuple_support.ML")

begin

text {*
This module provides operators and lemmas for types isomorphic to tuples.
These types are used in defining efficient records. Consider the record
access/update simplification, alpha (beta_update f rec) = alpha rec for
distinct fields alpha and beta of some record type with n fields. There
are n^2 such theorems, which is prohibits storage of all of them for
large n. The rules can be proved on the fly by case decomposition and
simplification in O(n) time. By creating O(n) isomorphic-tuple types
while defining the record, however, we can prove the access/update
simplification in O(log(n)^2) time.

The O(n) cost of case decomposition is not because O(n) steps are taken,
but rather because the resulting rule must contain O(n) new variables and
an O(n) size concrete record construction. To sidestep this cost, we would
like to avoid case decomposition in proving access/update theorems.

Record types are defined as isomorphic to tuple types. For instance, a
record type with fields 'a, 'b, 'c and 'd might be introduced as
isomorphic to 'a \<times> ('b \<times> ('c \<times> 'd)). If we balance the tuple tree to
('a \<times> 'b) \<times> ('c \<times> 'd) then accessors can be defined by converting to
the underlying type then using O(log(n)) fst or snd operations.
Updators can be defined similarly, if we introduce a fst_update and
snd_update function. Furthermore, we can prove the access/update
theorem in O(log(n)) steps by using simple rewrites on fst, snd,
fst_update and snd_update.

The catch is that, although O(log(n)) steps were taken, the underlying
type we converted to is a tuple tree of size O(n). Processing this term
type wastes performance. We avoid this for large n by taking each
subtree of size K and defining a new type isomorphic to that tuple
subtree. The record can now be defined as isomorphic to a tuple tree
of these O(n/K) new types, or, if n > K*K, we can repeat the process,
until the record can be defined in terms of a tuple tree of complexity
less than the constant K.

If we prove the access/update theorem on this type with the analagous
steps to the tuple tree, we consume O(log(n)^2) time as the intermediate
terms are O(log(n)) in size and the types needed have size bounded by K.
To enable this analagous traversal, we define the functions seen below:
istuple_fst, istuple_snd, istuple_fst_update and istuple_snd. These
functions generalise tuple operations by taking a parameter that
encapsulates a tuple isomorphism. The rewrites needed on these functions
now need an additional assumption which is that the isomorphism works.

These rewrites are typically used in a structured way. With a little
thinking they can be presented as an introduction rule set rather than
a rewrite rule set. This is an optimisation, as net matching can be
performed at one term location for each step rather than the simplifier
searching the term for possible applications.
*}

typedef ('a, 'b, 'c) tuple_isomorphism
  = "UNIV :: (('a \<Rightarrow> ('b \<times> 'c)) \<times> (('b \<times> 'c) \<Rightarrow> 'a)) set"
  by simp

constdefs
  "TupleIsomorphism repr abst \<equiv> Abs_tuple_isomorphism (repr, abst)"

constdefs
  istuple_fst :: "('a, 'b, 'c) tuple_isomorphism \<Rightarrow> 'a \<Rightarrow> 'b"
 "istuple_fst isom \<equiv> let (repr, abst) = Rep_tuple_isomorphism isom in fst \<circ> repr"
  istuple_snd :: "('a, 'b, 'c) tuple_isomorphism \<Rightarrow> 'a \<Rightarrow> 'c"
 "istuple_snd isom \<equiv>  let (repr, abst) = Rep_tuple_isomorphism isom in snd \<circ> repr"
  istuple_fst_update :: "('a, 'b, 'c) tuple_isomorphism \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'a)"
 "istuple_fst_update isom \<equiv>
     let (repr, abst) = Rep_tuple_isomorphism isom in
        (\<lambda>f v. abst (f (fst (repr v)), snd (repr v)))"
  istuple_snd_update :: "('a, 'b, 'c) tuple_isomorphism \<Rightarrow> ('c \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'a)"
 "istuple_snd_update isom \<equiv>
     let (repr, abst) = Rep_tuple_isomorphism isom in
        (\<lambda>f v. abst (fst (repr v), f (snd (repr v))))"
  istuple_cons :: "('a, 'b, 'c) tuple_isomorphism \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'a"
 "istuple_cons isom \<equiv> let (repr, abst) = Rep_tuple_isomorphism isom in curry abst"

text {*
These predicates are used in the introduction rule set to constrain
matching appropriately. The elimination rules for them produce the
desired theorems once they are proven. The final introduction rules are
used when no further rules from the introduction rule set can apply.
*}

constdefs
  istuple_surjective_proof_assist :: "'a \<Rightarrow> 'b \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
 "istuple_surjective_proof_assist x y f \<equiv> f x = y"
  istuple_update_accessor_cong_assist :: "(('b \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'a))
                              \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
 "istuple_update_accessor_cong_assist upd acc
    \<equiv> (\<forall>f v. upd (\<lambda>x. f (acc v)) v = upd f v)
       \<and> (\<forall>v. upd id v = v)"
  istuple_update_accessor_eq_assist :: "(('b \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'a)) \<Rightarrow> ('a \<Rightarrow> 'b)
                              \<Rightarrow> 'a \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool"
 "istuple_update_accessor_eq_assist upd acc v f v' x
    \<equiv> upd f v = v' \<and> acc v = x
      \<and> istuple_update_accessor_cong_assist upd acc"

lemma update_accessor_congruence_foldE:
  assumes uac: "istuple_update_accessor_cong_assist upd acc"
  and       r: "r = r'" and v: "acc r' = v'"
  and       f: "\<And>v. v' = v \<Longrightarrow> f v = f' v"
  shows        "upd f r = upd f' r'"
  using uac r v[symmetric]
  apply (subgoal_tac "upd (\<lambda>x. f (acc r')) r' = upd (\<lambda>x. f' (acc r')) r'")
   apply (simp add: istuple_update_accessor_cong_assist_def)
  apply (simp add: f)
  done

lemma update_accessor_congruence_unfoldE:
  "\<lbrakk> istuple_update_accessor_cong_assist upd acc;
     r = r'; acc r' = v'; \<And>v. v = v' \<Longrightarrow> f v = f' v \<rbrakk>
     \<Longrightarrow> upd f r = upd f' r'"
  apply (erule(2) update_accessor_congruence_foldE)
  apply simp
  done

lemma istuple_update_accessor_cong_assist_id:
  "istuple_update_accessor_cong_assist upd acc \<Longrightarrow> upd id = id"
  by (rule ext, simp add: istuple_update_accessor_cong_assist_def)

lemma update_accessor_noopE:
  assumes uac: "istuple_update_accessor_cong_assist upd acc"
      and acc: "f (acc x) = acc x"
  shows        "upd f x = x"
  using uac
  by (simp add: acc istuple_update_accessor_cong_assist_id[OF uac, unfolded id_def]
          cong: update_accessor_congruence_unfoldE[OF uac])

lemma update_accessor_noop_compE:
  assumes uac: "istuple_update_accessor_cong_assist upd acc"
  assumes acc: "f (acc x) = acc x"
  shows      "upd (g \<circ> f) x = upd g x"
  by (simp add: acc cong: update_accessor_congruence_unfoldE[OF uac])

lemma update_accessor_cong_assist_idI:
  "istuple_update_accessor_cong_assist id id"
  by (simp add: istuple_update_accessor_cong_assist_def)

lemma update_accessor_cong_assist_triv:
  "istuple_update_accessor_cong_assist upd acc
       \<Longrightarrow> istuple_update_accessor_cong_assist upd acc"
  by assumption

lemma update_accessor_accessor_eqE:
  "\<lbrakk> istuple_update_accessor_eq_assist upd acc v f v' x \<rbrakk> \<Longrightarrow> acc v = x"
  by (simp add: istuple_update_accessor_eq_assist_def)

lemma update_accessor_updator_eqE:
  "\<lbrakk> istuple_update_accessor_eq_assist upd acc v f v' x \<rbrakk> \<Longrightarrow> upd f v = v'"
  by (simp add: istuple_update_accessor_eq_assist_def)

lemma istuple_update_accessor_eq_assist_idI:
  "v' = f v \<Longrightarrow> istuple_update_accessor_eq_assist id id v f v' v"
  by (simp add: istuple_update_accessor_eq_assist_def
                update_accessor_cong_assist_idI)

lemma istuple_update_accessor_eq_assist_triv:
  "istuple_update_accessor_eq_assist upd acc v f v' x
     \<Longrightarrow> istuple_update_accessor_eq_assist upd acc v f v' x"
  by assumption

lemma istuple_update_accessor_cong_from_eq:
  "istuple_update_accessor_eq_assist upd acc v f v' x
     \<Longrightarrow> istuple_update_accessor_cong_assist upd acc"
  by (simp add: istuple_update_accessor_eq_assist_def)

lemma o_eq_dest:
  "a o b = c o d \<Longrightarrow> a (b v) = c (d v)"
  apply (clarsimp simp: o_def)
  apply (erule fun_cong)
  done

lemma o_eq_elim:
  "\<lbrakk> a o b = c o d; \<lbrakk> \<And>v. a (b v) = c (d v) \<rbrakk> \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  apply (erule meta_mp)
  apply (erule o_eq_dest)
  done

lemma istuple_surjective_proof_assistI:
  "f x = y \<Longrightarrow>
     istuple_surjective_proof_assist x y f"
  by (simp add: istuple_surjective_proof_assist_def)

lemma istuple_surjective_proof_assist_idE:
  "istuple_surjective_proof_assist x y id \<Longrightarrow> x = y"
  by (simp add: istuple_surjective_proof_assist_def)

locale isomorphic_tuple =
  fixes isom :: "('a, 'b, 'c) tuple_isomorphism" 
       and repr and abst
  defines "repr \<equiv> fst (Rep_tuple_isomorphism isom)"
  defines "abst \<equiv> snd (Rep_tuple_isomorphism isom)"
  assumes repr_inv: "\<And>x. abst (repr x) = x"
  assumes abst_inv: "\<And>y. repr (abst y) = y"

begin

lemma repr_inj:
  "(repr x = repr y) = (x = y)"
  apply (rule iffI, simp_all)
  apply (drule_tac f=abst in arg_cong, simp add: repr_inv)
  done

lemma abst_inj:
  "(abst x = abst y) = (x = y)"
  apply (rule iffI, simp_all)
  apply (drule_tac f=repr in arg_cong, simp add: abst_inv)
  done

lemma split_Rep:
  "split f (Rep_tuple_isomorphism isom)
     = f repr abst"
  by (simp add: split_def repr_def abst_def)

lemmas simps = Let_def split_Rep repr_inv abst_inv repr_inj abst_inj

lemma istuple_access_update_fst_fst:
  "\<lbrakk> f o h g = j o f \<rbrakk> \<Longrightarrow>
    (f o istuple_fst isom) o (istuple_fst_update isom o h) g
          = j o (f o istuple_fst isom)"
  by (clarsimp simp: istuple_fst_update_def istuple_fst_def simps
             intro!: ext elim!: o_eq_elim)

lemma istuple_access_update_snd_snd:
  "\<lbrakk> f o h g = j o f \<rbrakk> \<Longrightarrow>
    (f o istuple_snd isom) o (istuple_snd_update isom o h) g
          = j o (f o istuple_snd isom)"
  by (clarsimp simp: istuple_snd_update_def istuple_snd_def simps
             intro!: ext elim!: o_eq_elim)

lemma istuple_access_update_fst_snd:
  "(f o istuple_fst isom) o (istuple_snd_update isom o h) g
          = id o (f o istuple_fst isom)"
  by (clarsimp simp: istuple_snd_update_def istuple_fst_def simps
             intro!: ext elim!: o_eq_elim)

lemma istuple_access_update_snd_fst:
  "(f o istuple_snd isom) o (istuple_fst_update isom o h) g
          = id o (f o istuple_snd isom)"
  by (clarsimp simp: istuple_fst_update_def istuple_snd_def simps
             intro!: ext elim!: o_eq_elim)

lemma istuple_update_swap_fst_fst:
  "\<lbrakk> h f o j g = j g o h f \<rbrakk> \<Longrightarrow>
    (istuple_fst_update isom o h) f o (istuple_fst_update isom o j) g
          = (istuple_fst_update isom o j) g o (istuple_fst_update isom o h) f"
  by (clarsimp simp: istuple_fst_update_def simps
             intro!: ext elim!: o_eq_elim)

lemma istuple_update_swap_snd_snd:
  "\<lbrakk> h f o j g = j g o h f \<rbrakk> \<Longrightarrow>
    (istuple_snd_update isom o h) f o (istuple_snd_update isom o j) g
          = (istuple_snd_update isom o j) g o (istuple_snd_update isom o h) f"
  by (clarsimp simp: istuple_snd_update_def simps
             intro!: ext elim!: o_eq_elim)

lemma istuple_update_swap_fst_snd:
  "(istuple_snd_update isom o h) f o (istuple_fst_update isom o j) g
          = (istuple_fst_update isom o j) g o (istuple_snd_update isom o h) f"
  by (clarsimp simp: istuple_fst_update_def istuple_snd_update_def simps
             intro!: ext elim!: o_eq_elim)

lemma istuple_update_swap_snd_fst:
  "(istuple_fst_update isom o h) f o (istuple_snd_update isom o j) g
          = (istuple_snd_update isom o j) g o (istuple_fst_update isom o h) f"
  by (clarsimp simp: istuple_fst_update_def istuple_snd_update_def simps
             intro!: ext elim!: o_eq_elim)

lemma istuple_update_compose_fst_fst:
  "\<lbrakk> h f o j g = k (f o g) \<rbrakk> \<Longrightarrow>
    (istuple_fst_update isom o h) f o (istuple_fst_update isom o j) g
          = (istuple_fst_update isom o k) (f o g)"
  by (fastsimp simp: istuple_fst_update_def simps
             intro!: ext elim!: o_eq_elim dest: fun_cong)

lemma istuple_update_compose_snd_snd:
  "\<lbrakk> h f o j g = k (f o g) \<rbrakk> \<Longrightarrow>
    (istuple_snd_update isom o h) f o (istuple_snd_update isom o j) g
          = (istuple_snd_update isom o k) (f o g)"
  by (fastsimp simp: istuple_snd_update_def simps
             intro!: ext elim!: o_eq_elim dest: fun_cong)

lemma istuple_surjective_proof_assist_step:
  "\<lbrakk> istuple_surjective_proof_assist v a (istuple_fst isom o f);
     istuple_surjective_proof_assist v b (istuple_snd isom o f) \<rbrakk>
      \<Longrightarrow> istuple_surjective_proof_assist v (istuple_cons isom a b) f"
  by (clarsimp simp: istuple_surjective_proof_assist_def simps
                     istuple_fst_def istuple_snd_def istuple_cons_def)

lemma istuple_fst_update_accessor_cong_assist:
  "istuple_update_accessor_cong_assist f g \<Longrightarrow>
      istuple_update_accessor_cong_assist (istuple_fst_update isom o f) (g o istuple_fst isom)"
  by (clarsimp simp: istuple_update_accessor_cong_assist_def simps
                     istuple_fst_update_def istuple_fst_def)

lemma istuple_snd_update_accessor_cong_assist:
  "istuple_update_accessor_cong_assist f g \<Longrightarrow>
      istuple_update_accessor_cong_assist (istuple_snd_update isom o f) (g o istuple_snd isom)"
  by (clarsimp simp: istuple_update_accessor_cong_assist_def simps
                     istuple_snd_update_def istuple_snd_def)

lemma istuple_fst_update_accessor_eq_assist:
  "istuple_update_accessor_eq_assist f g a u a' v \<Longrightarrow>
      istuple_update_accessor_eq_assist (istuple_fst_update isom o f) (g o istuple_fst isom)
              (istuple_cons isom a b) u (istuple_cons isom a' b) v"
  by (clarsimp simp: istuple_update_accessor_eq_assist_def istuple_fst_update_def istuple_fst_def
                     istuple_update_accessor_cong_assist_def istuple_cons_def simps)

lemma istuple_snd_update_accessor_eq_assist:
  "istuple_update_accessor_eq_assist f g b u b' v \<Longrightarrow>
      istuple_update_accessor_eq_assist (istuple_snd_update isom o f) (g o istuple_snd isom)
              (istuple_cons isom a b) u (istuple_cons isom a b') v"
  by (clarsimp simp: istuple_update_accessor_eq_assist_def istuple_snd_update_def istuple_snd_def
                     istuple_update_accessor_cong_assist_def istuple_cons_def simps)

lemma istuple_cons_conj_eqI:
  "\<lbrakk> (a = c \<and> b = d \<and> P) = Q \<rbrakk> \<Longrightarrow>
    (istuple_cons isom a b = istuple_cons isom c d \<and> P) = Q"
  by (clarsimp simp: istuple_cons_def simps)

lemmas intros =
    istuple_access_update_fst_fst
    istuple_access_update_snd_snd
    istuple_access_update_fst_snd
    istuple_access_update_snd_fst
    istuple_update_swap_fst_fst
    istuple_update_swap_snd_snd
    istuple_update_swap_fst_snd
    istuple_update_swap_snd_fst
    istuple_update_compose_fst_fst
    istuple_update_compose_snd_snd
    istuple_surjective_proof_assist_step
    istuple_fst_update_accessor_eq_assist
    istuple_snd_update_accessor_eq_assist
    istuple_fst_update_accessor_cong_assist
    istuple_snd_update_accessor_cong_assist
    istuple_cons_conj_eqI

end

lemma isomorphic_tuple_intro:
  assumes repr_inj: "\<And>x y. (repr x = repr y) = (x = y)"
     and abst_inv: "\<And>z. repr (abst z) = z"
  shows "v \<equiv> TupleIsomorphism repr abst \<Longrightarrow> isomorphic_tuple v"
  apply (rule isomorphic_tuple.intro,
         simp_all add: TupleIsomorphism_def Abs_tuple_isomorphism_inverse
                       tuple_isomorphism_def abst_inv)
  apply (cut_tac x="abst (repr x)" and y="x" in repr_inj)
  apply (simp add: abst_inv)
  done

constdefs
 "tuple_istuple \<equiv> TupleIsomorphism id id"

lemma tuple_istuple:
  "isomorphic_tuple tuple_istuple"
  by (simp add: isomorphic_tuple_intro[OF _ _ reflexive] tuple_istuple_def)

lemma refl_conj_eq:
  "Q = R \<Longrightarrow> (P \<and> Q) = (P \<and> R)"
  by simp

lemma meta_all_sameI:
  "(\<And>x. PROP P x \<equiv> PROP Q x) \<Longrightarrow> (\<And>x. PROP P x) \<equiv> (\<And>x. PROP Q x)"
  by simp

lemma istuple_UNIV_I: "\<And>x. x\<in>UNIV \<equiv> True"
  by simp

lemma istuple_True_simp: "(True \<Longrightarrow> PROP P) \<equiv> PROP P"
  by simp

use "Tools/istuple_support.ML";

end
