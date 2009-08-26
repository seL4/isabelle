theory IsTuple imports Product_Type

uses ("Tools/istuple_support.ML")

begin

constdefs
  istuple_fst :: "('a \<Rightarrow> ('b \<times> 'c)) \<Rightarrow> 'a \<Rightarrow> 'b"
 "istuple_fst isom \<equiv> (fst \<circ> isom)"
  istuple_snd :: "('a \<Rightarrow> ('b \<times> 'c)) \<Rightarrow> 'a \<Rightarrow> 'c"
 "istuple_snd isom \<equiv> (snd \<circ> isom)"
  istuple_fst_update :: "('a \<Rightarrow> ('b \<times> 'c)) \<Rightarrow> (('b \<times> 'c) \<Rightarrow> 'a)
                           \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'a)"
 "istuple_fst_update isom inv \<equiv> \<lambda>f v. inv (f (fst (isom v)), snd (isom v))"
  istuple_snd_update :: "('a \<Rightarrow> ('b \<times> 'c)) \<Rightarrow> (('b \<times> 'c) \<Rightarrow> 'a)
                           \<Rightarrow> ('c \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'a)"
 "istuple_snd_update isom inv \<equiv> \<lambda>f v. inv (fst (isom v), f (snd (isom v)))"

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
  fixes isom :: "'a \<Rightarrow> ('b \<times> 'c)" and inv :: "('b \<times> 'c) \<Rightarrow> 'a"
    and cons :: "'b \<Rightarrow> 'c \<Rightarrow> 'a"
  assumes isom_eq: "(isom x = isom y) = (x = y)"
  and inverse_inv: "isom (inv v) = v"
  and cons_def: "cons \<equiv> curry inv"

begin

lemma inverse_isom:
  "(inv (isom v)) = v"
  by (rule iffD1 [OF isom_eq], simp add: inverse_inv)

lemma inv_eq:
  "(inv x = inv y) = (x = y)"
  apply (rule iffI)
   apply (drule arg_cong[where f=isom])
   apply (simp add: inverse_inv)
  apply simp
  done

lemmas simps = isom_eq inv_eq inverse_inv inverse_isom cons_def

lemma istuple_access_update_fst_fst:
  "\<lbrakk> f o h g = j o f \<rbrakk> \<Longrightarrow>
    (f o istuple_fst isom) o (istuple_fst_update isom inv o h) g
          = j o (f o istuple_fst isom)"
  by (clarsimp simp: istuple_fst_update_def istuple_fst_def simps
             intro!: ext elim!: o_eq_elim)

lemma istuple_access_update_snd_snd:
  "\<lbrakk> f o h g = j o f \<rbrakk> \<Longrightarrow>
    (f o istuple_snd isom) o (istuple_snd_update isom inv o h) g
          = j o (f o istuple_snd isom)"
  by (clarsimp simp: istuple_snd_update_def istuple_snd_def simps
             intro!: ext elim!: o_eq_elim)

lemma istuple_access_update_fst_snd:
  "(f o istuple_fst isom) o (istuple_snd_update isom inv o h) g
          = id o (f o istuple_fst isom)"
  by (clarsimp simp: istuple_snd_update_def istuple_fst_def simps
             intro!: ext elim!: o_eq_elim)

lemma istuple_access_update_snd_fst:
  "(f o istuple_snd isom) o (istuple_fst_update isom inv o h) g
          = id o (f o istuple_snd isom)"
  by (clarsimp simp: istuple_fst_update_def istuple_snd_def simps
             intro!: ext elim!: o_eq_elim)

lemma istuple_update_swap_fst_fst:
  "\<lbrakk> h f o j g = j g o h f \<rbrakk> \<Longrightarrow>
    (istuple_fst_update isom inv o h) f o (istuple_fst_update isom inv o j) g
          = (istuple_fst_update isom inv o j) g o (istuple_fst_update isom inv o h) f"
  by (clarsimp simp: istuple_fst_update_def simps
             intro!: ext elim!: o_eq_elim)

lemma istuple_update_swap_snd_snd:
  "\<lbrakk> h f o j g = j g o h f \<rbrakk> \<Longrightarrow>
    (istuple_snd_update isom inv o h) f o (istuple_snd_update isom inv o j) g
          = (istuple_snd_update isom inv o j) g o (istuple_snd_update isom inv o h) f"
  by (clarsimp simp: istuple_snd_update_def simps
             intro!: ext elim!: o_eq_elim)

lemma istuple_update_swap_fst_snd:
  "(istuple_snd_update isom inv o h) f o (istuple_fst_update isom inv o j) g
          = (istuple_fst_update isom inv o j) g o (istuple_snd_update isom inv o h) f"
  by (clarsimp simp: istuple_fst_update_def istuple_snd_update_def simps
             intro!: ext elim!: o_eq_elim)

lemma istuple_update_swap_snd_fst:
  "(istuple_fst_update isom inv o h) f o (istuple_snd_update isom inv o j) g
          = (istuple_snd_update isom inv o j) g o (istuple_fst_update isom inv o h) f"
  by (clarsimp simp: istuple_fst_update_def istuple_snd_update_def simps
             intro!: ext elim!: o_eq_elim)

lemma istuple_update_compose_fst_fst:
  "\<lbrakk> h f o j g = k (f o g) \<rbrakk> \<Longrightarrow>
    (istuple_fst_update isom inv o h) f o (istuple_fst_update isom inv o j) g
          = (istuple_fst_update isom inv o k) (f o g)"
  by (fastsimp simp: istuple_fst_update_def simps
             intro!: ext elim!: o_eq_elim dest: fun_cong)

lemma istuple_update_compose_snd_snd:
  "\<lbrakk> h f o j g = k (f o g) \<rbrakk> \<Longrightarrow>
    (istuple_snd_update isom inv o h) f o (istuple_snd_update isom inv o j) g
          = (istuple_snd_update isom inv o k) (f o g)"
  by (fastsimp simp: istuple_snd_update_def simps
             intro!: ext elim!: o_eq_elim dest: fun_cong)

lemma istuple_surjective_proof_assist_step:
  "\<lbrakk> istuple_surjective_proof_assist v a (istuple_fst isom o f);
     istuple_surjective_proof_assist v b (istuple_snd isom o f) \<rbrakk>
      \<Longrightarrow> istuple_surjective_proof_assist v (cons a b) f"
  by (clarsimp simp: istuple_surjective_proof_assist_def simps
                     istuple_fst_def istuple_snd_def)

lemma istuple_fst_update_accessor_cong_assist:
  "istuple_update_accessor_cong_assist f g \<Longrightarrow>
      istuple_update_accessor_cong_assist (istuple_fst_update isom inv o f) (g o istuple_fst isom)"
  by (simp add: istuple_update_accessor_cong_assist_def istuple_fst_update_def istuple_fst_def simps)

lemma istuple_snd_update_accessor_cong_assist:
  "istuple_update_accessor_cong_assist f g \<Longrightarrow>
      istuple_update_accessor_cong_assist (istuple_snd_update isom inv o f) (g o istuple_snd isom)"
  by (simp add: istuple_update_accessor_cong_assist_def istuple_snd_update_def istuple_snd_def simps)

lemma istuple_fst_update_accessor_eq_assist:
  "istuple_update_accessor_eq_assist f g a u a' v \<Longrightarrow>
      istuple_update_accessor_eq_assist (istuple_fst_update isom inv o f) (g o istuple_fst isom)
              (cons a b) u (cons a' b) v"
  by (simp add: istuple_update_accessor_eq_assist_def istuple_fst_update_def istuple_fst_def simps
                istuple_update_accessor_cong_assist_def)

lemma istuple_snd_update_accessor_eq_assist:
  "istuple_update_accessor_eq_assist f g b u b' v \<Longrightarrow>
      istuple_update_accessor_eq_assist (istuple_snd_update isom inv o f) (g o istuple_snd isom)
              (cons a b) u (cons a b') v"
  by (simp add: istuple_update_accessor_eq_assist_def istuple_snd_update_def istuple_snd_def simps
                istuple_update_accessor_cong_assist_def)

lemma cons_conj_eqI:
  "\<lbrakk> (a = c \<and> b = d \<and> P) = Q \<rbrakk> \<Longrightarrow>
    (cons a b = cons c d \<and> P) = Q"
  by (simp add: simps)

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
    cons_conj_eqI

end

interpretation tuple_automorphic: isomorphic_tuple [id id Pair]
  by (unfold_locales, simp_all add: curry_def)

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

ML {* val traceref = ref [TrueI]; *}

use "Tools/istuple_support.ML";

end
