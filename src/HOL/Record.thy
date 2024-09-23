(*  Title:      HOL/Record.thy
    Author:     Wolfgang Naraschewski, TU Muenchen
    Author:     Markus Wenzel, TU Muenchen
    Author:     Norbert Schirmer, TU Muenchen
    Author:     Thomas Sewell, NICTA
    Author:     Florian Haftmann, TU Muenchen
*)

section \<open>Extensible records with structural subtyping\<close>

theory Record
imports Quickcheck_Exhaustive
keywords
  "record" :: thy_defn and
  "print_record" :: diag
begin

subsection \<open>Introduction\<close>

text \<open>
  Records are isomorphic to compound tuple types. To implement
  efficient records, we make this isomorphism explicit. Consider the
  record access/update simplification \<open>alpha (beta_update f
  rec) = alpha rec\<close> for distinct fields alpha and beta of some record
  rec with n fields. There are \<open>n ^ 2\<close> such theorems, which
  prohibits storage of all of them for large n. The rules can be
  proved on the fly by case decomposition and simplification in O(n)
  time. By creating O(n) isomorphic-tuple types while defining the
  record, however, we can prove the access/update simplification in
  \<open>O(log(n)^2)\<close> time.

  The O(n) cost of case decomposition is not because O(n) steps are
  taken, but rather because the resulting rule must contain O(n) new
  variables and an O(n) size concrete record construction. To sidestep
  this cost, we would like to avoid case decomposition in proving
  access/update theorems.

  Record types are defined as isomorphic to tuple types. For instance,
  a record type with fields \<open>'a\<close>, \<open>'b\<close>, \<open>'c\<close>
  and \<open>'d\<close> might be introduced as isomorphic to \<open>'a \<times>
  ('b \<times> ('c \<times> 'd))\<close>. If we balance the tuple tree to \<open>('a \<times>
  'b) \<times> ('c \<times> 'd)\<close> then accessors can be defined by converting to the
  underlying type then using O(log(n)) fst or snd operations.
  Updators can be defined similarly, if we introduce a \<open>fst_update\<close> and \<open>snd_update\<close> function. Furthermore, we can
  prove the access/update theorem in O(log(n)) steps by using simple
  rewrites on fst, snd, \<open>fst_update\<close> and \<open>snd_update\<close>.

  The catch is that, although O(log(n)) steps were taken, the
  underlying type we converted to is a tuple tree of size
  O(n). Processing this term type wastes performance. We avoid this
  for large n by taking each subtree of size K and defining a new type
  isomorphic to that tuple subtree. A record can now be defined as
  isomorphic to a tuple tree of these O(n/K) new types, or, if \<open>n > K*K\<close>, we can repeat the process, until the record can be
  defined in terms of a tuple tree of complexity less than the
  constant K.

  If we prove the access/update theorem on this type with the
  analogous steps to the tuple tree, we consume \<open>O(log(n)^2)\<close>
  time as the intermediate terms are \<open>O(log(n))\<close> in size and
  the types needed have size bounded by K.  To enable this analogous
  traversal, we define the functions seen below: \<open>iso_tuple_fst\<close>, \<open>iso_tuple_snd\<close>, \<open>iso_tuple_fst_update\<close>
  and \<open>iso_tuple_snd_update\<close>. These functions generalise tuple
  operations by taking a parameter that encapsulates a tuple
  isomorphism.  The rewrites needed on these functions now need an
  additional assumption which is that the isomorphism works.

  These rewrites are typically used in a structured way. They are here
  presented as the introduction rule \<open>isomorphic_tuple.intros\<close>
  rather than as a rewrite rule set. The introduction form is an
  optimisation, as net matching can be performed at one term location
  for each step rather than the simplifier searching the term for
  possible pattern matches. The rule set is used as it is viewed
  outside the locale, with the locale assumption (that the isomorphism
  is valid) left as a rule assumption. All rules are structured to aid
  net matching, using either a point-free form or an encapsulating
  predicate.
\<close>

subsection \<open>Operators and lemmas for types isomorphic to tuples\<close>

datatype (dead 'a, dead 'b, dead 'c) tuple_isomorphism =
  Tuple_Isomorphism "'a \<Rightarrow> 'b \<times> 'c" "'b \<times> 'c \<Rightarrow> 'a"

primrec
  repr :: "('a, 'b, 'c) tuple_isomorphism \<Rightarrow> 'a \<Rightarrow> 'b \<times> 'c" where
  "repr (Tuple_Isomorphism r a) = r"

primrec
  abst :: "('a, 'b, 'c) tuple_isomorphism \<Rightarrow> 'b \<times> 'c \<Rightarrow> 'a" where
  "abst (Tuple_Isomorphism r a) = a"

definition
  iso_tuple_fst :: "('a, 'b, 'c) tuple_isomorphism \<Rightarrow> 'a \<Rightarrow> 'b" where
  "iso_tuple_fst isom = fst \<circ> repr isom"

definition
  iso_tuple_snd :: "('a, 'b, 'c) tuple_isomorphism \<Rightarrow> 'a \<Rightarrow> 'c" where
  "iso_tuple_snd isom = snd \<circ> repr isom"

definition
  iso_tuple_fst_update ::
    "('a, 'b, 'c) tuple_isomorphism \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'a)" where
  "iso_tuple_fst_update isom f = abst isom \<circ> apfst f \<circ> repr isom"

definition
  iso_tuple_snd_update ::
    "('a, 'b, 'c) tuple_isomorphism \<Rightarrow> ('c \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'a)" where
  "iso_tuple_snd_update isom f = abst isom \<circ> apsnd f \<circ> repr isom"

definition
  iso_tuple_cons ::
    "('a, 'b, 'c) tuple_isomorphism \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'a" where
  "iso_tuple_cons isom = curry (abst isom)"


subsection \<open>Logical infrastructure for records\<close>

definition
  iso_tuple_surjective_proof_assist :: "'a \<Rightarrow> 'b \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "iso_tuple_surjective_proof_assist x y f \<longleftrightarrow> f x = y"

definition
  iso_tuple_update_accessor_cong_assist ::
    "(('b \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'a)) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "iso_tuple_update_accessor_cong_assist upd ac \<longleftrightarrow>
     (\<forall>f v. upd (\<lambda>x. f (ac v)) v = upd f v) \<and> (\<forall>v. upd id v = v)"

definition
  iso_tuple_update_accessor_eq_assist ::
    "(('b \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'a)) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool" where
  "iso_tuple_update_accessor_eq_assist upd ac v f v' x \<longleftrightarrow>
     upd f v = v' \<and> ac v = x \<and> iso_tuple_update_accessor_cong_assist upd ac"

lemma update_accessor_congruence_foldE:
  assumes uac: "iso_tuple_update_accessor_cong_assist upd ac"
    and r: "r = r'" and v: "ac r' = v'"
    and f: "\<And>v. v' = v \<Longrightarrow> f v = f' v"
  shows "upd f r = upd f' r'"
  using uac r v [symmetric]
  apply (subgoal_tac "upd (\<lambda>x. f (ac r')) r' = upd (\<lambda>x. f' (ac r')) r'")
   apply (simp add: iso_tuple_update_accessor_cong_assist_def)
  apply (simp add: f)
  done

lemma update_accessor_congruence_unfoldE:
  "iso_tuple_update_accessor_cong_assist upd ac \<Longrightarrow>
    r = r' \<Longrightarrow> ac r' = v' \<Longrightarrow> (\<And>v. v = v' \<Longrightarrow> f v = f' v) \<Longrightarrow>
    upd f r = upd f' r'"
  apply (erule(2) update_accessor_congruence_foldE)
  apply simp
  done

lemma iso_tuple_update_accessor_cong_assist_id:
  "iso_tuple_update_accessor_cong_assist upd ac \<Longrightarrow> upd id = id"
  by rule (simp add: iso_tuple_update_accessor_cong_assist_def)

lemma update_accessor_noopE:
  assumes uac: "iso_tuple_update_accessor_cong_assist upd ac"
    and ac: "f (ac x) = ac x"
  shows "upd f x = x"
  using uac
  by (simp add: ac iso_tuple_update_accessor_cong_assist_id [OF uac, unfolded id_def]
    cong: update_accessor_congruence_unfoldE [OF uac])

lemma update_accessor_noop_compE:
  assumes uac: "iso_tuple_update_accessor_cong_assist upd ac"
    and ac: "f (ac x) = ac x"
  shows "upd (g \<circ> f) x = upd g x"
  by (simp add: ac cong: update_accessor_congruence_unfoldE[OF uac])

lemma update_accessor_cong_assist_idI:
  "iso_tuple_update_accessor_cong_assist id id"
  by (simp add: iso_tuple_update_accessor_cong_assist_def)

lemma update_accessor_cong_assist_triv:
  "iso_tuple_update_accessor_cong_assist upd ac \<Longrightarrow>
    iso_tuple_update_accessor_cong_assist upd ac"
  by assumption

lemma update_accessor_accessor_eqE:
  "iso_tuple_update_accessor_eq_assist upd ac v f v' x \<Longrightarrow> ac v = x"
  by (simp add: iso_tuple_update_accessor_eq_assist_def)

lemma update_accessor_updator_eqE:
  "iso_tuple_update_accessor_eq_assist upd ac v f v' x \<Longrightarrow> upd f v = v'"
  by (simp add: iso_tuple_update_accessor_eq_assist_def)

lemma iso_tuple_update_accessor_eq_assist_idI:
  "v' = f v \<Longrightarrow> iso_tuple_update_accessor_eq_assist id id v f v' v"
  by (simp add: iso_tuple_update_accessor_eq_assist_def update_accessor_cong_assist_idI)

lemma iso_tuple_update_accessor_eq_assist_triv:
  "iso_tuple_update_accessor_eq_assist upd ac v f v' x \<Longrightarrow>
    iso_tuple_update_accessor_eq_assist upd ac v f v' x"
  by assumption

lemma iso_tuple_update_accessor_cong_from_eq:
  "iso_tuple_update_accessor_eq_assist upd ac v f v' x \<Longrightarrow>
    iso_tuple_update_accessor_cong_assist upd ac"
  by (simp add: iso_tuple_update_accessor_eq_assist_def)

lemma iso_tuple_surjective_proof_assistI:
  "f x = y \<Longrightarrow> iso_tuple_surjective_proof_assist x y f"
  by (simp add: iso_tuple_surjective_proof_assist_def)

lemma iso_tuple_surjective_proof_assist_idE:
  "iso_tuple_surjective_proof_assist x y id \<Longrightarrow> x = y"
  by (simp add: iso_tuple_surjective_proof_assist_def)

locale isomorphic_tuple =
  fixes isom :: "('a, 'b, 'c) tuple_isomorphism"
  assumes repr_inv: "\<And>x. abst isom (repr isom x) = x"
    and abst_inv: "\<And>y. repr isom (abst isom y) = y"
begin

lemma repr_inj: "repr isom x = repr isom y \<longleftrightarrow> x = y"
  by (auto dest: arg_cong [of "repr isom x" "repr isom y" "abst isom"]
    simp add: repr_inv)

lemma abst_inj: "abst isom x = abst isom y \<longleftrightarrow> x = y"
  by (auto dest: arg_cong [of "abst isom x" "abst isom y" "repr isom"]
    simp add: abst_inv)

lemmas simps = Let_def repr_inv abst_inv repr_inj abst_inj

lemma iso_tuple_access_update_fst_fst:
  "f \<circ> h g = j \<circ> f \<Longrightarrow>
    (f \<circ> iso_tuple_fst isom) \<circ> (iso_tuple_fst_update isom \<circ> h) g =
      j \<circ> (f \<circ> iso_tuple_fst isom)"
  by (clarsimp simp: iso_tuple_fst_update_def iso_tuple_fst_def simps
    fun_eq_iff)

lemma iso_tuple_access_update_snd_snd:
  "f \<circ> h g = j \<circ> f \<Longrightarrow>
    (f \<circ> iso_tuple_snd isom) \<circ> (iso_tuple_snd_update isom \<circ> h) g =
      j \<circ> (f \<circ> iso_tuple_snd isom)"
  by (clarsimp simp: iso_tuple_snd_update_def iso_tuple_snd_def simps
    fun_eq_iff)

lemma iso_tuple_access_update_fst_snd:
  "(f \<circ> iso_tuple_fst isom) \<circ> (iso_tuple_snd_update isom \<circ> h) g =
    id \<circ> (f \<circ> iso_tuple_fst isom)"
  by (clarsimp simp: iso_tuple_snd_update_def iso_tuple_fst_def simps
    fun_eq_iff)

lemma iso_tuple_access_update_snd_fst:
  "(f \<circ> iso_tuple_snd isom) \<circ> (iso_tuple_fst_update isom \<circ> h) g =
    id \<circ> (f \<circ> iso_tuple_snd isom)"
  by (clarsimp simp: iso_tuple_fst_update_def iso_tuple_snd_def simps
    fun_eq_iff)

lemma iso_tuple_update_swap_fst_fst:
  "h f \<circ> j g = j g \<circ> h f \<Longrightarrow>
    (iso_tuple_fst_update isom \<circ> h) f \<circ> (iso_tuple_fst_update isom \<circ> j) g =
      (iso_tuple_fst_update isom \<circ> j) g \<circ> (iso_tuple_fst_update isom \<circ> h) f"
  by (clarsimp simp: iso_tuple_fst_update_def simps apfst_compose fun_eq_iff)

lemma iso_tuple_update_swap_snd_snd:
  "h f \<circ> j g = j g \<circ> h f \<Longrightarrow>
    (iso_tuple_snd_update isom \<circ> h) f \<circ> (iso_tuple_snd_update isom \<circ> j) g =
      (iso_tuple_snd_update isom \<circ> j) g \<circ> (iso_tuple_snd_update isom \<circ> h) f"
  by (clarsimp simp: iso_tuple_snd_update_def simps apsnd_compose fun_eq_iff)

lemma iso_tuple_update_swap_fst_snd:
  "(iso_tuple_snd_update isom \<circ> h) f \<circ> (iso_tuple_fst_update isom \<circ> j) g =
    (iso_tuple_fst_update isom \<circ> j) g \<circ> (iso_tuple_snd_update isom \<circ> h) f"
  by (clarsimp simp: iso_tuple_fst_update_def iso_tuple_snd_update_def
    simps fun_eq_iff)

lemma iso_tuple_update_swap_snd_fst:
  "(iso_tuple_fst_update isom \<circ> h) f \<circ> (iso_tuple_snd_update isom \<circ> j) g =
    (iso_tuple_snd_update isom \<circ> j) g \<circ> (iso_tuple_fst_update isom \<circ> h) f"
  by (clarsimp simp: iso_tuple_fst_update_def iso_tuple_snd_update_def simps
    fun_eq_iff)

lemma iso_tuple_update_compose_fst_fst:
  "h f \<circ> j g = k (f \<circ> g) \<Longrightarrow>
    (iso_tuple_fst_update isom \<circ> h) f \<circ> (iso_tuple_fst_update isom \<circ> j) g =
      (iso_tuple_fst_update isom \<circ> k) (f \<circ> g)"
  by (clarsimp simp: iso_tuple_fst_update_def simps apfst_compose fun_eq_iff)

lemma iso_tuple_update_compose_snd_snd:
  "h f \<circ> j g = k (f \<circ> g) \<Longrightarrow>
    (iso_tuple_snd_update isom \<circ> h) f \<circ> (iso_tuple_snd_update isom \<circ> j) g =
      (iso_tuple_snd_update isom \<circ> k) (f \<circ> g)"
  by (clarsimp simp: iso_tuple_snd_update_def simps apsnd_compose fun_eq_iff)

lemma iso_tuple_surjective_proof_assist_step:
  "iso_tuple_surjective_proof_assist v a (iso_tuple_fst isom \<circ> f) \<Longrightarrow>
    iso_tuple_surjective_proof_assist v b (iso_tuple_snd isom \<circ> f) \<Longrightarrow>
    iso_tuple_surjective_proof_assist v (iso_tuple_cons isom a b) f"
  by (clarsimp simp: iso_tuple_surjective_proof_assist_def simps
    iso_tuple_fst_def iso_tuple_snd_def iso_tuple_cons_def)

lemma iso_tuple_fst_update_accessor_cong_assist:
  assumes "iso_tuple_update_accessor_cong_assist f g"
  shows "iso_tuple_update_accessor_cong_assist
    (iso_tuple_fst_update isom \<circ> f) (g \<circ> iso_tuple_fst isom)"
proof -
  from assms have "f id = id"
    by (rule iso_tuple_update_accessor_cong_assist_id)
  with assms show ?thesis
    by (clarsimp simp: iso_tuple_update_accessor_cong_assist_def simps
      iso_tuple_fst_update_def iso_tuple_fst_def)
qed

lemma iso_tuple_snd_update_accessor_cong_assist:
  assumes "iso_tuple_update_accessor_cong_assist f g"
  shows "iso_tuple_update_accessor_cong_assist
    (iso_tuple_snd_update isom \<circ> f) (g \<circ> iso_tuple_snd isom)"
proof -
  from assms have "f id = id"
    by (rule iso_tuple_update_accessor_cong_assist_id)
  with assms show ?thesis
    by (clarsimp simp: iso_tuple_update_accessor_cong_assist_def simps
      iso_tuple_snd_update_def iso_tuple_snd_def)
qed

lemma iso_tuple_fst_update_accessor_eq_assist:
  assumes "iso_tuple_update_accessor_eq_assist f g a u a' v"
  shows "iso_tuple_update_accessor_eq_assist
    (iso_tuple_fst_update isom \<circ> f) (g \<circ> iso_tuple_fst isom)
    (iso_tuple_cons isom a b) u (iso_tuple_cons isom a' b) v"
proof -
  from assms have "f id = id"
    by (auto simp add: iso_tuple_update_accessor_eq_assist_def
      intro: iso_tuple_update_accessor_cong_assist_id)
  with assms show ?thesis
    by (clarsimp simp: iso_tuple_update_accessor_eq_assist_def
      iso_tuple_fst_update_def iso_tuple_fst_def
      iso_tuple_update_accessor_cong_assist_def iso_tuple_cons_def simps)
qed

lemma iso_tuple_snd_update_accessor_eq_assist:
  assumes "iso_tuple_update_accessor_eq_assist f g b u b' v"
  shows "iso_tuple_update_accessor_eq_assist
    (iso_tuple_snd_update isom \<circ> f) (g \<circ> iso_tuple_snd isom)
    (iso_tuple_cons isom a b) u (iso_tuple_cons isom a b') v"
proof -
  from assms have "f id = id"
    by (auto simp add: iso_tuple_update_accessor_eq_assist_def
      intro: iso_tuple_update_accessor_cong_assist_id)
  with assms show ?thesis
    by (clarsimp simp: iso_tuple_update_accessor_eq_assist_def
      iso_tuple_snd_update_def iso_tuple_snd_def
      iso_tuple_update_accessor_cong_assist_def iso_tuple_cons_def simps)
qed

lemma iso_tuple_cons_conj_eqI:
  "a = c \<and> b = d \<and> P \<longleftrightarrow> Q \<Longrightarrow>
    iso_tuple_cons isom a b = iso_tuple_cons isom c d \<and> P \<longleftrightarrow> Q"
  by (clarsimp simp: iso_tuple_cons_def simps)

lemmas intros =
  iso_tuple_access_update_fst_fst
  iso_tuple_access_update_snd_snd
  iso_tuple_access_update_fst_snd
  iso_tuple_access_update_snd_fst
  iso_tuple_update_swap_fst_fst
  iso_tuple_update_swap_snd_snd
  iso_tuple_update_swap_fst_snd
  iso_tuple_update_swap_snd_fst
  iso_tuple_update_compose_fst_fst
  iso_tuple_update_compose_snd_snd
  iso_tuple_surjective_proof_assist_step
  iso_tuple_fst_update_accessor_eq_assist
  iso_tuple_snd_update_accessor_eq_assist
  iso_tuple_fst_update_accessor_cong_assist
  iso_tuple_snd_update_accessor_cong_assist
  iso_tuple_cons_conj_eqI

end

lemma isomorphic_tuple_intro:
  fixes repr abst
  assumes repr_inj: "\<And>x y. repr x = repr y \<longleftrightarrow> x = y"
    and abst_inv: "\<And>z. repr (abst z) = z"
    and v: "v \<equiv> Tuple_Isomorphism repr abst"
  shows "isomorphic_tuple v"
proof
  fix x have "repr (abst (repr x)) = repr x"
    by (simp add: abst_inv)
  then show "Record.abst v (Record.repr v x) = x"
    by (simp add: v repr_inj)
next
  fix y
  show "Record.repr v (Record.abst v y) = y"
    by (simp add: v) (fact abst_inv)
qed

definition
  "tuple_iso_tuple \<equiv> Tuple_Isomorphism id id"

lemma tuple_iso_tuple:
  "isomorphic_tuple tuple_iso_tuple"
  by (simp add: isomorphic_tuple_intro [OF _ _ reflexive] tuple_iso_tuple_def)

lemma refl_conj_eq: "Q = R \<Longrightarrow> P \<and> Q \<longleftrightarrow> P \<and> R"
  by simp

lemma iso_tuple_UNIV_I: "x \<in> UNIV \<equiv> True"
  by simp

lemma iso_tuple_True_simp: "(True \<Longrightarrow> PROP P) \<equiv> PROP P"
  by simp

lemma prop_subst: "s = t \<Longrightarrow> PROP P t \<Longrightarrow> PROP P s"
  by simp

lemma K_record_comp: "(\<lambda>x. c) \<circ> f = (\<lambda>x. c)"
  by (simp add: comp_def)


subsection \<open>Concrete record syntax\<close>

nonterminal
  ident and
  field_type and
  field_types and
  field and
  fields and
  field_update and
  field_updates

syntax
  "_constify"           :: "id => ident"                        (\<open>_\<close>)
  "_constify"           :: "longid => ident"                    (\<open>_\<close>)

  "_field_type"         :: "ident => type => field_type"        (\<open>(\<open>indent=2 notation=\<open>infix field type\<close>\<close>_ ::/ _)\<close>)
  ""                    :: "field_type => field_types"          (\<open>_\<close>)
  "_field_types"        :: "field_type => field_types => field_types"    (\<open>_,/ _\<close>)
  "_record_type"        :: "field_types => type"                (\<open>(\<open>indent=3 notation=\<open>mixfix record type\<close>\<close>\<lparr>_\<rparr>)\<close>)
  "_record_type_scheme" :: "field_types => type => type"        (\<open>(\<open>indent=3 notation=\<open>mixfix record type\<close>\<close>\<lparr>_,/ (2\<dots> ::/ _)\<rparr>)\<close>)

  "_field"              :: "ident => 'a => field"               (\<open>(\<open>indent=2 notation=\<open>infix field value\<close>\<close>_ =/ _)\<close>)
  ""                    :: "field => fields"                    (\<open>_\<close>)
  "_fields"             :: "field => fields => fields"          (\<open>_,/ _\<close>)
  "_record"             :: "fields => 'a"                       (\<open>(\<open>indent=3 notation=\<open>mixfix record value\<close>\<close>\<lparr>_\<rparr>)\<close>)
  "_record_scheme"      :: "fields => 'a => 'a"                 (\<open>(\<open>indent=3 notation=\<open>mixfix record value\<close>\<close>\<lparr>_,/ (2\<dots> =/ _)\<rparr>)\<close>)

  "_field_update"       :: "ident => 'a => field_update"        (\<open>(\<open>indent=2 notation=\<open>infix field update\<close>\<close>_ :=/ _)\<close>)
  ""                    :: "field_update => field_updates"      (\<open>_\<close>)
  "_field_updates"      :: "field_update => field_updates => field_updates"  (\<open>_,/ _\<close>)
  "_record_update"      :: "'a => field_updates => 'b"          (\<open>_/(\<open>indent=3 notation=\<open>mixfix record update\<close>\<close>\<lparr>_\<rparr>)\<close> [900, 0] 900)

syntax (ASCII)
  "_record_type"        :: "field_types => type"                (\<open>(\<open>indent=3 notation=\<open>mixfix record type\<close>\<close>'(| _ |'))\<close>)
  "_record_type_scheme" :: "field_types => type => type"        (\<open>(\<open>indent=3 notation=\<open>mixfix record type\<close>\<close>'(| _,/ (2... ::/ _) |'))\<close>)
  "_record"             :: "fields => 'a"                       (\<open>(\<open>indent=3 notation=\<open>mixfix record value\<close>\<close>'(| _ |'))\<close>)
  "_record_scheme"      :: "fields => 'a => 'a"                 (\<open>(\<open>indent=3 notation=\<open>mixfix record value\<close>\<close>'(| _,/ (2... =/ _) |'))\<close>)
  "_record_update"      :: "'a => field_updates => 'b"          (\<open>_/(\<open>indent=3 notation=\<open>mixfix record update\<close>\<close>'(| _ |'))\<close> [900, 0] 900)


subsection \<open>Record package\<close>

ML_file \<open>Tools/record.ML\<close>

hide_const (open) Tuple_Isomorphism repr abst iso_tuple_fst iso_tuple_snd
  iso_tuple_fst_update iso_tuple_snd_update iso_tuple_cons
  iso_tuple_surjective_proof_assist iso_tuple_update_accessor_cong_assist
  iso_tuple_update_accessor_eq_assist tuple_iso_tuple

end
