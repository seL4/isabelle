(*  Title:      HOL/Record.thy
    Author:     Wolfgang Naraschewski, TU Muenchen
    Author:     Markus Wenzel, TU Muenchen
    Author:     Norbert Schirmer, TU Muenchen
    Author:     Thomas Sewell, NICTA
    Author:     Florian Haftmann, TU Muenchen
*)

header {* Extensible records with structural subtyping *}

theory Record
imports Plain Quickcheck_Narrowing
keywords "record" :: thy_decl
begin

subsection {* Introduction *}

text {*
  Records are isomorphic to compound tuple types. To implement
  efficient records, we make this isomorphism explicit. Consider the
  record access/update simplification @{text "alpha (beta_update f
  rec) = alpha rec"} for distinct fields alpha and beta of some record
  rec with n fields. There are @{text "n ^ 2"} such theorems, which
  prohibits storage of all of them for large n. The rules can be
  proved on the fly by case decomposition and simplification in O(n)
  time. By creating O(n) isomorphic-tuple types while defining the
  record, however, we can prove the access/update simplification in
  @{text "O(log(n)^2)"} time.

  The O(n) cost of case decomposition is not because O(n) steps are
  taken, but rather because the resulting rule must contain O(n) new
  variables and an O(n) size concrete record construction. To sidestep
  this cost, we would like to avoid case decomposition in proving
  access/update theorems.

  Record types are defined as isomorphic to tuple types. For instance,
  a record type with fields @{text "'a"}, @{text "'b"}, @{text "'c"}
  and @{text "'d"} might be introduced as isomorphic to @{text "'a \<times>
  ('b \<times> ('c \<times> 'd))"}. If we balance the tuple tree to @{text "('a \<times>
  'b) \<times> ('c \<times> 'd)"} then accessors can be defined by converting to the
  underlying type then using O(log(n)) fst or snd operations.
  Updators can be defined similarly, if we introduce a @{text
  "fst_update"} and @{text "snd_update"} function. Furthermore, we can
  prove the access/update theorem in O(log(n)) steps by using simple
  rewrites on fst, snd, @{text "fst_update"} and @{text "snd_update"}.

  The catch is that, although O(log(n)) steps were taken, the
  underlying type we converted to is a tuple tree of size
  O(n). Processing this term type wastes performance. We avoid this
  for large n by taking each subtree of size K and defining a new type
  isomorphic to that tuple subtree. A record can now be defined as
  isomorphic to a tuple tree of these O(n/K) new types, or, if @{text
  "n > K*K"}, we can repeat the process, until the record can be
  defined in terms of a tuple tree of complexity less than the
  constant K.

  If we prove the access/update theorem on this type with the
  analogous steps to the tuple tree, we consume @{text "O(log(n)^2)"}
  time as the intermediate terms are @{text "O(log(n))"} in size and
  the types needed have size bounded by K.  To enable this analogous
  traversal, we define the functions seen below: @{text
  "iso_tuple_fst"}, @{text "iso_tuple_snd"}, @{text "iso_tuple_fst_update"}
  and @{text "iso_tuple_snd_update"}. These functions generalise tuple
  operations by taking a parameter that encapsulates a tuple
  isomorphism.  The rewrites needed on these functions now need an
  additional assumption which is that the isomorphism works.

  These rewrites are typically used in a structured way. They are here
  presented as the introduction rule @{text "isomorphic_tuple.intros"}
  rather than as a rewrite rule set. The introduction form is an
  optimisation, as net matching can be performed at one term location
  for each step rather than the simplifier searching the term for
  possible pattern matches. The rule set is used as it is viewed
  outside the locale, with the locale assumption (that the isomorphism
  is valid) left as a rule assumption. All rules are structured to aid
  net matching, using either a point-free form or an encapsulating
  predicate.
*}

subsection {* Operators and lemmas for types isomorphic to tuples *}

datatype ('a, 'b, 'c) tuple_isomorphism =
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


subsection {* Logical infrastructure for records *}

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
  "f o h g = j o f \<Longrightarrow>
    (f o iso_tuple_fst isom) o (iso_tuple_fst_update isom o h) g =
      j o (f o iso_tuple_fst isom)"
  by (clarsimp simp: iso_tuple_fst_update_def iso_tuple_fst_def simps
    fun_eq_iff)

lemma iso_tuple_access_update_snd_snd:
  "f o h g = j o f \<Longrightarrow>
    (f o iso_tuple_snd isom) o (iso_tuple_snd_update isom o h) g =
      j o (f o iso_tuple_snd isom)"
  by (clarsimp simp: iso_tuple_snd_update_def iso_tuple_snd_def simps
    fun_eq_iff)

lemma iso_tuple_access_update_fst_snd:
  "(f o iso_tuple_fst isom) o (iso_tuple_snd_update isom o h) g =
    id o (f o iso_tuple_fst isom)"
  by (clarsimp simp: iso_tuple_snd_update_def iso_tuple_fst_def simps
    fun_eq_iff)

lemma iso_tuple_access_update_snd_fst:
  "(f o iso_tuple_snd isom) o (iso_tuple_fst_update isom o h) g =
    id o (f o iso_tuple_snd isom)"
  by (clarsimp simp: iso_tuple_fst_update_def iso_tuple_snd_def simps
    fun_eq_iff)

lemma iso_tuple_update_swap_fst_fst:
  "h f o j g = j g o h f \<Longrightarrow>
    (iso_tuple_fst_update isom o h) f o (iso_tuple_fst_update isom o j) g =
      (iso_tuple_fst_update isom o j) g o (iso_tuple_fst_update isom o h) f"
  by (clarsimp simp: iso_tuple_fst_update_def simps apfst_compose fun_eq_iff)

lemma iso_tuple_update_swap_snd_snd:
  "h f o j g = j g o h f \<Longrightarrow>
    (iso_tuple_snd_update isom o h) f o (iso_tuple_snd_update isom o j) g =
      (iso_tuple_snd_update isom o j) g o (iso_tuple_snd_update isom o h) f"
  by (clarsimp simp: iso_tuple_snd_update_def simps apsnd_compose fun_eq_iff)

lemma iso_tuple_update_swap_fst_snd:
  "(iso_tuple_snd_update isom o h) f o (iso_tuple_fst_update isom o j) g =
    (iso_tuple_fst_update isom o j) g o (iso_tuple_snd_update isom o h) f"
  by (clarsimp simp: iso_tuple_fst_update_def iso_tuple_snd_update_def
    simps fun_eq_iff)

lemma iso_tuple_update_swap_snd_fst:
  "(iso_tuple_fst_update isom o h) f o (iso_tuple_snd_update isom o j) g =
    (iso_tuple_snd_update isom o j) g o (iso_tuple_fst_update isom o h) f"
  by (clarsimp simp: iso_tuple_fst_update_def iso_tuple_snd_update_def simps
    fun_eq_iff)

lemma iso_tuple_update_compose_fst_fst:
  "h f o j g = k (f o g) \<Longrightarrow>
    (iso_tuple_fst_update isom o h) f o (iso_tuple_fst_update isom o j) g =
      (iso_tuple_fst_update isom o k) (f o g)"
  by (clarsimp simp: iso_tuple_fst_update_def simps apfst_compose fun_eq_iff)

lemma iso_tuple_update_compose_snd_snd:
  "h f o j g = k (f o g) \<Longrightarrow>
    (iso_tuple_snd_update isom o h) f o (iso_tuple_snd_update isom o j) g =
      (iso_tuple_snd_update isom o k) (f o g)"
  by (clarsimp simp: iso_tuple_snd_update_def simps apsnd_compose fun_eq_iff)

lemma iso_tuple_surjective_proof_assist_step:
  "iso_tuple_surjective_proof_assist v a (iso_tuple_fst isom o f) \<Longrightarrow>
    iso_tuple_surjective_proof_assist v b (iso_tuple_snd isom o f) \<Longrightarrow>
    iso_tuple_surjective_proof_assist v (iso_tuple_cons isom a b) f"
  by (clarsimp simp: iso_tuple_surjective_proof_assist_def simps
    iso_tuple_fst_def iso_tuple_snd_def iso_tuple_cons_def)

lemma iso_tuple_fst_update_accessor_cong_assist:
  assumes "iso_tuple_update_accessor_cong_assist f g"
  shows "iso_tuple_update_accessor_cong_assist
    (iso_tuple_fst_update isom o f) (g o iso_tuple_fst isom)"
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
    (iso_tuple_snd_update isom o f) (g o iso_tuple_snd isom)"
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
    (iso_tuple_fst_update isom o f) (g o iso_tuple_fst isom)
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
    (iso_tuple_snd_update isom o f) (g o iso_tuple_snd isom)
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

lemma iso_tuple_UNIV_I [no_atp]: "x \<in> UNIV \<equiv> True"
  by simp

lemma iso_tuple_True_simp: "(True \<Longrightarrow> PROP P) \<equiv> PROP P"
  by simp

lemma prop_subst: "s = t \<Longrightarrow> PROP P t \<Longrightarrow> PROP P s"
  by simp

lemma K_record_comp: "(\<lambda>x. c) \<circ> f = (\<lambda>x. c)"
  by (simp add: comp_def)

lemma o_eq_dest_lhs: "a o b = c \<Longrightarrow> a (b v) = c v"
  by clarsimp

lemma o_eq_id_dest: "a o b = id o c \<Longrightarrow> a (b v) = c v"
  by clarsimp


subsection {* Concrete record syntax *}

nonterminal
  ident and
  field_type and
  field_types and
  field and
  fields and
  field_update and
  field_updates

syntax
  "_constify"           :: "id => ident"                        ("_")
  "_constify"           :: "longid => ident"                    ("_")

  "_field_type"         :: "ident => type => field_type"        ("(2_ ::/ _)")
  ""                    :: "field_type => field_types"          ("_")
  "_field_types"        :: "field_type => field_types => field_types"    ("_,/ _")
  "_record_type"        :: "field_types => type"                ("(3'(| _ |'))")
  "_record_type_scheme" :: "field_types => type => type"        ("(3'(| _,/ (2... ::/ _) |'))")

  "_field"              :: "ident => 'a => field"               ("(2_ =/ _)")
  ""                    :: "field => fields"                    ("_")
  "_fields"             :: "field => fields => fields"          ("_,/ _")
  "_record"             :: "fields => 'a"                       ("(3'(| _ |'))")
  "_record_scheme"      :: "fields => 'a => 'a"                 ("(3'(| _,/ (2... =/ _) |'))")

  "_field_update"       :: "ident => 'a => field_update"        ("(2_ :=/ _)")
  ""                    :: "field_update => field_updates"      ("_")
  "_field_updates"      :: "field_update => field_updates => field_updates"  ("_,/ _")
  "_record_update"      :: "'a => field_updates => 'b"          ("_/(3'(| _ |'))" [900, 0] 900)

syntax (xsymbols)
  "_record_type"        :: "field_types => type"                ("(3\<lparr>_\<rparr>)")
  "_record_type_scheme" :: "field_types => type => type"        ("(3\<lparr>_,/ (2\<dots> ::/ _)\<rparr>)")
  "_record"             :: "fields => 'a"                       ("(3\<lparr>_\<rparr>)")
  "_record_scheme"      :: "fields => 'a => 'a"                 ("(3\<lparr>_,/ (2\<dots> =/ _)\<rparr>)")
  "_record_update"      :: "'a => field_updates => 'b"          ("_/(3\<lparr>_\<rparr>)" [900, 0] 900)


subsection {* Record package *}

ML_file "Tools/record.ML" setup Record.setup

hide_const (open) Tuple_Isomorphism repr abst iso_tuple_fst iso_tuple_snd
  iso_tuple_fst_update iso_tuple_snd_update iso_tuple_cons
  iso_tuple_surjective_proof_assist iso_tuple_update_accessor_cong_assist
  iso_tuple_update_accessor_eq_assist tuple_iso_tuple

end
