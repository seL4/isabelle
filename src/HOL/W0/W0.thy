(*  Title:      HOL/W0/W0.thy
    ID:         $Id$
    Author:     Dieter Nazareth, Tobias Nipkow, Thomas Stauner, and Markus Wenzel
    License:    GPL (GNU GENERAL PUBLIC LICENSE)
*)

theory W0 = Main:

section {* Universal error monad *}

datatype 'a maybe = Ok 'a | Fail

constdefs
  bind :: "'a maybe \<Rightarrow> ('a \<Rightarrow> 'b maybe) \<Rightarrow> 'b maybe"    (infixl "\<bind>" 60)
  "m \<bind> f \<equiv> case m of Ok r \<Rightarrow> f r | Fail \<Rightarrow> Fail"

syntax
  "_bind" :: "patterns \<Rightarrow> 'a maybe \<Rightarrow> 'b \<Rightarrow> 'c"    ("(_ := _;//_)" 0)
translations
  "P := E; F" == "E \<bind> (\<lambda>P. F)"

lemma bind_Ok [simp]: "(Ok s) \<bind> f = (f s)"
  by (simp add: bind_def)

lemma bind_Fail [simp]: "Fail \<bind> f = Fail"
  by (simp add: bind_def)

lemma split_bind:
    "P (res \<bind> f) = ((res = Fail \<longrightarrow> P Fail) \<and> (\<forall>s. res = Ok s \<longrightarrow> P (f s)))"
  by (induct res) simp_all

lemma split_bind_asm:
  "P (res \<bind> f) = (\<not> (res = Fail \<and> \<not> P Fail \<or> (\<exists>s. res = Ok s \<and> \<not> P (f s))))"
  by (simp split: split_bind)

lemmas bind_splits = split_bind split_bind_asm

lemma bind_eq_Fail [simp]:
  "((m \<bind> f) = Fail) = ((m = Fail) \<or> (\<exists>p. m = Ok p \<and> f p = Fail))"
  by (simp split: split_bind)

lemma rotate_Ok: "(y = Ok x) = (Ok x = y)"
  by (rule eq_sym_conv)


section {* MiniML-types and type substitutions *}

axclass type_struct \<subseteq> type
  -- {* new class for structures containing type variables *}

datatype "typ" = TVar nat | TFun "typ" "typ"    (infixr "->" 70)
  -- {* type expressions *}

types subst = "nat => typ"
  -- {* type variable substitution *}

instance "typ" :: type_struct ..
instance list :: (type_struct) type_struct ..
instance fun :: (type, type_struct) type_struct ..


subsection {* Substitutions *}

consts
  app_subst :: "subst \<Rightarrow> 'a::type_struct \<Rightarrow> 'a::type_struct"    ("$")
  -- {* extension of substitution to type structures *}
primrec
  app_subst_TVar: "$s (TVar n) = s n"
  app_subst_Fun: "$s (t1 -> t2) = $s t1 -> $s t2"

defs (overloaded)
  app_subst_list: "$s \<equiv> map ($s)"

consts
  free_tv :: "'a::type_struct \<Rightarrow> nat set"
  -- {* @{text "free_tv s"}: the type variables occuring freely in the type structure @{text s} *}

primrec
  "free_tv (TVar m) = {m}"
  "free_tv (t1 -> t2) = free_tv t1 \<union> free_tv t2"

primrec
  "free_tv [] = {}"
  "free_tv (x # xs) = free_tv x \<union> free_tv xs"

constdefs
  dom :: "subst \<Rightarrow> nat set"
  "dom s \<equiv> {n. s n \<noteq> TVar n}"
  -- {* domain of a substitution *}

  cod :: "subst \<Rightarrow> nat set"
  "cod s \<equiv> \<Union>m \<in> dom s. free_tv (s m)"
  -- {* codomain of a substitutions: the introduced variables *}

defs
  free_tv_subst: "free_tv s \<equiv> dom s \<union> cod s"

text {*
  @{text "new_tv s n"} checks whether @{text n} is a new type variable
  wrt.\ a type structure @{text s}, i.e.\ whether @{text n} is greater
  than any type variable occuring in the type structure.
*}

constdefs
  new_tv :: "nat \<Rightarrow> 'a::type_struct \<Rightarrow> bool"
  "new_tv n ts \<equiv> \<forall>m. m \<in> free_tv ts \<longrightarrow> m < n"


subsubsection {* Identity substitution *}

constdefs
  id_subst :: subst
  "id_subst \<equiv> \<lambda>n. TVar n"

lemma app_subst_id_te [simp]:
  "$id_subst = (\<lambda>t::typ. t)"
  -- {* application of @{text id_subst} does not change type expression *}
proof
  fix t :: "typ"
  show "$id_subst t = t"
    by (induct t) (simp_all add: id_subst_def)
qed

lemma app_subst_id_tel [simp]: "$id_subst = (\<lambda>ts::typ list. ts)"
  -- {* application of @{text id_subst} does not change list of type expressions *}
proof
  fix ts :: "typ list"
  show "$id_subst ts = ts"
    by (induct ts) (simp_all add: app_subst_list)
qed

lemma o_id_subst [simp]: "$s o id_subst = s"
  by (rule ext) (simp add: id_subst_def)

lemma dom_id_subst [simp]: "dom id_subst = {}"
  by (simp add: dom_def id_subst_def empty_def)

lemma cod_id_subst [simp]: "cod id_subst = {}"
  by (simp add: cod_def)

lemma free_tv_id_subst [simp]: "free_tv id_subst = {}"
  by (simp add: free_tv_subst)


lemma cod_app_subst [simp]:
  assumes free: "v \<in> free_tv (s n)"
    and neq: "v \<noteq> n"
  shows "v \<in> cod s"
proof -
  have "s n \<noteq> TVar n"
  proof
    assume "s n = TVar n"
    with free have "v = n" by simp
    with neq show False ..
  qed
  with free show ?thesis
    by (auto simp add: dom_def cod_def)
qed

lemma subst_comp_te: "$g ($f t :: typ) = $(\<lambda>x. $g (f x)) t"
  -- {* composition of substitutions *}
  by (induct t) simp_all

lemma subst_comp_tel: "$g ($f ts :: typ list) = $(\<lambda>x. $g (f x)) ts"
  by (induct ts) (simp_all add: app_subst_list subst_comp_te)


lemma app_subst_Nil [simp]: "$s [] = []"
  by (simp add: app_subst_list)

lemma app_subst_Cons [simp]: "$s (t # ts) = ($s t) # ($s ts)"
  by (simp add: app_subst_list)

lemma new_tv_TVar [simp]: "new_tv n (TVar m) = (m < n)"
  by (simp add: new_tv_def)

lemma new_tv_Fun [simp]:
  "new_tv n (t1 -> t2) = (new_tv n t1 \<and> new_tv n t2)"
  by (auto simp add: new_tv_def)

lemma new_tv_Nil [simp]: "new_tv n []"
  by (simp add: new_tv_def)

lemma new_tv_Cons [simp]: "new_tv n (t # ts) = (new_tv n t \<and> new_tv n ts)"
  by (auto simp add: new_tv_def)

lemma new_tv_id_subst [simp]: "new_tv n id_subst"
  by (simp add: id_subst_def new_tv_def free_tv_subst dom_def cod_def)

lemma new_tv_subst:
  "new_tv n s =
    ((\<forall>m. n \<le> m \<longrightarrow> s m = TVar m) \<and>
     (\<forall>l. l < n \<longrightarrow> new_tv n (s l)))"
  apply (unfold new_tv_def)
  apply (tactic "safe_tac HOL_cs")
  -- {* @{text \<Longrightarrow>} *}
    apply (tactic {* fast_tac (HOL_cs addDs [leD] addss (simpset()
      addsimps [thm "free_tv_subst", thm "dom_def"])) 1 *})
   apply (subgoal_tac "m \<in> cod s \<or> s l = TVar l")
    apply (tactic "safe_tac HOL_cs")
     apply (tactic {* fast_tac (HOL_cs addDs [UnI2] addss (simpset()
       addsimps [thm "free_tv_subst"])) 1 *})
    apply (drule_tac P = "\<lambda>x. m \<in> free_tv x" in subst, assumption)
    apply simp
   apply (tactic {* fast_tac (set_cs addss (simpset()
     addsimps [thm "free_tv_subst", thm "cod_def", thm "dom_def"])) 1 *})
  -- {* @{text \<Longleftarrow>} *}
  apply (unfold free_tv_subst cod_def dom_def)
  apply (tactic "safe_tac set_cs")
   apply (cut_tac m = m and n = n in less_linear)
   apply (tactic "fast_tac (HOL_cs addSIs [less_or_eq_imp_le]) 1")
  apply (cut_tac m = ma and n = n in less_linear)
  apply (fast intro!: less_or_eq_imp_le)
  done

lemma new_tv_list: "new_tv n x = (\<forall>y \<in> set x. new_tv n y)"
  by (induct x) simp_all

lemma subst_te_new_tv [simp]:
  "new_tv n (t::typ) \<longrightarrow> $(\<lambda>x. if x = n then t' else s x) t = $s t"
  -- {* substitution affects only variables occurring freely *}
  by (induct t) simp_all

lemma subst_tel_new_tv [simp]:
  "new_tv n (ts::typ list) \<longrightarrow> $(\<lambda>x. if x = n then t else s x) ts = $s ts"
  by (induct ts) simp_all

lemma new_tv_le: "n \<le> m \<Longrightarrow> new_tv n (t::typ) \<Longrightarrow> new_tv m t"
  -- {* all greater variables are also new *}
proof (induct t)
  case (TVar n)
  thus ?case by (auto intro: less_le_trans)
next
  case TFun
  thus ?case by simp
qed

lemma [simp]: "new_tv n t \<Longrightarrow> new_tv (Suc n) (t::typ)"
  by (rule lessI [THEN less_imp_le [THEN new_tv_le]])

lemma new_tv_list_le:
  "n \<le> m \<Longrightarrow> new_tv n (ts::typ list) \<Longrightarrow> new_tv m ts"
proof (induct ts)
  case Nil
  thus ?case by simp
next
  case Cons
  thus ?case by (auto intro: new_tv_le)
qed

lemma [simp]: "new_tv n ts \<Longrightarrow> new_tv (Suc n) (ts::typ list)"
  by (rule lessI [THEN less_imp_le [THEN new_tv_list_le]])

lemma new_tv_subst_le: "n \<le> m \<Longrightarrow> new_tv n (s::subst) \<Longrightarrow> new_tv m s"
  apply (simp add: new_tv_subst)
  apply clarify
  apply (rule_tac P = "l < n" and Q = "n <= l" in disjE)
    apply clarify
    apply (simp_all add: new_tv_le)
  done

lemma [simp]: "new_tv n s \<Longrightarrow> new_tv (Suc n) (s::subst)"
  by (rule lessI [THEN less_imp_le [THEN new_tv_subst_le]])

lemma new_tv_subst_var:
    "n < m \<Longrightarrow> new_tv m (s::subst) \<Longrightarrow> new_tv m (s n)"
  -- {* @{text new_tv} property remains if a substitution is applied *}
  by (simp add: new_tv_subst)

lemma new_tv_subst_te [simp]:
    "new_tv n s \<Longrightarrow> new_tv n (t::typ) \<Longrightarrow> new_tv n ($s t)"
  by (induct t) (auto simp add: new_tv_subst)

lemma new_tv_subst_tel [simp]:
    "new_tv n s \<Longrightarrow> new_tv n (ts::typ list) \<Longrightarrow> new_tv n ($s ts)"
  by (induct ts) (fastsimp simp add: new_tv_subst)+

lemma new_tv_Suc_list: "new_tv n ts --> new_tv (Suc n) (TVar n # ts)"
  -- {* auxilliary lemma *}
  by (simp add: new_tv_list)

lemma new_tv_subst_comp_1 [simp]:
    "new_tv n (s::subst) \<Longrightarrow> new_tv n r \<Longrightarrow> new_tv n ($r o s)"
  -- {* composition of substitutions preserves @{text new_tv} proposition *}
  by (simp add: new_tv_subst)

lemma new_tv_subst_comp_2 [simp]:
    "new_tv n (s::subst) \<Longrightarrow> new_tv n r \<Longrightarrow> new_tv n (\<lambda>v. $r (s v))"
  by (simp add: new_tv_subst)

lemma new_tv_not_free_tv [simp]: "new_tv n ts \<Longrightarrow> n \<notin> free_tv ts"
  -- {* new type variables do not occur freely in a type structure *}
  by (auto simp add: new_tv_def)

lemma ftv_mem_sub_ftv_list [simp]:
    "(t::typ) \<in> set ts \<Longrightarrow> free_tv t \<subseteq> free_tv ts"
  by (induct ts) auto

text {*
  If two substitutions yield the same result if applied to a type
  structure the substitutions coincide on the free type variables
  occurring in the type structure.
*}

lemma eq_subst_te_eq_free:
    "$s1 (t::typ) = $s2 t \<Longrightarrow> n \<in> free_tv t \<Longrightarrow> s1 n = s2 n"
  by (induct t) auto

lemma eq_free_eq_subst_te:
    "(\<forall>n. n \<in> free_tv t --> s1 n = s2 n) \<Longrightarrow> $s1 (t::typ) = $s2 t"
  by (induct t) auto

lemma eq_subst_tel_eq_free:
    "$s1 (ts::typ list) = $s2 ts \<Longrightarrow> n \<in> free_tv ts \<Longrightarrow> s1 n = s2 n"
  by (induct ts) (auto intro: eq_subst_te_eq_free)

lemma eq_free_eq_subst_tel:
    "(\<forall>n. n \<in> free_tv ts --> s1 n = s2 n) \<Longrightarrow> $s1 (ts::typ list) = $s2 ts"
  by (induct ts) (auto intro: eq_free_eq_subst_te)

text {*
  \medskip Some useful lemmas.
*}

lemma codD: "v \<in> cod s \<Longrightarrow> v \<in> free_tv s"
  by (simp add: free_tv_subst)

lemma not_free_impl_id: "x \<notin> free_tv s \<Longrightarrow> s x = TVar x"
  by (simp add: free_tv_subst dom_def)

lemma free_tv_le_new_tv: "new_tv n t \<Longrightarrow> m \<in> free_tv t \<Longrightarrow> m < n"
  by (unfold new_tv_def) fast

lemma free_tv_subst_var: "free_tv (s (v::nat)) \<le> insert v (cod s)"
  by (cases "v \<in> dom s") (auto simp add: cod_def dom_def)

lemma free_tv_app_subst_te: "free_tv ($s (t::typ)) \<subseteq> cod s \<union> free_tv t"
  by (induct t) (auto simp add: free_tv_subst_var)

lemma free_tv_app_subst_tel: "free_tv ($s (ts::typ list)) \<subseteq> cod s \<union> free_tv ts"
  apply (induct ts)
   apply simp
  apply (cut_tac free_tv_app_subst_te)
  apply fastsimp
  done

lemma free_tv_comp_subst:
    "free_tv (\<lambda>u::nat. $s1 (s2 u) :: typ) \<subseteq> free_tv s1 \<union> free_tv s2"
  apply (unfold free_tv_subst dom_def)
  apply (tactic {*
    fast_tac (set_cs addSDs [thm "free_tv_app_subst_te" RS subsetD,
    thm "free_tv_subst_var" RS subsetD]
    addss (simpset() delsimps bex_simps
    addsimps [thm "cod_def", thm "dom_def"])) 1 *})
  done


subsection {* Most general unifiers *}

consts
  mgu :: "typ \<Rightarrow> typ \<Rightarrow> subst maybe"
axioms
  mgu_eq [simp]: "mgu t1 t2 = Ok u \<Longrightarrow> $u t1 = $u t2"
  mgu_mg [simp]: "mgu t1 t2 = Ok u \<Longrightarrow> $s t1 = $s t2 \<Longrightarrow> \<exists>r. s = $r o u"
  mgu_Ok: "$s t1 = $s t2 \<Longrightarrow> \<exists>u. mgu t1 t2 = Ok u"
  mgu_free [simp]: "mgu t1 t2 = Ok u \<Longrightarrow> free_tv u \<subseteq> free_tv t1 \<union> free_tv t2"

lemma mgu_new: "mgu t1 t2 = Ok u \<Longrightarrow> new_tv n t1 \<Longrightarrow> new_tv n t2 \<Longrightarrow> new_tv n u"
  -- {* @{text mgu} does not introduce new type variables *}
  by (unfold new_tv_def) (blast dest: mgu_free)


section {* Mini-ML with type inference rules *}

datatype
  expr = Var nat | Abs expr | App expr expr


text {* Type inference rules. *}

consts
  has_type :: "(typ list \<times> expr \<times> typ) set"

syntax
  "_has_type" :: "typ list \<Rightarrow> expr \<Rightarrow> typ \<Rightarrow> bool"
    ("((_) |-/ (_) :: (_))" [60, 0, 60] 60)
translations
  "a |- e :: t" == "(a, e, t) \<in> has_type"

inductive has_type
  intros
    Var: "n < length a \<Longrightarrow> a |- Var n :: a ! n"
    Abs: "t1#a |- e :: t2 \<Longrightarrow> a |- Abs e :: t1 -> t2"
    App: "a |- e1 :: t2 -> t1 \<Longrightarrow> a |- e2 :: t2
      \<Longrightarrow> a |- App e1 e2 :: t1"


text {* Type assigment is closed wrt.\ substitution. *}

lemma has_type_subst_closed: "a |- e :: t ==> $s a |- e :: $s t"
proof -
  assume "a |- e :: t"
  thus ?thesis (is "?P a e t")
  proof induct
    case (Var a n)
    hence "n < length (map ($ s) a)" by simp
    hence "map ($ s) a |- Var n :: map ($ s) a ! n"
      by (rule has_type.Var)
    also have "map ($ s) a ! n = $ s (a ! n)"
      by (rule nth_map)
    also have "map ($ s) a = $ s a"
      by (simp only: app_subst_list)
    finally show "?P a (Var n) (a ! n)" .
  next
    case (Abs a e t1 t2)
    hence "$ s t1 # map ($ s) a |- e :: $ s t2"
      by (simp add: app_subst_list)
    hence "map ($ s) a |- Abs e :: $ s t1 -> $ s t2"
      by (rule has_type.Abs)
    thus "?P a (Abs e) (t1 -> t2)"
      by (simp add: app_subst_list)
  next
    case App
    thus ?case by (simp add: has_type.App)
  qed
qed


section {* Correctness and completeness of the type inference algorithm @{text \<W>} *}

consts
  W :: "expr \<Rightarrow> typ list \<Rightarrow> nat \<Rightarrow> (subst \<times> typ \<times> nat) maybe"  ("\<W>")

primrec
  "\<W> (Var i) a n =
    (if i < length a then Ok (id_subst, a ! i, n) else Fail)"
  "\<W> (Abs e) a n =
    ((s, t, m) := \<W> e (TVar n # a) (Suc n);
     Ok (s, (s n) -> t, m))"
  "\<W> (App e1 e2) a n =
    ((s1, t1, m1) := \<W> e1 a n;
     (s2, t2, m2) := \<W> e2 ($s1 a) m1;
     u := mgu ($ s2 t1) (t2 -> TVar m2);
     Ok ($u o $s2 o s1, $u (TVar m2), Suc m2))"

theorem W_correct: "!!a s t m n. Ok (s, t, m) = \<W> e a n ==> $s a |- e :: t"
  (is "PROP ?P e")
proof (induct e)
  fix a s t m n
  {
    fix i
    assume "Ok (s, t, m) = \<W> (Var i) a n"
    thus "$s a |- Var i :: t" by (simp add: has_type.Var split: if_splits)
  next
    fix e assume hyp: "PROP ?P e"
    assume "Ok (s, t, m) = \<W> (Abs e) a n"
    then obtain t' where "t = s n -> t'"
        and "Ok (s, t', m) = \<W> e (TVar n # a) (Suc n)"
      by (auto split: bind_splits)
    with hyp show "$s a |- Abs e :: t"
      by (force intro: has_type.Abs)
  next
    fix e1 e2 assume hyp1: "PROP ?P e1" and hyp2: "PROP ?P e2"
    assume "Ok (s, t, m) = \<W> (App e1 e2) a n"
    then obtain s1 t1 n1 s2 t2 n2 u where
          s: "s = $u o $s2 o s1"
        and t: "t = u n2"
        and mgu_ok: "mgu ($s2 t1) (t2 -> TVar n2) = Ok u"
        and W1_ok: "Ok (s1, t1, n1) = \<W> e1 a n"
        and W2_ok: "Ok (s2, t2, n2) = \<W> e2 ($s1 a) n1"
      by (auto split: bind_splits simp: that)
    show "$s a |- App e1 e2 :: t"
    proof (rule has_type.App)
      from s have s': "$u ($s2 ($s1 a)) = $s a"
        by (simp add: subst_comp_tel o_def)
      show "$s a |- e1 :: $u t2 -> t"
      proof -
        from W1_ok have "$s1 a |- e1 :: t1" by (rule hyp1)
        hence "$u ($s2 ($s1 a)) |- e1 :: $u ($s2 t1)"
          by (intro has_type_subst_closed)
        with s' t mgu_ok show ?thesis by simp
      qed
      show "$s a |- e2 :: $u t2"
      proof -
        from W2_ok have "$s2 ($s1 a) |- e2 :: t2" by (rule hyp2)
        hence "$u ($s2 ($s1 a)) |- e2 :: $u t2"
          by (rule has_type_subst_closed)
        with s' show ?thesis by simp
      qed
    qed
  }
qed


inductive_cases has_type_casesE:
  "s |- Var n :: t"
  "s |- Abs e :: t"
  "s |- App e1 e2 ::t"


lemmas [simp] = Suc_le_lessD
  and [simp del] = less_imp_le ex_simps all_simps

lemma W_var_ge [simp]: "!!a n s t m. \<W> e a n = Ok (s, t, m) \<Longrightarrow> n \<le> m"
  -- {* the resulting type variable is always greater or equal than the given one *}
  apply (atomize (full))
  apply (induct e)
    txt {* case @{text "Var n"} *}
    apply clarsimp
   txt {* case @{text "Abs e"} *}
   apply (simp split add: split_bind)
   apply (fast dest: Suc_leD)
  txt {* case @{text "App e1 e2"} *}
  apply (simp (no_asm) split add: split_bind)
  apply (intro strip)
  apply (rename_tac s t na sa ta nb sb)
  apply (erule_tac x = a in allE)
  apply (erule_tac x = n in allE)
  apply (erule_tac x = "$s a" in allE)
  apply (erule_tac x = s in allE)
  apply (erule_tac x = t in allE)
  apply (erule_tac x = na in allE)
  apply (erule_tac x = na in allE)
  apply (simp add: eq_sym_conv)
  done

lemma W_var_geD: "Ok (s, t, m) = \<W> e a n \<Longrightarrow> n \<le> m"
  by (simp add: eq_sym_conv)

lemma new_tv_W: "!!n a s t m.
  new_tv n a \<Longrightarrow> \<W> e a n = Ok (s, t, m) \<Longrightarrow> new_tv m s & new_tv m t"
  -- {* resulting type variable is new *}
  apply (atomize (full))
  apply (induct e)
    txt {* case @{text "Var n"} *}
    apply clarsimp
    apply (force elim: list_ball_nth simp add: id_subst_def new_tv_list new_tv_subst)
   txt {* case @{text "Abs e"} *}
   apply (simp (no_asm) add: new_tv_subst new_tv_Suc_list split add: split_bind)
   apply (intro strip)
   apply (erule_tac x = "Suc n" in allE)
   apply (erule_tac x = "TVar n # a" in allE)
   apply (fastsimp simp add: new_tv_subst new_tv_Suc_list)
  txt {* case @{text "App e1 e2"} *}
  apply (simp (no_asm) split add: split_bind)
  apply (intro strip)
  apply (rename_tac s t na sa ta nb sb)
  apply (erule_tac x = n in allE)
  apply (erule_tac x = a in allE)
  apply (erule_tac x = s in allE)
  apply (erule_tac x = t in allE)
  apply (erule_tac x = na in allE)
  apply (erule_tac x = na in allE)
  apply (simp add: eq_sym_conv)
  apply (erule_tac x = "$s a" in allE)
  apply (erule_tac x = sa in allE)
  apply (erule_tac x = ta in allE)
  apply (erule_tac x = nb in allE)
  apply (simp add: o_def rotate_Ok)
  apply (rule conjI)
   apply (rule new_tv_subst_comp_2)
    apply (rule new_tv_subst_comp_2)
     apply (rule lessI [THEN less_imp_le, THEN new_tv_subst_le])
     apply (rule_tac n = na in new_tv_subst_le)
      apply (simp add: rotate_Ok)
     apply (simp (no_asm_simp))
    apply (fast dest: W_var_geD intro: new_tv_list_le new_tv_subst_tel
      lessI [THEN less_imp_le, THEN new_tv_subst_le])
   apply (erule sym [THEN mgu_new])
    apply (best dest: W_var_geD intro: new_tv_subst_te new_tv_list_le new_tv_subst_tel
      lessI [THEN less_imp_le, THEN new_tv_le] lessI [THEN less_imp_le, THEN new_tv_subst_le]
      new_tv_le)
   apply (tactic {* fast_tac (HOL_cs addDs [thm "W_var_geD"]
     addIs [thm "new_tv_list_le", thm "new_tv_subst_tel", thm "new_tv_le"]
     addss (simpset())) 1 *})
  apply (rule lessI [THEN new_tv_subst_var])
  apply (erule sym [THEN mgu_new])
    apply (bestsimp intro!: lessI [THEN less_imp_le, THEN new_tv_le] new_tv_subst_te
      dest!: W_var_geD intro: new_tv_list_le new_tv_subst_tel
        lessI [THEN less_imp_le, THEN new_tv_subst_le] new_tv_le)
  apply (tactic {* fast_tac (HOL_cs addDs [thm "W_var_geD"]
    addIs [thm "new_tv_list_le", thm "new_tv_subst_tel", thm "new_tv_le"]
    addss (simpset())) 1 *})
  done

lemma free_tv_W: "!!n a s t m v. \<W> e a n = Ok (s, t, m) \<Longrightarrow>
    (v \<in> free_tv s \<or> v \<in> free_tv t) \<Longrightarrow> v < n \<Longrightarrow> v \<in> free_tv a"
  apply (atomize (full))
  apply (induct e)
    txt {* case @{text "Var n"} *}
    apply clarsimp
    apply (tactic {* fast_tac (HOL_cs addIs [nth_mem, subsetD, thm "ftv_mem_sub_ftv_list"]) 1 *})
   txt {* case @{text "Abs e"} *}
   apply (simp add: free_tv_subst split add: split_bind)
   apply (intro strip)
   apply (rename_tac s t n1 v)
   apply (erule_tac x = "Suc n" in allE)
   apply (erule_tac x = "TVar n # a" in allE)
   apply (erule_tac x = s in allE)
   apply (erule_tac x = t in allE)
   apply (erule_tac x = n1 in allE)
   apply (erule_tac x = v in allE)
   apply (force elim!: allE intro: cod_app_subst)
  txt {* case @{text "App e1 e2"} *}
  apply (simp (no_asm) split add: split_bind)
  apply (intro strip)
  apply (rename_tac s t n1 s1 t1 n2 s3 v)
  apply (erule_tac x = n in allE)
  apply (erule_tac x = a in allE)
  apply (erule_tac x = s in allE)
  apply (erule_tac x = t in allE)
  apply (erule_tac x = n1 in allE)
  apply (erule_tac x = n1 in allE)
  apply (erule_tac x = v in allE)
  txt {* second case *}
  apply (erule_tac x = "$ s a" in allE)
  apply (erule_tac x = s1 in allE)
  apply (erule_tac x = t1 in allE)
  apply (erule_tac x = n2 in allE)
  apply (erule_tac x = v in allE)
  apply (tactic "safe_tac (empty_cs addSIs [conjI, impI] addSEs [conjE])")
   apply (simp add: rotate_Ok o_def)
   apply (drule W_var_geD)
   apply (drule W_var_geD)
   apply (frule less_le_trans, assumption)
   apply (fastsimp dest: free_tv_comp_subst [THEN subsetD] sym [THEN mgu_free] codD
     free_tv_app_subst_te [THEN subsetD] free_tv_app_subst_tel [THEN subsetD] subsetD elim: UnE)
  apply simp
  apply (drule sym [THEN W_var_geD])
  apply (drule sym [THEN W_var_geD])
  apply (frule less_le_trans, assumption)
  apply (tactic {* fast_tac (HOL_cs addDs [thm "mgu_free", thm "codD",
    thm "free_tv_subst_var" RS subsetD,
    thm "free_tv_app_subst_te" RS subsetD,
    thm "free_tv_app_subst_tel" RS subsetD, less_le_trans, subsetD]
    addSEs [UnE] addss (simpset() setSolver unsafe_solver)) 1 *})
      -- {* builtin arithmetic in simpset messes things up *}
  done

text {*
  \medskip Completeness of @{text \<W>} wrt.\ @{text has_type}.
*}

lemma W_complete_aux: "!!s' a t' n. $s' a |- e :: t' \<Longrightarrow> new_tv n a \<Longrightarrow>
    (\<exists>s t. (\<exists>m. \<W> e a n = Ok (s, t, m)) \<and> (\<exists>r. $s' a = $r ($s a) \<and> t' = $r t))"
  apply (atomize (full))
  apply (induct e)
    txt {* case @{text "Var n"} *}
    apply (intro strip)
    apply (simp (no_asm) cong add: conj_cong)
    apply (erule has_type_casesE)
    apply (simp add: eq_sym_conv app_subst_list)
    apply (rule_tac x = s' in exI)
    apply simp
   txt {* case @{text "Abs e"} *}
   apply (intro strip)
   apply (erule has_type_casesE)
   apply (erule_tac x = "\<lambda>x. if x = n then t1 else (s' x)" in allE)
   apply (erule_tac x = "TVar n # a" in allE)
   apply (erule_tac x = t2 in allE)
   apply (erule_tac x = "Suc n" in allE)
   apply (fastsimp cong add: conj_cong split add: split_bind)
  txt {* case @{text "App e1 e2"} *}
  apply (intro strip)
  apply (erule has_type_casesE)
  apply (erule_tac x = s' in allE)
  apply (erule_tac x = a in allE)
  apply (erule_tac x = "t2 -> t'" in allE)
  apply (erule_tac x = n in allE)
  apply (tactic "safe_tac HOL_cs")
  apply (erule_tac x = r in allE)
  apply (erule_tac x = "$s a" in allE)
  apply (erule_tac x = t2 in allE)
  apply (erule_tac x = m in allE)
  apply simp
  apply (tactic "safe_tac HOL_cs")
   apply (tactic {* fast_tac (HOL_cs addIs [sym RS thm "W_var_geD",
     thm "new_tv_W" RS conjunct1, thm "new_tv_list_le", thm "new_tv_subst_tel"]) 1 *})
  apply (subgoal_tac
    "$(\<lambda>x. if x = ma then t' else (if x \<in> free_tv t - free_tv sa then r x
      else ra x)) ($ sa t) =
    $(\<lambda>x. if x = ma then t' else (if x \<in> free_tv t - free_tv sa then r x
      else ra x)) (ta -> (TVar ma))")
   apply (rule_tac [2] t = "$(\<lambda>x. if x = ma then t'
     else (if x \<in> (free_tv t - free_tv sa) then r x else ra x)) ($sa t)" and
     s = "($ ra ta) -> t'" in ssubst)
    prefer 2
    apply (simp add: subst_comp_te)
    apply (rule eq_free_eq_subst_te)
    apply (intro strip)
    apply (subgoal_tac "na \<noteq> ma")
     prefer 2
     apply (fast dest: new_tv_W sym [THEN W_var_geD] new_tv_not_free_tv new_tv_le)
    apply (case_tac "na \<in> free_tv sa")
     txt {* @{text "na \<notin> free_tv sa"} *}
     prefer 2
     apply (frule not_free_impl_id)
     apply simp
    txt {* @{text "na \<in> free_tv sa"} *}
    apply (drule_tac ts1 = "$s a" in subst_comp_tel [THEN [2] trans])
    apply (drule_tac eq_subst_tel_eq_free)
     apply (fast intro: free_tv_W free_tv_le_new_tv dest: new_tv_W)
    apply simp
    apply (case_tac "na \<in> dom sa")
     prefer 2
     txt {* @{text "na \<noteq> dom sa"} *}
     apply (simp add: dom_def)
    txt {* @{text "na \<in> dom sa"} *}
    apply (rule eq_free_eq_subst_te)
    apply (intro strip)
    apply (subgoal_tac "nb \<noteq> ma")
     prefer 2
     apply (frule new_tv_W, assumption)
     apply (erule conjE)
     apply (drule new_tv_subst_tel)
      apply (fast intro: new_tv_list_le dest: sym [THEN W_var_geD])
     apply (fastsimp dest: new_tv_W new_tv_not_free_tv simp add: cod_def free_tv_subst)
    apply (fastsimp simp add: cod_def free_tv_subst)
   prefer 2
   apply (simp (no_asm))
   apply (rule eq_free_eq_subst_te)
   apply (intro strip)
   apply (subgoal_tac "na \<noteq> ma")
    prefer 2
    apply (frule new_tv_W, assumption)
    apply (erule conjE)
    apply (drule sym [THEN W_var_geD])
    apply (fast dest: new_tv_list_le new_tv_subst_tel new_tv_W new_tv_not_free_tv)
   apply (case_tac "na \<in> free_tv t - free_tv sa")
    prefer 2
    txt {* case @{text "na \<notin> free_tv t - free_tv sa"} *}
    apply simp
    defer
    txt {* case @{text "na \<in> free_tv t - free_tv sa"} *}
    apply simp
    apply (drule_tac ts1 = "$s a" in subst_comp_tel [THEN [2] trans])
    apply (drule eq_subst_tel_eq_free)
     apply (fast intro: free_tv_W free_tv_le_new_tv dest: new_tv_W)
    apply (simp add: free_tv_subst dom_def)
   prefer 2 apply fast
  apply (simp (no_asm_simp) split add: split_bind)
  apply (tactic "safe_tac HOL_cs")
   apply (drule mgu_Ok)
   apply fastsimp
  apply (drule mgu_mg, assumption)
  apply (erule exE)
  apply (rule_tac x = rb in exI)
  apply (rule conjI)
   prefer 2
   apply (drule_tac x = ma in fun_cong)
   apply (simp add: eq_sym_conv)
  apply (simp (no_asm) add: o_def subst_comp_tel [symmetric])
  apply (rule subst_comp_tel [symmetric, THEN [2] trans])
  apply (simp add: o_def eq_sym_conv)
  apply (rule eq_free_eq_subst_tel)
  apply (tactic "safe_tac HOL_cs")
  apply (subgoal_tac "ma \<noteq> na")
   prefer 2
   apply (frule new_tv_W, assumption)
   apply (erule conjE)
   apply (drule new_tv_subst_tel)
    apply (fast intro: new_tv_list_le dest: sym [THEN W_var_geD])
   apply (frule_tac n = m in new_tv_W, assumption)
   apply (erule conjE)
   apply (drule free_tv_app_subst_tel [THEN subsetD])
   apply (tactic {* fast_tac (set_cs addDs [sym RS thm "W_var_geD", thm "new_tv_list_le",
     thm "codD", thm "new_tv_not_free_tv"]) 1 *})
  apply (case_tac "na \<in> free_tv t - free_tv sa")
   prefer 2
   txt {* case @{text "na \<notin> free_tv t - free_tv sa"} *}
   apply simp
   defer
   txt {* case @{text "na \<in> free_tv t - free_tv sa"} *}
   apply simp
   apply (drule free_tv_app_subst_tel [THEN subsetD])
   apply (fastsimp dest: codD subst_comp_tel [THEN [2] trans]
     eq_subst_tel_eq_free simp add: free_tv_subst dom_def)
  apply fast
  done

lemma W_complete: "[] |- e :: t' ==>
    \<exists>s t. (\<exists>m. \<W> e [] n = Ok (s, t, m)) \<and> (\<exists>r. t' = $r t)"
  apply (cut_tac a = "[]" and s' = id_subst and e = e and t' = t' in W_complete_aux)
    apply simp_all
  done


section {* Equivalence of @{text \<W>} and @{text \<I>} *}

text {*
  Recursive definition of type inference algorithm @{text \<I>} for
  Mini-ML.
*}

consts
  I :: "expr \<Rightarrow> typ list \<Rightarrow> nat \<Rightarrow> subst \<Rightarrow> (subst \<times> typ \<times> nat) maybe"  ("\<I>")
primrec
  "\<I> (Var i) a n s = (if i < length a then Ok (s, a ! i, n) else Fail)"
  "\<I> (Abs e) a n s = ((s, t, m) := \<I> e (TVar n # a) (Suc n) s;
    Ok (s, TVar n -> t, m))"
  "\<I> (App e1 e2) a n s =
    ((s1, t1, m1) := \<I> e1 a n s;
    (s2, t2, m2) := \<I> e2 a m1 s1;
    u := mgu ($s2 t1) ($s2 t2 -> TVar m2);
    Ok($u o s2, TVar m2, Suc m2))"

text {* \medskip Correctness. *}

lemma I_correct_wrt_W: "!!a m s s' t n.
    new_tv m a \<and> new_tv m s \<Longrightarrow> \<I> e a m s = Ok (s', t, n) \<Longrightarrow>
    \<exists>r. \<W> e ($s a) m = Ok (r, $s' t, n) \<and> s' = ($r o s)"
  apply (atomize (full))
  apply (induct e)
    txt {* case @{text "Var n"} *}
    apply (simp add: app_subst_list split: split_if)
   txt {* case @{text "Abs e"} *}
   apply (tactic {* asm_full_simp_tac
     (simpset() setloop (split_inside_tac [thm "split_bind"])) 1 *})
   apply (intro strip)
   apply (rule conjI)
    apply (intro strip)
    apply (erule allE)+
    apply (erule impE)
     prefer 2 apply (fastsimp simp add: new_tv_subst)
    apply (tactic {* fast_tac (HOL_cs addIs [thm "new_tv_Suc_list" RS mp,
      thm "new_tv_subst_le", less_imp_le, lessI]) 1 *})
   apply (intro strip)
   apply (erule allE)+
   apply (erule impE)
    prefer 2 apply (fastsimp simp add: new_tv_subst)
   apply (tactic {* fast_tac (HOL_cs addIs [thm "new_tv_Suc_list" RS mp,
     thm "new_tv_subst_le", less_imp_le, lessI]) 1 *})
  txt {* case @{text "App e1 e2"} *}
  apply (tactic {* simp_tac (simpset () setloop (split_inside_tac [thm "split_bind"])) 1 *})
  apply (intro strip)
  apply (rename_tac s1' t1 n1 s2' t2 n2 sa)
  apply (rule conjI)
   apply fastsimp
  apply (intro strip)
  apply (rename_tac s1 t1' n1')
  apply (erule_tac x = a in allE)
  apply (erule_tac x = m in allE)
  apply (erule_tac x = s in allE)
  apply (erule_tac x = s1' in allE)
  apply (erule_tac x = t1 in allE)
  apply (erule_tac x = n1 in allE)
  apply (erule_tac x = a in allE)
  apply (erule_tac x = n1 in allE)
  apply (erule_tac x = s1' in allE)
  apply (erule_tac x = s2' in allE)
  apply (erule_tac x = t2 in allE)
  apply (erule_tac x = n2 in allE)
  apply (rule conjI)
   apply (intro strip)
   apply (rule notI)
   apply simp
   apply (erule impE)
    apply (frule new_tv_subst_tel, assumption)
    apply (drule_tac a = "$s a" in new_tv_W, assumption)
    apply (fastsimp dest: sym [THEN W_var_geD] new_tv_subst_le new_tv_list_le)
   apply (fastsimp simp add: subst_comp_tel)
  apply (intro strip)
  apply (rename_tac s2 t2' n2')
  apply (rule conjI)
   apply (intro strip)
   apply (rule notI)
   apply simp
   apply (erule impE)
   apply (frule new_tv_subst_tel, assumption)
   apply (drule_tac a = "$s a" in new_tv_W, assumption)
    apply (fastsimp dest: sym [THEN W_var_geD] new_tv_subst_le new_tv_list_le)
   apply (fastsimp simp add: subst_comp_tel subst_comp_te)
  apply (intro strip)
  apply (erule (1) notE impE)
  apply (erule (1) notE impE)
  apply (erule exE)
  apply (erule conjE)
  apply (erule impE)
   apply (frule new_tv_subst_tel, assumption)
   apply (drule_tac a = "$s a" in new_tv_W, assumption)
   apply (fastsimp dest: sym [THEN W_var_geD] new_tv_subst_le new_tv_list_le)
  apply (erule (1) notE impE)
  apply (erule exE conjE)+
  apply (simp add: subst_comp_tel subst_comp_te o_def, (erule conjE)+, hypsubst)+
  apply (subgoal_tac "new_tv n2 s \<and> new_tv n2 r \<and> new_tv n2 ra")
   apply (simp add: new_tv_subst)
  apply (frule new_tv_subst_tel, assumption)
  apply (drule_tac a = "$s a" in new_tv_W, assumption)
  apply (tactic "safe_tac HOL_cs")
    apply (bestsimp dest: sym [THEN W_var_geD] new_tv_subst_le new_tv_list_le)
   apply (fastsimp dest: sym [THEN W_var_geD] new_tv_subst_le new_tv_list_le)
  apply (drule_tac e = expr1 in sym [THEN W_var_geD])
  apply (drule new_tv_subst_tel, assumption)
  apply (drule_tac ts = "$s a" in new_tv_list_le, assumption)
  apply (drule new_tv_subst_tel, assumption)
  apply (bestsimp dest: new_tv_W simp add: subst_comp_tel)
  done

lemma I_complete_wrt_W: "!!a m s.
    new_tv m a \<and> new_tv m s \<Longrightarrow> \<I> e a m s = Fail \<Longrightarrow> \<W> e ($s a) m = Fail"
  apply (atomize (full))
  apply (induct e)
    apply (simp add: app_subst_list)
   apply (simp (no_asm))
   apply (intro strip)
   apply (subgoal_tac "TVar m # $s a = $s (TVar m # a)")
    apply (tactic {* asm_simp_tac (HOL_ss addsimps
      [thm "new_tv_Suc_list", lessI RS less_imp_le RS thm "new_tv_subst_le"]) 1 *})
    apply (erule conjE)
    apply (drule new_tv_not_free_tv [THEN not_free_impl_id])
    apply (simp (no_asm_simp))
  apply (simp (no_asm_simp))
  apply (intro strip)
  apply (erule exE)+
  apply (erule conjE)+
  apply (drule I_correct_wrt_W [COMP swap_prems_rl])
   apply fast
  apply (erule exE)
  apply (erule conjE)
  apply hypsubst
  apply (simp (no_asm_simp))
  apply (erule disjE)
   apply (rule disjI1)
   apply (simp (no_asm_use) add: o_def subst_comp_tel)
   apply (erule allE, erule allE, erule allE, erule impE, erule_tac [2] impE,
     erule_tac [2] asm_rl, erule_tac [2] asm_rl)
   apply (rule conjI)
    apply (fast intro: W_var_ge [THEN new_tv_list_le])
   apply (rule new_tv_subst_comp_2)
    apply (fast intro: W_var_ge [THEN new_tv_subst_le])
   apply (fast intro!: new_tv_subst_tel intro: new_tv_W [THEN conjunct1])
  apply (rule disjI2)
  apply (erule exE)+
  apply (erule conjE)
  apply (drule I_correct_wrt_W [COMP swap_prems_rl])
   apply (rule conjI)
   apply (fast intro: W_var_ge [THEN new_tv_list_le])
   apply (rule new_tv_subst_comp_1)
   apply (fast intro: W_var_ge [THEN new_tv_subst_le])
   apply (fast intro!: new_tv_subst_tel intro: new_tv_W [THEN conjunct1])
  apply (erule exE)
  apply (erule conjE)
  apply hypsubst
  apply (simp add: o_def subst_comp_te [symmetric] subst_comp_tel [symmetric])
  done

end
