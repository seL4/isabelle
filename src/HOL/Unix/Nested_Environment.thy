(*  Title:      HOL/Unix/Nested_Environment.thy
    Author:     Markus Wenzel, TU Muenchen
*)

section \<open>Nested environments\<close>

theory Nested_Environment
imports Main
begin

text \<open>
  Consider a partial function @{term [source] "e :: 'a \<Rightarrow> 'b option"}; this may
  be understood as an \<^emph>\<open>environment\<close> mapping indexes \<^typ>\<open>'a\<close> to optional
  entry values \<^typ>\<open>'b\<close> (cf.\ the basic theory \<open>Map\<close> of Isabelle/HOL). This
  basic idea is easily generalized to that of a \<^emph>\<open>nested environment\<close>, where
  entries may be either basic values or again proper environments. Then each
  entry is accessed by a \<^emph>\<open>path\<close>, i.e.\ a list of indexes leading to its
  position within the structure.
\<close>

datatype (dead 'a, dead 'b, dead 'c) env =
    Val 'a
  | Env 'b  "'c \<Rightarrow> ('a, 'b, 'c) env option"

text \<open>
  \<^medskip>
  In the type \<^typ>\<open>('a, 'b, 'c) env\<close> the parameter \<^typ>\<open>'a\<close> refers to
  basic values (occurring in terminal positions), type \<^typ>\<open>'b\<close> to values
  associated with proper (inner) environments, and type \<^typ>\<open>'c\<close> with the
  index type for branching. Note that there is no restriction on any of these
  types. In particular, arbitrary branching may yield rather large
  (transfinite) tree structures.
\<close>


subsection \<open>The lookup operation\<close>

text \<open>
  Lookup in nested environments works by following a given path of index
  elements, leading to an optional result (a terminal value or nested
  environment). A \<^emph>\<open>defined position\<close> within a nested environment is one where
  \<^term>\<open>lookup\<close> at its path does not yield \<^term>\<open>None\<close>.
\<close>

primrec lookup :: "('a, 'b, 'c) env \<Rightarrow> 'c list \<Rightarrow> ('a, 'b, 'c) env option"
  and lookup_option :: "('a, 'b, 'c) env option \<Rightarrow> 'c list \<Rightarrow> ('a, 'b, 'c) env option"
where
    "lookup (Val a) xs = (if xs = [] then Some (Val a) else None)"
  | "lookup (Env b es) xs =
      (case xs of
        [] \<Rightarrow> Some (Env b es)
      | y # ys \<Rightarrow> lookup_option (es y) ys)"
  | "lookup_option None xs = None"
  | "lookup_option (Some e) xs = lookup e xs"

hide_const lookup_option

text \<open>
  \<^medskip>
  The characteristic cases of \<^term>\<open>lookup\<close> are expressed by the following
  equalities.
\<close>

theorem lookup_nil: "lookup e [] = Some e"
  by (cases e) simp_all

theorem lookup_val_cons: "lookup (Val a) (x # xs) = None"
  by simp

theorem lookup_env_cons:
  "lookup (Env b es) (x # xs) =
    (case es x of
      None \<Rightarrow> None
    | Some e \<Rightarrow> lookup e xs)"
  by (cases "es x") simp_all

lemmas lookup.simps [simp del] lookup_option.simps [simp del]
  and lookup_simps [simp] = lookup_nil lookup_val_cons lookup_env_cons

theorem lookup_eq:
  "lookup env xs =
    (case xs of
      [] \<Rightarrow> Some env
    | x # xs \<Rightarrow>
      (case env of
        Val a \<Rightarrow> None
      | Env b es \<Rightarrow>
          (case es x of
            None \<Rightarrow> None
          | Some e \<Rightarrow> lookup e xs)))"
  by (simp split: list.split env.split)

text \<open>
  \<^medskip>
  Displaced \<^term>\<open>lookup\<close> operations, relative to a certain base path prefix,
  may be reduced as follows. There are two cases, depending whether the
  environment actually extends far enough to follow the base path.
\<close>

theorem lookup_append_none:
  assumes "lookup env xs = None"
  shows "lookup env (xs @ ys) = None"
  using assms
proof (induct xs arbitrary: env)
  case Nil
  then have False by simp
  then show ?case ..
next
  case (Cons x xs)
  show ?case
  proof (cases env)
    case Val
    then show ?thesis by simp
  next
    case (Env b es)
    show ?thesis
    proof (cases "es x")
      case None
      with Env show ?thesis by simp
    next
      case (Some e)
      note es = \<open>es x = Some e\<close>
      show ?thesis
      proof (cases "lookup e xs")
        case None
        then have "lookup e (xs @ ys) = None" by (rule Cons.hyps)
        with Env Some show ?thesis by simp
      next
        case Some
        with Env es have False using Cons.prems by simp
        then show ?thesis ..
      qed
    qed
  qed
qed

theorem lookup_append_some:
  assumes "lookup env xs = Some e"
  shows "lookup env (xs @ ys) = lookup e ys"
  using assms
proof (induct xs arbitrary: env e)
  case Nil
  then have "env = e" by simp
  then show "lookup env ([] @ ys) = lookup e ys" by simp
next
  case (Cons x xs)
  note asm = \<open>lookup env (x # xs) = Some e\<close>
  show "lookup env ((x # xs) @ ys) = lookup e ys"
  proof (cases env)
    case (Val a)
    with asm have False by simp
    then show ?thesis ..
  next
    case (Env b es)
    show ?thesis
    proof (cases "es x")
      case None
      with asm Env have False by simp
      then show ?thesis ..
    next
      case (Some e')
      note es = \<open>es x = Some e'\<close>
      show ?thesis
      proof (cases "lookup e' xs")
        case None
        with asm Env es have False by simp
        then show ?thesis ..
      next
        case Some
        with asm Env es have "lookup e' xs = Some e"
          by simp
        then have "lookup e' (xs @ ys) = lookup e ys" by (rule Cons.hyps)
        with Env es show ?thesis by simp
      qed
    qed
  qed
qed

text \<open>
  \<^medskip>
  Successful \<^term>\<open>lookup\<close> deeper down an environment structure means we are
  able to peek further up as well. Note that this is basically just the
  contrapositive statement of @{thm [source] lookup_append_none} above.
\<close>

theorem lookup_some_append:
  assumes "lookup env (xs @ ys) = Some e"
  shows "\<exists>e. lookup env xs = Some e"
proof -
  from assms have "lookup env (xs @ ys) \<noteq> None" by simp
  then have "lookup env xs \<noteq> None"
    by (rule contrapos_nn) (simp only: lookup_append_none)
  then show ?thesis by (simp)
qed

text \<open>
  The subsequent statement describes in more detail how a successful \<^term>\<open>lookup\<close> with a non-empty path results in a certain situation at any upper
  position.
\<close>

theorem lookup_some_upper:
  assumes "lookup env (xs @ y # ys) = Some e"
  shows "\<exists>b' es' env'.
    lookup env xs = Some (Env b' es') \<and>
    es' y = Some env' \<and>
    lookup env' ys = Some e"
  using assms
proof (induct xs arbitrary: env e)
  case Nil
  from Nil.prems have "lookup env (y # ys) = Some e"
    by simp
  then obtain b' es' env' where
      env: "env = Env b' es'" and
      es': "es' y = Some env'" and
      look': "lookup env' ys = Some e"
    by (auto simp add: lookup_eq split: option.splits env.splits)
  from env have "lookup env [] = Some (Env b' es')" by simp
  with es' look' show ?case by blast
next
  case (Cons x xs)
  from Cons.prems
  obtain b' es' env' where
      env: "env = Env b' es'" and
      es': "es' x = Some env'" and
      look': "lookup env' (xs @ y # ys) = Some e"
    by (auto simp add: lookup_eq split: option.splits env.splits)
  from Cons.hyps [OF look'] obtain b'' es'' env'' where
      upper': "lookup env' xs = Some (Env b'' es'')" and
      es'': "es'' y = Some env''" and
      look'': "lookup env'' ys = Some e"
    by blast
  from env es' upper' have "lookup env (x # xs) = Some (Env b'' es'')"
    by simp
  with es'' look'' show ?case by blast
qed


subsection \<open>The update operation\<close>

text \<open>
  Update at a certain position in a nested environment may either delete an
  existing entry, or overwrite an existing one. Note that update at undefined
  positions is simple absorbed, i.e.\ the environment is left unchanged.
\<close>

primrec update :: "'c list \<Rightarrow> ('a, 'b, 'c) env option \<Rightarrow>
    ('a, 'b, 'c) env \<Rightarrow> ('a, 'b, 'c) env"
  and update_option :: "'c list \<Rightarrow> ('a, 'b, 'c) env option \<Rightarrow>
    ('a, 'b, 'c) env option \<Rightarrow> ('a, 'b, 'c) env option"
where
  "update xs opt (Val a) =
    (if xs = [] then (case opt of None \<Rightarrow> Val a | Some e \<Rightarrow> e)
     else Val a)"
| "update xs opt (Env b es) =
    (case xs of
      [] \<Rightarrow> (case opt of None \<Rightarrow> Env b es | Some e \<Rightarrow> e)
    | y # ys \<Rightarrow> Env b (es (y := update_option ys opt (es y))))"
| "update_option xs opt None =
    (if xs = [] then opt else None)"
| "update_option xs opt (Some e) =
    (if xs = [] then opt else Some (update xs opt e))"

hide_const update_option

text \<open>
  \<^medskip>
  The characteristic cases of \<^term>\<open>update\<close> are expressed by the following
  equalities.
\<close>

theorem update_nil_none: "update [] None env = env"
  by (cases env) simp_all

theorem update_nil_some: "update [] (Some e) env = e"
  by (cases env) simp_all

theorem update_cons_val: "update (x # xs) opt (Val a) = Val a"
  by simp

theorem update_cons_nil_env:
    "update [x] opt (Env b es) = Env b (es (x := opt))"
  by (cases "es x") simp_all

theorem update_cons_cons_env:
  "update (x # y # ys) opt (Env b es) =
    Env b (es (x :=
      (case es x of
        None \<Rightarrow> None
      | Some e \<Rightarrow> Some (update (y # ys) opt e))))"
  by (cases "es x") simp_all

lemmas update.simps [simp del] update_option.simps [simp del]
  and update_simps [simp] = update_nil_none update_nil_some
    update_cons_val update_cons_nil_env update_cons_cons_env

lemma update_eq:
  "update xs opt env =
    (case xs of
      [] \<Rightarrow>
        (case opt of
          None \<Rightarrow> env
        | Some e \<Rightarrow> e)
    | x # xs \<Rightarrow>
        (case env of
          Val a \<Rightarrow> Val a
        | Env b es \<Rightarrow>
            (case xs of
              [] \<Rightarrow> Env b (es (x := opt))
            | y # ys \<Rightarrow>
                Env b (es (x :=
                  (case es x of
                    None \<Rightarrow> None
                  | Some e \<Rightarrow> Some (update (y # ys) opt e)))))))"
  by (simp split: list.split env.split option.split)

text \<open>
  \<^medskip>
  The most basic correspondence of \<^term>\<open>lookup\<close> and \<^term>\<open>update\<close> states
  that after \<^term>\<open>update\<close> at a defined position, subsequent \<^term>\<open>lookup\<close>
  operations would yield the new value.
\<close>

theorem lookup_update_some:
  assumes "lookup env xs = Some e"
  shows "lookup (update xs (Some env') env) xs = Some env'"
  using assms
proof (induct xs arbitrary: env e)
  case Nil
  then have "env = e" by simp
  then show ?case by simp
next
  case (Cons x xs)
  note hyp = Cons.hyps
    and asm = \<open>lookup env (x # xs) = Some e\<close>
  show ?case
  proof (cases env)
    case (Val a)
    with asm have False by simp
    then show ?thesis ..
  next
    case (Env b es)
    show ?thesis
    proof (cases "es x")
      case None
      with asm Env have False by simp
      then show ?thesis ..
    next
      case (Some e')
      note es = \<open>es x = Some e'\<close>
      show ?thesis
      proof (cases xs)
        case Nil
        with Env show ?thesis by simp
      next
        case (Cons x' xs')
        from asm Env es have "lookup e' xs = Some e" by simp
        then have "lookup (update xs (Some env') e') xs = Some env'" by (rule hyp)
        with Env es Cons show ?thesis by simp
      qed
    qed
  qed
qed

text \<open>
  \<^medskip>
  The properties of displaced \<^term>\<open>update\<close> operations are analogous to those
  of \<^term>\<open>lookup\<close> above. There are two cases: below an undefined position
  \<^term>\<open>update\<close> is absorbed altogether, and below a defined positions \<^term>\<open>update\<close> affects subsequent \<^term>\<open>lookup\<close> operations in the obvious way.
\<close>

theorem update_append_none:
  assumes "lookup env xs = None"
  shows "update (xs @ y # ys) opt env = env"
  using assms
proof (induct xs arbitrary: env)
  case Nil
  then have False by simp
  then show ?case ..
next
  case (Cons x xs)
  note hyp = Cons.hyps
    and asm = \<open>lookup env (x # xs) = None\<close>
  show "update ((x # xs) @ y # ys) opt env = env"
  proof (cases env)
    case (Val a)
    then show ?thesis by simp
  next
    case (Env b es)
    show ?thesis
    proof (cases "es x")
      case None
      note es = \<open>es x = None\<close>
      show ?thesis
        by (cases xs) (simp_all add: es Env fun_upd_idem_iff)
    next
      case (Some e)
      note es = \<open>es x = Some e\<close>
      show ?thesis
      proof (cases xs)
        case Nil
        with asm Env Some have False by simp
        then show ?thesis ..
      next
        case (Cons x' xs')
        from asm Env es have "lookup e xs = None" by simp
        then have "update (xs @ y # ys) opt e = e" by (rule hyp)
        with Env es Cons show "update ((x # xs) @ y # ys) opt env = env"
          by (simp add: fun_upd_idem_iff)
      qed
    qed
  qed
qed

theorem update_append_some:
  assumes "lookup env xs = Some e"
  shows "lookup (update (xs @ y # ys) opt env) xs = Some (update (y # ys) opt e)"
  using assms
proof (induct xs arbitrary: env e)
  case Nil
  then have "env = e" by simp
  then show ?case by simp
next
  case (Cons x xs)
  note hyp = Cons.hyps
    and asm = \<open>lookup env (x # xs) = Some e\<close>
  show "lookup (update ((x # xs) @ y # ys) opt env) (x # xs) =
      Some (update (y # ys) opt e)"
  proof (cases env)
    case (Val a)
    with asm have False by simp
    then show ?thesis ..
  next
    case (Env b es)
    show ?thesis
    proof (cases "es x")
      case None
      with asm Env have False by simp
      then show ?thesis ..
    next
      case (Some e')
      note es = \<open>es x = Some e'\<close>
      show ?thesis
      proof (cases xs)
        case Nil
        with asm Env es have "e = e'" by simp
        with Env es Nil show ?thesis by simp
      next
        case (Cons x' xs')
        from asm Env es have "lookup e' xs = Some e" by simp
        then have "lookup (update (xs @ y # ys) opt e') xs =
          Some (update (y # ys) opt e)" by (rule hyp)
        with Env es Cons show ?thesis by simp
      qed
    qed
  qed
qed

text \<open>
  \<^medskip>
  Apparently, \<^term>\<open>update\<close> does not affect the result of subsequent \<^term>\<open>lookup\<close> operations at independent positions, i.e.\ in case that the paths
  for \<^term>\<open>update\<close> and \<^term>\<open>lookup\<close> fork at a certain point.
\<close>

theorem lookup_update_other:
  assumes neq: "y \<noteq> (z::'c)"
  shows "lookup (update (xs @ z # zs) opt env) (xs @ y # ys) =
    lookup env (xs @ y # ys)"
proof (induct xs arbitrary: env)
  case Nil
  show ?case
  proof (cases env)
    case Val
    then show ?thesis by simp
  next
    case Env
    show ?thesis
    proof (cases zs)
      case Nil
      with neq Env show ?thesis by simp
    next
      case Cons
      with neq Env show ?thesis by simp
    qed
  qed
next
  case (Cons x xs)
  note hyp = Cons.hyps
  show ?case
  proof (cases env)
    case Val
    then show ?thesis by simp
  next
    case (Env y es)
    show ?thesis
    proof (cases xs)
      case Nil
      show ?thesis
      proof (cases "es x")
        case None
        with Env Nil show ?thesis by simp
      next
        case Some
        with neq hyp and Env Nil show ?thesis by simp
      qed
    next
      case (Cons x' xs')
      show ?thesis
      proof (cases "es x")
        case None
        with Env Cons show ?thesis by simp
      next
        case Some
        with neq hyp and Env Cons show ?thesis by simp
      qed
    qed
  qed
qed

end
