(*  Title:      HOL/Library/Nested_Environment.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)
*)

header {* Nested environments *}

theory Nested_Environment = Main:

text {*
  Consider a partial function @{term [source] "e :: 'a => 'b option"};
  this may be understood as an \emph{environment} mapping indexes
  @{typ 'a} to optional entry values @{typ 'b} (cf.\ the basic theory
  @{text Map} of Isabelle/HOL).  This basic idea is easily generalized
  to that of a \emph{nested environment}, where entries may be either
  basic values or again proper environments.  Then each entry is
  accessed by a \emph{path}, i.e.\ a list of indexes leading to its
  position within the structure.
*}

datatype ('a, 'b, 'c) env =
    Val 'a
  | Env 'b  "'c => ('a, 'b, 'c) env option"

text {*
  \medskip In the type @{typ "('a, 'b, 'c) env"} the parameter @{typ
  'a} refers to basic values (occurring in terminal positions), type
  @{typ 'b} to values associated with proper (inner) environments, and
  type @{typ 'c} with the index type for branching.  Note that there
  is no restriction on any of these types.  In particular, arbitrary
  branching may yield rather large (transfinite) tree structures.
*}


subsection {* The lookup operation *}

text {*
  Lookup in nested environments works by following a given path of
  index elements, leading to an optional result (a terminal value or
  nested environment).  A \emph{defined position} within a nested
  environment is one where @{term lookup} at its path does not yield
  @{term None}.
*}

consts
  lookup :: "('a, 'b, 'c) env => 'c list => ('a, 'b, 'c) env option"
  lookup_option :: "('a, 'b, 'c) env option => 'c list => ('a, 'b, 'c) env option"

primrec (lookup)
  "lookup (Val a) xs = (if xs = [] then Some (Val a) else None)"
  "lookup (Env b es) xs =
    (case xs of
      [] => Some (Env b es)
    | y # ys => lookup_option (es y) ys)"
  "lookup_option None xs = None"
  "lookup_option (Some e) xs = lookup e xs"

hide const lookup_option

text {*
  \medskip The characteristic cases of @{term lookup} are expressed by
  the following equalities.
*}

theorem lookup_nil: "lookup e [] = Some e"
  by (cases e) simp_all

theorem lookup_val_cons: "lookup (Val a) (x # xs) = None"
  by simp

theorem lookup_env_cons:
  "lookup (Env b es) (x # xs) =
    (case es x of
      None => None
    | Some e => lookup e xs)"
  by (cases "es x") simp_all

lemmas lookup.simps [simp del]
  and lookup_simps [simp] = lookup_nil lookup_val_cons lookup_env_cons

theorem lookup_eq:
  "lookup env xs =
    (case xs of
      [] => Some env
    | x # xs =>
      (case env of
        Val a => None
      | Env b es =>
          (case es x of
            None => None
          | Some e => lookup e xs)))"
  by (simp split: list.split env.split)

text {*
  \medskip Displaced @{term lookup} operations, relative to a certain
  base path prefix, may be reduced as follows.  There are two cases,
  depending whether the environment actually extends far enough to
  follow the base path.
*}

theorem lookup_append_none:
  "!!env. lookup env xs = None ==> lookup env (xs @ ys) = None"
  (is "PROP ?P xs")
proof (induct xs)
  fix env :: "('a, 'b, 'c) env"
  {
    assume "lookup env [] = None"
    hence False by simp
    thus "lookup env ([] @ ys) = None" ..
  next
    fix x xs
    assume hyp: "PROP ?P xs"
    assume asm: "lookup env (x # xs) = None"
    show "lookup env ((x # xs) @ ys) = None"
    proof (cases env)
      case Val
      thus ?thesis by simp
    next
      fix b es assume env: "env = Env b es"
      show ?thesis
      proof (cases "es x")
        assume "es x = None"
        with env show ?thesis by simp
      next
        fix e assume es: "es x = Some e"
        show ?thesis
        proof (cases "lookup e xs")
          case None
          hence "lookup e (xs @ ys) = None" by (rule hyp)
          with env es show ?thesis by simp
        next
          case Some
          with asm env es have False by simp
          thus ?thesis ..
        qed
      qed
    qed
  }
qed

theorem lookup_append_some:
  "!!env e. lookup env xs = Some e ==> lookup env (xs @ ys) = lookup e ys"
  (is "PROP ?P xs")
proof (induct xs)
  fix env e :: "('a, 'b, 'c) env"
  {
    assume "lookup env [] = Some e"
    hence "env = e" by simp
    thus "lookup env ([] @ ys) = lookup e ys" by simp
  next
    fix x xs
    assume hyp: "PROP ?P xs"
    assume asm: "lookup env (x # xs) = Some e"
    show "lookup env ((x # xs) @ ys) = lookup e ys"
    proof (cases env)
      fix a assume "env = Val a"
      with asm have False by simp
      thus ?thesis ..
    next
      fix b es assume env: "env = Env b es"
      show ?thesis
      proof (cases "es x")
        assume "es x = None"
        with asm env have False by simp
        thus ?thesis ..
      next
        fix e' assume es: "es x = Some e'"
        show ?thesis
        proof (cases "lookup e' xs")
          case None
          with asm env es have False by simp
          thus ?thesis ..
        next
          case Some
          with asm env es have "lookup e' xs = Some e"
            by simp
          hence "lookup e' (xs @ ys) = lookup e ys" by (rule hyp)
          with env es show ?thesis by simp
        qed
      qed
    qed
  }
qed

text {*
  \medskip Successful @{term lookup} deeper down an environment
  structure means we are able to peek further up as well.  Note that
  this is basically just the contrapositive statement of @{thm
  [source] lookup_append_none} above.
*}

theorem lookup_some_append:
  "lookup env (xs @ ys) = Some e ==> \<exists>e. lookup env xs = Some e"
proof -
  assume "lookup env (xs @ ys) = Some e"
  hence "lookup env (xs @ ys) \<noteq> None" by simp
  hence "lookup env xs \<noteq> None"
    by (rule contrapos_nn) (simp only: lookup_append_none)
  thus ?thesis by simp
qed

text {*
  The subsequent statement describes in more detail how a successful
  @{term lookup} with a non-empty path results in a certain situation
  at any upper position.
*}

theorem lookup_some_upper: "!!env e.
  lookup env (xs @ y # ys) = Some e ==>
    \<exists>b' es' env'.
      lookup env xs = Some (Env b' es') \<and>
      es' y = Some env' \<and>
      lookup env' ys = Some e"
  (is "PROP ?P xs" is "!!env e. ?A env e xs ==> ?C env e xs")
proof (induct xs)
  fix env e let ?A = "?A env e" and ?C = "?C env e"
  {
    assume "?A []"
    hence "lookup env (y # ys) = Some e" by simp
    then obtain b' es' env' where
        env: "env = Env b' es'" and
        es': "es' y = Some env'" and
        look': "lookup env' ys = Some e"
      by (auto simp add: lookup_eq split: option.splits env.splits)
    from env have "lookup env [] = Some (Env b' es')" by simp
    with es' look' show "?C []" by blast
  next
    fix x xs
    assume hyp: "PROP ?P xs"
    assume "?A (x # xs)"
    then obtain b' es' env' where
        env: "env = Env b' es'" and
        es': "es' x = Some env'" and
        look': "lookup env' (xs @ y # ys) = Some e"
      by (auto simp add: lookup_eq split: option.splits env.splits)
    from hyp [OF look'] obtain b'' es'' env'' where
        upper': "lookup env' xs = Some (Env b'' es'')" and
        es'': "es'' y = Some env''" and
        look'': "lookup env'' ys = Some e"
      by blast
    from env es' upper' have "lookup env (x # xs) = Some (Env b'' es'')"
      by simp
    with es'' look'' show "?C (x # xs)" by blast
  }
qed


subsection {* The update operation *}

text {*
  Update at a certain position in a nested environment may either
  delete an existing entry, or overwrite an existing one.  Note that
  update at undefined positions is simple absorbed, i.e.\ the
  environment is left unchanged.
*}

consts
  update :: "'c list => ('a, 'b, 'c) env option
    => ('a, 'b, 'c) env => ('a, 'b, 'c) env"
  update_option :: "'c list => ('a, 'b, 'c) env option
    => ('a, 'b, 'c) env option => ('a, 'b, 'c) env option"

primrec (update)
  "update xs opt (Val a) =
    (if xs = [] then (case opt of None => Val a | Some e => e)
    else Val a)"
  "update xs opt (Env b es) =
    (case xs of
      [] => (case opt of None => Env b es | Some e => e)
    | y # ys => Env b (es (y := update_option ys opt (es y))))"
  "update_option xs opt None =
    (if xs = [] then opt else None)"
  "update_option xs opt (Some e) =
    (if xs = [] then opt else Some (update xs opt e))"

hide const update_option

text {*
  \medskip The characteristic cases of @{term update} are expressed by
  the following equalities.
*}

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
        None => None
      | Some e => Some (update (y # ys) opt e))))"
  by (cases "es x") simp_all

lemmas update.simps [simp del]
  and update_simps [simp] = update_nil_none update_nil_some
    update_cons_val update_cons_nil_env update_cons_cons_env

lemma update_eq:
  "update xs opt env =
    (case xs of
      [] =>
        (case opt of
          None => env
        | Some e => e)
    | x # xs =>
        (case env of
          Val a => Val a
        | Env b es =>
            (case xs of
              [] => Env b (es (x := opt))
            | y # ys =>
                Env b (es (x :=
                  (case es x of
                    None => None
                  | Some e => Some (update (y # ys) opt e)))))))"
  by (simp split: list.split env.split option.split)

text {*
  \medskip The most basic correspondence of @{term lookup} and @{term
  update} states that after @{term update} at a defined position,
  subsequent @{term lookup} operations would yield the new value.
*}

theorem lookup_update_some:
  "!!env e. lookup env xs = Some e ==>
    lookup (update xs (Some env') env) xs = Some env'"
  (is "PROP ?P xs")
proof (induct xs)
  fix env e :: "('a, 'b, 'c) env"
  {
    assume "lookup env [] = Some e"
    hence "env = e" by simp
    thus "lookup (update [] (Some env') env) [] = Some env'"
      by simp
  next
    fix x xs
    assume hyp: "PROP ?P xs"
    assume asm: "lookup env (x # xs) = Some e"
    show "lookup (update (x # xs) (Some env') env) (x # xs) = Some env'"
    proof (cases env)
      fix a assume "env = Val a"
      with asm have False by simp
      thus ?thesis ..
    next
      fix b es assume env: "env = Env b es"
      show ?thesis
      proof (cases "es x")
        assume "es x = None"
        with asm env have False by simp
        thus ?thesis ..
      next
        fix e' assume es: "es x = Some e'"
        show ?thesis
        proof (cases xs)
          assume "xs = []"
          with env show ?thesis by simp
        next
          fix x' xs' assume xs: "xs = x' # xs'"
          from asm env es have "lookup e' xs = Some e" by simp
          hence "lookup (update xs (Some env') e') xs = Some env'" by (rule hyp)
          with env es xs show ?thesis by simp
        qed
      qed
    qed
  }
qed

text {*
  \medskip The properties of displaced @{term update} operations are
  analogous to those of @{term lookup} above.  There are two cases:
  below an undefined position @{term update} is absorbed altogether,
  and below a defined positions @{term update} affects subsequent
  @{term lookup} operations in the obvious way.
*}

theorem update_append_none:
  "!!env. lookup env xs = None ==> update (xs @ y # ys) opt env = env"
  (is "PROP ?P xs")
proof (induct xs)
  fix env :: "('a, 'b, 'c) env"
  {
    assume "lookup env [] = None"
    hence False by simp
    thus "update ([] @ y # ys) opt env = env" ..
  next
    fix x xs
    assume hyp: "PROP ?P xs"
    assume asm: "lookup env (x # xs) = None"
    show "update ((x # xs) @ y # ys) opt env = env"
    proof (cases env)
      fix a assume "env = Val a"
      thus ?thesis by simp
    next
      fix b es assume env: "env = Env b es"
      show ?thesis
      proof (cases "es x")
        assume es: "es x = None"
        show ?thesis
          by (cases xs) (simp_all add: es env fun_upd_idem_iff)
      next
        fix e assume es: "es x = Some e"
        show ?thesis
        proof (cases xs)
          assume "xs = []"
          with asm env es have False by simp
          thus ?thesis ..
        next
          fix x' xs' assume xs: "xs = x' # xs'"
          from asm env es have "lookup e xs = None" by simp
          hence "update (xs @ y # ys) opt e = e" by (rule hyp)
          with env es xs show "update ((x # xs) @ y # ys) opt env = env"
            by (simp add: fun_upd_idem_iff)
        qed
      qed
    qed
  }
qed

theorem update_append_some:
  "!!env e. lookup env xs = Some e ==>
    lookup (update (xs @ y # ys) opt env) xs = Some (update (y # ys) opt e)"
  (is "PROP ?P xs")
proof (induct xs)
  fix env e :: "('a, 'b, 'c) env"
  {
    assume "lookup env [] = Some e"
    hence "env = e" by simp
    thus "lookup (update ([] @ y # ys) opt env) [] = Some (update (y # ys) opt e)"
      by simp
  next
    fix x xs
    assume hyp: "PROP ?P xs"
    assume asm: "lookup env (x # xs) = Some e"
    show "lookup (update ((x # xs) @ y # ys) opt env) (x # xs)
      = Some (update (y # ys) opt e)"
    proof (cases env)
      fix a assume "env = Val a"
      with asm have False by simp
      thus ?thesis ..
    next
      fix b es assume env: "env = Env b es"
      show ?thesis
      proof (cases "es x")
        assume "es x = None"
        with asm env have False by simp
        thus ?thesis ..
      next
        fix e' assume es: "es x = Some e'"
        show ?thesis
        proof (cases xs)
          assume xs: "xs = []"
          from asm env es xs have "e = e'" by simp
          with env es xs show ?thesis by simp
        next
          fix x' xs' assume xs: "xs = x' # xs'"
          from asm env es have "lookup e' xs = Some e" by simp
          hence "lookup (update (xs @ y # ys) opt e') xs =
            Some (update (y # ys) opt e)" by (rule hyp)
          with env es xs show ?thesis by simp
        qed
      qed
    qed
  }
qed

text {*
  \medskip Apparently, @{term update} does not affect the result of
  subsequent @{term lookup} operations at independent positions, i.e.\
  in case that the paths for @{term update} and @{term lookup} fork at
  a certain point.
*}

theorem lookup_update_other:
  "!!env. y \<noteq> (z::'c) ==> lookup (update (xs @ z # zs) opt env) (xs @ y # ys) =
    lookup env (xs @ y # ys)"
  (is "PROP ?P xs")
proof (induct xs)
  fix env :: "('a, 'b, 'c) env"
  assume neq: "y \<noteq> z"
  {
    show "lookup (update ([] @ z # zs) opt env) ([] @ y # ys) =
      lookup env ([] @ y # ys)"
    proof (cases env)
      case Val
      thus ?thesis by simp
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
    fix x xs
    assume hyp: "PROP ?P xs"
    show "lookup (update ((x # xs) @ z # zs) opt env) ((x # xs) @ y # ys) =
      lookup env ((x # xs) @ y # ys)"
    proof (cases env)
      case Val
      thus ?thesis by simp
    next
      fix y es assume env: "env = Env y es"
      show ?thesis
      proof (cases xs)
        assume xs: "xs = []"
        show ?thesis
        proof (cases "es x")
          case None
          with env xs show ?thesis by simp
        next
          case Some
          with hyp env xs and neq show ?thesis by simp
        qed
      next
        fix x' xs' assume xs: "xs = x' # xs'"
        show ?thesis
        proof (cases "es x")
          case None
          with env xs show ?thesis by simp
        next
          case Some
          with hyp env xs neq show ?thesis by simp
        qed
      qed
    qed
  }
qed

end
