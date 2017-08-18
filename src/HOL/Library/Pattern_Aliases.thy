(*  Title:      HOL/Library/Pattern_Aliases.thy
    Author:     Lars Hupel, Ondrej Kuncar
*)

section \<open>Input syntax for pattern aliases (or ``as-patterns'' in Haskell)\<close>

theory Pattern_Aliases
imports Main
begin

text \<open>
  Most functional languages (Haskell, ML, Scala) support aliases in patterns. This allows to refer
  to a subpattern with a variable name. This theory implements this using a check phase. It works
  well for function definitions (see usage below).

  The following caveats should be kept in mind:
  \<^item> The translation expects a term of the form @{prop "f x y = rhs"}, where \<open>x\<close> and \<open>y\<close> are patterns
    that may contain aliases. The result of the translation is a nested @{const Let}-expression on
    the right hand side. The code generator \<^emph>\<open>does not\<close> print Isabelle pattern aliases to target
    language pattern aliases.
  \<^item> The translation does not process nested equalities; only the top-level equality is translated.
  \<^item> Terms that do not adhere to the above shape may either stay untranslated or produce an error
    message. The @{command fun} command will complain if pattern aliases are left untranslated.
    In particular, there are no checks whether the patterns are wellformed or linear.
  \<^item> There is no corresonding uncheck phase, because it is unclear in which situations the
    translation should be reversed.
\<close>


subsection \<open>Definition\<close>

consts as :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"

ML\<open>
local

fun let_typ a b = a --> (a --> b) --> b

fun strip_all t =
  case try Logic.dest_all t of
    NONE => ([], t)
  | SOME (var, t) => apfst (cons var) (strip_all t)

fun all_Frees t =
  fold_aterms (fn Free (x, t) => insert op = (x, t) | _ => I) t []

in

fun check_pattern_syntax t =
  case strip_all t of
    (vars, @{const Trueprop} $ (Const (@{const_name HOL.eq}, _) $ lhs $ rhs)) =>
      let
        fun go (Const (@{const_name as}, _) $ pat $ var, rhs) =
              let
                val (pat', rhs') = go (pat, rhs)
                val _ = if is_Free var then () else error "Left-hand side of =: must be a free variable"
                val rhs'' =
                  Const (@{const_name Let}, let_typ (fastype_of var) (fastype_of rhs)) $
                    pat' $ lambda var rhs'
              in
                (pat', rhs'')
              end
          | go (t $ u, rhs) =
              let
                val (t', rhs') = go (t, rhs)
                val (u', rhs'') = go (u, rhs')
              in (t' $ u', rhs'') end
          | go (t, rhs) = (t, rhs)

        val (lhs', rhs') = go (lhs, rhs)

        val res = HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs', rhs'))

        val frees = filter (member op = vars) (all_Frees res)
      in fold (fn v => Logic.dependent_all_name ("", v)) (map Free frees) res end
  | _ => t

end
\<close>

bundle pattern_aliases begin

  notation as (infixr "=:" 1)

  declaration \<open>K (Syntax_Phases.term_check 98 "pattern_syntax" (K (map check_pattern_syntax)))\<close>

end

hide_const (open) as


subsection \<open>Usage\<close>

context includes pattern_aliases begin

text \<open>Not very useful for plain definitions, but works anyway.\<close>

private definition "test_1 x (y =: z) = y + z"

lemma "test_1 x y = y + y"
by (rule test_1_def[unfolded Let_def])

text \<open>Very useful for function definitions.\<close>

private fun test_2 where
"test_2 (y # (y' # ys =: x') =: x) = x @ x'" |
"test_2 _ = []"

lemma "test_2 (y # y' # ys) = (y # y' # ys) @ y' # ys"
by (rule test_2.simps[unfolded Let_def])

end

end