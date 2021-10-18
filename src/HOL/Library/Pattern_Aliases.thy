(*  Title:      HOL/Library/Pattern_Aliases.thy
    Author:     Lars Hupel, Ondrej Kuncar, Tobias Nipkow
*)

section \<open>Input syntax for pattern aliases (or ``as-patterns'' in Haskell)\<close>

theory Pattern_Aliases
imports Main
begin

text \<open>
  Most functional languages (Haskell, ML, Scala) support aliases in patterns. This allows to refer
  to a subpattern with a variable name. This theory implements this using a check phase. It works
  well for function definitions (see usage below). All features are packed into a @{command bundle}.

  The following caveats should be kept in mind:
  \<^item> The translation expects a term of the form \<^prop>\<open>f x y = rhs\<close>, where \<open>x\<close> and \<open>y\<close> are patterns
    that may contain aliases. The result of the translation is a nested \<^const>\<open>Let\<close>-expression on
    the right hand side. The code generator \<^emph>\<open>does not\<close> print Isabelle pattern aliases to target
    language pattern aliases.
  \<^item> The translation does not process nested equalities; only the top-level equality is translated.
  \<^item> Terms that do not adhere to the above shape may either stay untranslated or produce an error
    message. The @{command fun} command will complain if pattern aliases are left untranslated.
    In particular, there are no checks whether the patterns are wellformed or linear.
  \<^item> The corresponding uncheck phase attempts to reverse the translation (no guarantee). The
    additionally introduced variables are bound using a ``fake quantifier'' that does not
    appear in the output.
  \<^item> To obtain reasonable induction principles in function definitions, the bundle also declares
    a custom congruence rule for \<^const>\<open>Let\<close> that only affects @{command fun}. This congruence
    rule might lead to an explosion in term size (although that is rare)! In some circumstances
    (using \<open>let\<close> to destructure tuples), the internal construction of functions stumbles over this
    rule and prints an error. To mitigate this, either
    \<^item> activate the bundle locally (\<^theory_text>\<open>context includes ... begin\<close>) or
    \<^item> rewrite the \<open>let\<close>-expression to use \<open>case\<close>: \<^term>\<open>let (a, b) = x in (b, a)\<close> becomes
      \<^term>\<open>case x of (a, b) \<Rightarrow> (b, a)\<close>.
  \<^item> The bundle also adds the @{thm Let_def} rule to the simpset.
\<close>


subsection \<open>Definition\<close>

consts
  as :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  fake_quant :: "('a \<Rightarrow> prop) \<Rightarrow> prop"

lemma let_cong_unfolding: "M = N \<Longrightarrow> f N = g N \<Longrightarrow> Let M f = Let N g"
by simp

translations "P" <= "CONST fake_quant (\<lambda>x. P)"

ML\<open>
local

fun let_typ a b = a --> (a --> b) --> b
fun as_typ a = a --> a --> a

fun strip_all t =
  case try Logic.dest_all_global t of
    NONE => ([], t)
  | SOME (var, t) => apfst (cons var) (strip_all t)

fun all_Frees t =
  fold_aterms (fn Free (x, t) => insert (op =) (x, t) | _ => I) t []

fun subst_once (old, new) t =
  let
    fun go t =
      if t = old then
        (new, true)
      else
        case t of
          u $ v =>
            let
              val (u', substituted) = go u
            in
              if substituted then
                (u' $ v, true)
              else
                case go v of (v', substituted) => (u $ v', substituted)
            end
        | Abs (name, typ, t) =>
            (case go t of (t', substituted) => (Abs (name, typ, t'), substituted))
        | _ => (t, false)
  in fst (go t) end

(* adapted from logic.ML *)
fun fake_const T = Const (\<^const_name>\<open>fake_quant\<close>, (T --> propT) --> propT);

fun dependent_fake_name v t =
  let
    val x = Term.term_name v
    val T = Term.fastype_of v
    val t' = Term.abstract_over (v, t)
  in if Term.is_dependent t' then fake_const T $ Abs (x, T, t') else t end

in

fun check_pattern_syntax t =
  case strip_all t of
    (vars, \<^Const>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>HOL.eq\<close>, _) $ lhs $ rhs)) =>
      let
        fun go (Const (\<^const_name>\<open>as\<close>, _) $ pat $ var, rhs) =
              let
                val (pat', rhs') = go (pat, rhs)
                val _ = if is_Free var then () else error "Right-hand side of =: must be a free variable"
                val rhs'' =
                  Const (\<^const_name>\<open>Let\<close>, let_typ (fastype_of var) (fastype_of rhs)) $
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

        val frees = filter (member (op =) vars) (all_Frees res)
      in fold (fn v => Logic.dependent_all_name ("", v)) (map Free frees) res end
  | _ => t

fun uncheck_pattern_syntax ctxt t =
  case strip_all t of
    (vars, \<^Const>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>HOL.eq\<close>, _) $ lhs $ rhs)) =>
      let
        (* restricted to going down abstractions; ignores eta-contracted rhs *)
        fun go lhs (rhs as Const (\<^const_name>\<open>Let\<close>, _) $ pat $ Abs (name, typ, t)) ctxt frees =
              if exists_subterm (fn t' => t' = pat) lhs then
                let
                  val ([name'], ctxt') = Variable.variant_fixes [name] ctxt
                  val free = Free (name', typ)
                  val subst = (pat, Const (\<^const_name>\<open>as\<close>, as_typ typ) $ pat $ free)
                  val lhs' = subst_once subst lhs
                  val rhs' = subst_bound (free, t)
                in
                  go lhs' rhs' ctxt' (Free (name', typ) :: frees)
                end
              else
                (lhs, rhs, ctxt, frees)
          | go lhs rhs ctxt frees = (lhs, rhs, ctxt, frees)

        val (lhs', rhs', _, frees) = go lhs rhs ctxt []

        val res =
          HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs', rhs'))
          |> fold (fn v => Logic.dependent_all_name ("", v)) (map Free vars)
          |> fold dependent_fake_name frees
      in
        if null frees then t else res
      end
  | _ => t

end
\<close>

bundle pattern_aliases begin

  notation as (infixr "=:" 1)

  declaration \<open>K (Syntax_Phases.term_check 98 "pattern_syntax" (K (map check_pattern_syntax)))\<close>
  declaration \<open>K (Syntax_Phases.term_uncheck 98 "pattern_syntax" (map o uncheck_pattern_syntax))\<close>

  declare let_cong_unfolding [fundef_cong]
  declare Let_def [simp]

end

hide_const as
hide_const fake_quant


subsection \<open>Usage\<close>

context includes pattern_aliases begin

text \<open>Not very useful for plain definitions, but works anyway.\<close>

private definition "test_1 x (y =: z) = y + z"

lemma "test_1 x y = y + y"
by (rule test_1_def[unfolded Let_def])

text \<open>Very useful for function definitions.\<close>

private fun test_2 where
"test_2 (y # (y' # ys =: x') =: x) = x @ x' @ x'" |
"test_2 _ = []"

lemma "test_2 (y # y' # ys) = (y # y' # ys) @ (y' # ys) @ (y' # ys)"
by (rule test_2.simps[unfolded Let_def])

ML\<open>
let
  val actual =
    @{thm test_2.simps(1)}
    |> Thm.prop_of
    |> Syntax.string_of_term \<^context>
    |> YXML.content_of
  val expected = "test_2 (?y # (?y' # ?ys =: x') =: x) = x @ x' @ x'"
in \<^assert> (actual = expected) end
\<close>

end

end
