theory Rewrite_Examples
imports Main "HOL-Library.Rewrite"
begin

section \<open>The rewrite Proof Method by Example\<close>

(* This file is intended to give an overview over
   the features of the pattern-based rewrite proof method.

   See also https://www21.in.tum.de/~noschinl/Pattern-2014/
*)
lemma
  fixes a::int and b::int and c::int
  assumes "P (b + a)"
  shows "P (a + b)"
by (rewrite at "a + b" add.commute)
   (rule assms)

(* Selecting a specific subterm in a large, ambiguous term. *)
lemma
  fixes a b c :: int
  assumes "f (a - a + (a - a)) + f (   0    + c) = f 0 + f c"
  shows   "f (a - a + (a - a)) + f ((a - a) + c) = f 0 + f c"
  by (rewrite in "f _ + f \<hole> = _" diff_self) fact

lemma
  fixes a b c :: int
  assumes "f (a - a +    0   ) + f ((a - a) + c) = f 0 + f c"
  shows   "f (a - a + (a - a)) + f ((a - a) + c) = f 0 + f c"
  by (rewrite at "f (_ + \<hole>) + f _ = _" diff_self) fact

lemma
  fixes a b c :: int
  assumes "f (  0   + (a - a)) + f ((a - a) + c) = f 0 + f c"
  shows   "f (a - a + (a - a)) + f ((a - a) + c) = f 0 + f c"
  by (rewrite in "f (\<hole> + _) + _ = _" diff_self) fact

lemma
  fixes a b c :: int
  assumes "f (a - a +    0   ) + f ((a - a) + c) = f 0 + f c"
  shows   "f (a - a + (a - a)) + f ((a - a) + c) = f 0 + f c"
  by (rewrite in "f (_ + \<hole>) + _ = _" diff_self) fact

lemma
  fixes x y :: nat
  shows"x + y > c \<Longrightarrow> y + x > c"
  by (rewrite at "\<hole> > c" add.commute) assumption

(* We can also rewrite in the assumptions.  *)
lemma
  fixes x y :: nat
  assumes "y + x > c \<Longrightarrow> y + x > c"
  shows   "x + y > c \<Longrightarrow> y + x > c"
  by (rewrite in asm add.commute) fact

lemma
  fixes x y :: nat
  assumes "y + x > c \<Longrightarrow> y + x > c"
  shows   "x + y > c \<Longrightarrow> y + x > c"
  by (rewrite in "x + y > c" at asm add.commute) fact

lemma
  fixes x y :: nat
  assumes "y + x > c \<Longrightarrow> y + x > c"
  shows   "x + y > c \<Longrightarrow> y + x > c"
  by (rewrite at "\<hole> > c" at asm  add.commute) fact

lemma
  assumes "P {x::int. y + 1 = 1 + x}"
  shows   "P {x::int. y + 1 = x + 1}"
  by (rewrite at "x+1" in "{x::int. \<hole> }" add.commute) fact

lemma
  assumes "P {x::int. y + 1 = 1 + x}"
  shows   "P {x::int. y + 1 = x + 1}"
  by (rewrite at "any_identifier_will_work+1" in "{any_identifier_will_work::int. \<hole> }" add.commute)
   fact

lemma
  assumes "P {(x::nat, y::nat, z). x + z * 3 = Q (\<lambda>s t. s * t + y - 3)}"
  shows   "P {(x::nat, y::nat, z). x + z * 3 = Q (\<lambda>s t. y + s * t - 3)}"
  by (rewrite at "b + d * e" in "\<lambda>(a, b, c). _ = Q (\<lambda>d e. \<hole>)" add.commute) fact

(* This is not limited to the first assumption *)
lemma
  assumes "PROP P \<equiv> PROP Q"
  shows "PROP R \<Longrightarrow> PROP P \<Longrightarrow> PROP Q"
    by (rewrite at asm assms)

lemma
  assumes "PROP P \<equiv> PROP Q"
  shows "PROP R \<Longrightarrow> PROP R \<Longrightarrow> PROP P \<Longrightarrow> PROP Q"
    by (rewrite at asm assms)

(* Rewriting "at asm" selects each full assumption, not any parts *)
lemma
  assumes "(PROP P \<Longrightarrow> PROP Q) \<equiv> (PROP S \<Longrightarrow> PROP R)"
  shows "PROP S \<Longrightarrow> (PROP P \<Longrightarrow> PROP Q) \<Longrightarrow> PROP R"
  apply (rewrite at asm assms)
  apply assumption
  done



(* Rewriting with conditional rewriting rules works just as well. *)
lemma test_theorem:
  fixes x :: nat
  shows "x \<le> y \<Longrightarrow> x \<ge> y \<Longrightarrow> x = y"
  by (rule Orderings.order_antisym)

(* Premises of the conditional rule yield new subgoals. The
   assumptions of the goal are propagated into these subgoals
*)
lemma
  fixes f :: "nat \<Rightarrow> nat"
  shows "f x \<le> 0 \<Longrightarrow> f x \<ge> 0 \<Longrightarrow> f x = 0"
  apply (rewrite at "f x" to "0" test_theorem)
  apply assumption
  apply assumption
  apply (rule refl)
  done

(* This holds also for rewriting in assumptions. The order of assumptions is preserved *)
lemma
  assumes rewr: "PROP P \<Longrightarrow> PROP Q \<Longrightarrow> PROP R \<equiv> PROP R'"
  assumes A1: "PROP S \<Longrightarrow> PROP T \<Longrightarrow> PROP U \<Longrightarrow> PROP P"
  assumes A2: "PROP S \<Longrightarrow> PROP T \<Longrightarrow> PROP U \<Longrightarrow> PROP Q"
  assumes C: "PROP S \<Longrightarrow> PROP R' \<Longrightarrow> PROP T \<Longrightarrow> PROP U \<Longrightarrow> PROP V"
  shows "PROP S \<Longrightarrow> PROP R \<Longrightarrow> PROP T \<Longrightarrow> PROP U \<Longrightarrow> PROP V"
  apply (rewrite at asm rewr)
  apply (fact A1)
  apply (fact A2)
  apply (fact C)
  done


(*
   Instantiation.

   Since all rewriting is now done via conversions,
   instantiation becomes fairly easy to do.
*)

(* We first introduce a function f and an extended
   version of f that is annotated with an invariant. *)
fun f :: "nat \<Rightarrow> nat" where "f n = n"
definition "f_inv (I :: nat \<Rightarrow> bool) n \<equiv> f n"

lemma annotate_f: "f = f_inv I"
  by (simp add: f_inv_def fun_eq_iff)

(* We have a lemma with a bound variable n, and
   want to add an invariant to f. *)
lemma
  assumes "P (\<lambda>n. f_inv (\<lambda>_. True) n + 1) = x"
  shows "P (\<lambda>n. f n + 1) = x"
  by (rewrite to "f_inv (\<lambda>_. True)" annotate_f) fact

(* We can also add an invariant that contains the variable n bound in the outer context.
   For this, we need to bind this variable to an identifier. *)
lemma
  assumes "P (\<lambda>n. f_inv (\<lambda>x. n < x + 1) n + 1) = x"
  shows "P (\<lambda>n. f n + 1) = x"
  by (rewrite in "\<lambda>n. \<hole>" to "f_inv (\<lambda>x. n < x + 1)" annotate_f) fact

(* Any identifier will work *)
lemma
  assumes "P (\<lambda>n. f_inv (\<lambda>x. n < x + 1) n + 1) = x"
  shows "P (\<lambda>n. f n + 1) = x"
  by (rewrite in "\<lambda>abc. \<hole>" to "f_inv (\<lambda>x. abc < x + 1)" annotate_f) fact

(* The "for" keyword. *)
lemma
  assumes "P (2 + 1)"
  shows "\<And>x y. P (1 + 2 :: nat)"
by (rewrite in "P (1 + 2)" at for (x) add.commute) fact

lemma
  assumes "\<And>x y. P (y + x)"
  shows "\<And>x y. P (x + y :: nat)"
by (rewrite in "P (x + _)" at for (x y) add.commute) fact

lemma
  assumes "\<And>x y z. y + x + z = z + y + (x::int)"
  shows   "\<And>x y z. x + y + z = z + y + (x::int)"
by (rewrite at "x + y" in "x + y + z" in for (x y z) add.commute) fact

lemma
  assumes "\<And>x y z. z + (x + y) = z + y + (x::int)"
  shows   "\<And>x y z. x + y + z = z + y + (x::int)"
by (rewrite at "(_ + y) + z" in for (y z) add.commute) fact

lemma
  assumes "\<And>x y z. x + y + z = y + z + (x::int)"
  shows   "\<And>x y z. x + y + z = z + y + (x::int)"
by (rewrite at "\<hole> + _" at "_ = \<hole>" in for () add.commute) fact

lemma
  assumes eq: "\<And>x. P x \<Longrightarrow> g x = x"
  assumes f1: "\<And>x. Q x \<Longrightarrow> P x"
  assumes f2: "\<And>x. Q x \<Longrightarrow> x"
  shows "\<And>x. Q x \<Longrightarrow> g x"
  apply (rewrite at "g x" in for (x) eq)
  apply (fact f1)
  apply (fact f2)
  done

(* The for keyword can be used anywhere in the pattern where there is an \<And>-Quantifier. *)
lemma
  assumes "(\<And>(x::int). x < 1 + x)"
  and     "(x::int) + 1 > x"
  shows   "(\<And>(x::int). x + 1 > x) \<Longrightarrow> (x::int) + 1 > x"
by (rewrite at "x + 1" in for (x) at asm add.commute)
   (rule assms)

(* The rewrite method also has an ML interface *)
lemma
  assumes "\<And>a b. P ((a + 1) * (1 + b)) "
  shows "\<And>a b :: nat. P ((a + 1) * (b + 1))"
  apply (tactic \<open>
    let
      val (x, ctxt) = yield_singleton Variable.add_fixes "x" \<^context>
      (* Note that the pattern order is reversed *)
      val pat = [
        Rewrite.For [(x, SOME \<^Type>\<open>nat\<close>)],
        Rewrite.In,
        Rewrite.Term (\<^Const>\<open>plus \<^Type>\<open>nat\<close> for \<open>Free (x, \<^Type>\<open>nat\<close>)\<close> \<^term>\<open>1 :: nat\<close>\<close>, [])]
      val to = NONE
    in CCONVERSION (Rewrite.rewrite_conv ctxt (pat, to) @{thms add.commute}) 1 end
  \<close>)
  apply (fact assms)
  done

lemma
  assumes "Q (\<lambda>b :: int. P (\<lambda>a. a + b) (\<lambda>a. a + b))"
  shows "Q (\<lambda>b :: int. P (\<lambda>a. a + b) (\<lambda>a. b + a))"
  apply (tactic \<open>
    let
      val (x, ctxt) = yield_singleton Variable.add_fixes "x" \<^context>
      val pat = [
        Rewrite.Concl,
        Rewrite.In,
        Rewrite.Term (Free ("Q", (\<^Type>\<open>int\<close> --> TVar (("'b",0), [])) --> \<^Type>\<open>bool\<close>)
          $ Abs ("x", \<^Type>\<open>int\<close>, Rewrite.mk_hole 1 (\<^Type>\<open>int\<close> --> TVar (("'b",0), [])) $ Bound 0), [(x, \<^Type>\<open>int\<close>)]),
        Rewrite.In,
        Rewrite.Term (\<^Const>\<open>plus \<^Type>\<open>int\<close> for \<open>Free (x, \<^Type>\<open>int\<close>)\<close> \<open>Var (("c", 0), \<^Type>\<open>int\<close>)\<close>\<close>, [])
        ]
      val to = NONE
    in CCONVERSION (Rewrite.rewrite_conv ctxt (pat, to) @{thms add.commute}) 1 end
  \<close>)
  apply (fact assms)
  done

(* There is also conversion-like rewrite function: *)
ML \<open>
  val ct = \<^cprop>\<open>Q (\<lambda>b :: int. P (\<lambda>a. a + b) (\<lambda>a. b + a))\<close>
  val (x, ctxt) = yield_singleton Variable.add_fixes "x" \<^context>
  val pat = [
    Rewrite.Concl,
    Rewrite.In,
    Rewrite.Term (Free ("Q", (\<^typ>\<open>int\<close> --> TVar (("'b",0), [])) --> \<^typ>\<open>bool\<close>)
      $ Abs ("x", \<^typ>\<open>int\<close>, Rewrite.mk_hole 1 (\<^typ>\<open>int\<close> --> TVar (("'b",0), [])) $ Bound 0), [(x, \<^typ>\<open>int\<close>)]),
    Rewrite.In,
    Rewrite.Term (\<^Const>\<open>plus \<^Type>\<open>int\<close> for \<open>Free (x, \<^Type>\<open>int\<close>)\<close> \<open>Var (("c", 0), \<^Type>\<open>int\<close>)\<close>\<close>, [])
    ]
  val to = NONE
  val th = Rewrite.rewrite_conv ctxt (pat, to) @{thms add.commute} ct
\<close>

section \<open>Regression tests\<close>

ML \<open>
  val ct = \<^cterm>\<open>(\<lambda>b :: int. (\<lambda>a. b + a))\<close>
  val (x, ctxt) = yield_singleton Variable.add_fixes "x" \<^context>
  val pat = [
    Rewrite.In,
    Rewrite.Term (\<^Const>\<open>plus \<^Type>\<open>int\<close> for \<open>Var (("c", 0), \<^Type>\<open>int\<close>)\<close> \<open>Var (("c", 0), \<^Type>\<open>int\<close>)\<close>\<close>, [])
    ]
  val to = NONE
  val _ =
    case try (Rewrite.rewrite_conv ctxt (pat, to) @{thms add.commute}) ct of
      NONE => ()
    | _ => error "should not have matched anything"
\<close>

ML \<open>
  Rewrite.params_pconv (Conv.all_conv |> K |> K) \<^context> (Vartab.empty, []) \<^cterm>\<open>\<And>x. PROP A\<close>
\<close>

lemma
  assumes eq: "PROP A \<Longrightarrow> PROP B \<equiv> PROP C"
  assumes f1: "PROP D \<Longrightarrow> PROP A"
  assumes f2: "PROP D \<Longrightarrow> PROP C"
  shows "\<And>x. PROP D \<Longrightarrow> PROP B"
  apply (rewrite eq)
  apply (fact f1)
  apply (fact f2)
  done

end
