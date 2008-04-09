(*  Title:      HOL/Library/State_Monad.thy
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen
*)

header {* Combinators syntax for generic, open state monads (single threaded monads) *}

theory State_Monad
imports List
begin

subsection {* Motivation *}

text {*
  The logic HOL has no notion of constructor classes, so
  it is not possible to model monads the Haskell way
  in full genericity in Isabelle/HOL.
  
  However, this theory provides substantial support for
  a very common class of monads: \emph{state monads}
  (or \emph{single-threaded monads}, since a state
  is transformed single-threaded).

  To enter from the Haskell world,
  \url{http://www.engr.mun.ca/~theo/Misc/haskell_and_monads.htm}
  makes a good motivating start.  Here we just sketch briefly
  how those monads enter the game of Isabelle/HOL.
*}

subsection {* State transformations and combinators *}

text {*
  We classify functions operating on states into two categories:

  \begin{description}
    \item[transformations]
      with type signature @{text "\<sigma> \<Rightarrow> \<sigma>'"},
      transforming a state.
    \item[``yielding'' transformations]
      with type signature @{text "\<sigma> \<Rightarrow> \<alpha> \<times> \<sigma>'"},
      ``yielding'' a side result while transforming a state.
    \item[queries]
      with type signature @{text "\<sigma> \<Rightarrow> \<alpha>"},
      computing a result dependent on a state.
  \end{description}

  By convention we write @{text "\<sigma>"} for types representing states
  and @{text "\<alpha>"}, @{text "\<beta>"}, @{text "\<gamma>"}, @{text "\<dots>"}
  for types representing side results.  Type changes due
  to transformations are not excluded in our scenario.

  We aim to assert that values of any state type @{text "\<sigma>"}
  are used in a single-threaded way: after application
  of a transformation on a value of type @{text "\<sigma>"}, the
  former value should not be used again.  To achieve this,
  we use a set of monad combinators:
*}

notation fcomp (infixl ">>" 60)
notation (xsymbols) fcomp (infixl "\<guillemotright>" 60)
notation scomp (infixl ">>=" 60)
notation (xsymbols) scomp (infixl "\<guillemotright>=" 60)

abbreviation (input)
  "return \<equiv> Pair"

definition
  run :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" where
  "run f = f"

print_ast_translation {*
  [(@{const_syntax "run"}, fn (f::ts) => Syntax.mk_appl f ts)]
*}

text {*
  Given two transformations @{term f} and @{term g}, they
  may be directly composed using the @{term "op \<guillemotright>"} combinator,
  forming a forward composition: @{prop "(f \<guillemotright> g) s = f (g s)"}.

  After any yielding transformation, we bind the side result
  immediately using a lambda abstraction.  This 
  is the purpose of the @{term "op \<guillemotright>="} combinator:
  @{prop "(f \<guillemotright>= (\<lambda>x. g)) s = (let (x, s') = f s in g s')"}.

  For queries, the existing @{term "Let"} is appropriate.

  Naturally, a computation may yield a side result by pairing
  it to the state from the left;  we introduce the
  suggestive abbreviation @{term return} for this purpose.

  The @{const run} ist just a marker.

  The most crucial distinction to Haskell is that we do
  not need to introduce distinguished type constructors
  for different kinds of state.  This has two consequences:
  \begin{itemize}
    \item The monad model does not state anything about
       the kind of state; the model for the state is
       completely orthogonal and may be
       specified completely independently.
    \item There is no distinguished type constructor
       encapsulating away the state transformation, i.e.~transformations
       may be applied directly without using any lifting
       or providing and dropping units (``open monad'').
    \item The type of states may change due to a transformation.
  \end{itemize}
*}


subsection {* Obsolete runs *}

text {*
  @{term run} is just a doodle and should not occur nested:
*}

lemma run_simp [simp]:
  "\<And>f. run (run f) = run f"
  "\<And>f g. run f \<guillemotright>= g = f \<guillemotright>= g"
  "\<And>f g. run f \<guillemotright> g = f \<guillemotright> g"
  "\<And>f g. f \<guillemotright>= (\<lambda>x. run g) = f \<guillemotright>= (\<lambda>x. g)"
  "\<And>f g. f \<guillemotright> run g = f \<guillemotright> g"
  "\<And>f. f = run f \<longleftrightarrow> True"
  "\<And>f. run f = f \<longleftrightarrow> True"
  unfolding run_def by rule+

subsection {* Monad laws *}

text {*
  The common monadic laws hold and may also be used
  as normalization rules for monadic expressions:
*}

lemma
  return_scomp [simp]: "return x \<guillemotright>= f = f x"
  unfolding scomp_def by (simp add: expand_fun_eq)

lemma
  scomp_return [simp]: "x \<guillemotright>= return = x"
  unfolding scomp_def by (simp add: expand_fun_eq split_Pair)

lemma
  id_fcomp [simp]: "id \<guillemotright> f = f"
  unfolding fcomp_def by simp

lemma
  fcomp_id [simp]: "f \<guillemotright> id = f"
  unfolding fcomp_def by simp

lemma
  scomp_scomp [simp]: "(f \<guillemotright>= g) \<guillemotright>= h = f \<guillemotright>= (\<lambda>x. g x \<guillemotright>= h)"
  unfolding scomp_def by (simp add: split_def expand_fun_eq)

lemma
  scomp_fcomp [simp]: "(f \<guillemotright>= g) \<guillemotright> h = f \<guillemotright>= (\<lambda>x. g x \<guillemotright> h)"
  unfolding scomp_def fcomp_def by (simp add: split_def expand_fun_eq)

lemma
  fcomp_scomp [simp]: "(f \<guillemotright> g) \<guillemotright>= h = f \<guillemotright> (g \<guillemotright>= h)"
  unfolding scomp_def fcomp_def by (simp add: split_def expand_fun_eq)

lemma
  fcomp_fcomp [simp]: "(f \<guillemotright> g) \<guillemotright> h = f \<guillemotright> (g \<guillemotright> h)"
  unfolding fcomp_def o_assoc ..

lemmas monad_simp = run_simp return_scomp scomp_return id_fcomp fcomp_id
  scomp_scomp scomp_fcomp fcomp_scomp fcomp_fcomp

text {*
  Evaluation of monadic expressions by force:
*}

lemmas monad_collapse = monad_simp o_apply o_assoc split_Pair split_comp
  scomp_def fcomp_def run_def

subsection {* ML abstract operations *}

ML {*
structure StateMonad =
struct

fun liftT T sT = sT --> HOLogic.mk_prodT (T, sT);
fun liftT' sT = sT --> sT;

fun return T sT x = Const (@{const_name return}, T --> liftT T sT) $ x;

fun scomp T1 T2 sT f g = Const (@{const_name scomp},
  liftT T1 sT --> (T1 --> liftT T2 sT) --> liftT T2 sT) $ f $ g;

fun run T sT f = Const (@{const_name run}, liftT' (liftT T sT)) $ f;

end;
*}


subsection {* Syntax *}

text {*
  We provide a convenient do-notation for monadic expressions
  well-known from Haskell.  @{const Let} is printed
  specially in do-expressions.
*}

nonterminals do_expr

syntax
  "_do" :: "do_expr \<Rightarrow> 'a"
    ("do _ done" [12] 12)
  "_scomp" :: "pttrn \<Rightarrow> 'a \<Rightarrow> do_expr \<Rightarrow> do_expr"
    ("_ <- _;// _" [1000, 13, 12] 12)
  "_fcomp" :: "'a \<Rightarrow> do_expr \<Rightarrow> do_expr"
    ("_;// _" [13, 12] 12)
  "_let" :: "pttrn \<Rightarrow> 'a \<Rightarrow> do_expr \<Rightarrow> do_expr"
    ("let _ = _;// _" [1000, 13, 12] 12)
  "_nil" :: "'a \<Rightarrow> do_expr"
    ("_" [12] 12)

syntax (xsymbols)
  "_scomp" :: "pttrn \<Rightarrow> 'a \<Rightarrow> do_expr \<Rightarrow> do_expr"
    ("_ \<leftarrow> _;// _" [1000, 13, 12] 12)

translations
  "_do f" => "CONST run f"
  "_scomp x f g" => "f \<guillemotright>= (\<lambda>x. g)"
  "_fcomp f g" => "f \<guillemotright> g"
  "_let x t f" => "CONST Let t (\<lambda>x. f)"
  "_nil f" => "f"

print_translation {*
let
  fun dest_abs_eta (Abs (abs as (_, ty, _))) =
        let
          val (v, t) = Syntax.variant_abs abs;
        in ((v, ty), t) end
    | dest_abs_eta t =
        let
          val (v, t) = Syntax.variant_abs ("", dummyT, t $ Bound 0);
        in ((v, dummyT), t) end
  fun unfold_monad (Const (@{const_syntax scomp}, _) $ f $ g) =
        let
          val ((v, ty), g') = dest_abs_eta g;
        in Const ("_scomp", dummyT) $ Free (v, ty) $ f $ unfold_monad g' end
    | unfold_monad (Const (@{const_syntax fcomp}, _) $ f $ g) =
        Const ("_fcomp", dummyT) $ f $ unfold_monad g
    | unfold_monad (Const (@{const_syntax Let}, _) $ f $ g) =
        let
          val ((v, ty), g') = dest_abs_eta g;
        in Const ("_let", dummyT) $ Free (v, ty) $ f $ unfold_monad g' end
    | unfold_monad (Const (@{const_syntax Pair}, _) $ f) =
        Const ("return", dummyT) $ f
    | unfold_monad f = f;
  fun tr' (f::ts) =
    list_comb (Const ("_do", dummyT) $ unfold_monad f, ts)
in [(@{const_syntax "run"}, tr')] end;
*}


subsection {* Combinators *}

definition
  lift :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'c \<Rightarrow> 'b \<times> 'c" where
  "lift f x = return (f x)"

primrec
  list :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b" where
  "list f [] = id"
| "list f (x#xs) = (do f x; list f xs done)"

primrec
  list_yield :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<times> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'c list \<times> 'b" where
  "list_yield f [] = return []"
| "list_yield f (x#xs) = (do y \<leftarrow> f x; ys \<leftarrow> list_yield f xs; return (y#ys) done)"

definition
  collapse :: "('a \<Rightarrow> ('a \<Rightarrow> 'b \<times> 'a) \<times> 'a) \<Rightarrow> 'a \<Rightarrow> 'b \<times> 'a" where
  "collapse f = (do g \<leftarrow> f; g done)"

text {* combinator properties *}

lemma list_append [simp]:
  "list f (xs @ ys) = list f xs \<guillemotright> list f ys"
  by (induct xs) (simp_all del: id_apply)

lemma list_cong [fundef_cong, recdef_cong]:
  "\<lbrakk> \<And>x. x \<in> set xs \<Longrightarrow> f x = g x; xs = ys \<rbrakk>
    \<Longrightarrow> list f xs = list g ys"
proof (induct xs arbitrary: ys)
  case Nil then show ?case by simp
next
  case (Cons x xs)
  from Cons have "\<And>y. y \<in> set (x # xs) \<Longrightarrow> f y = g y" by auto
  then have "\<And>y. y \<in> set xs \<Longrightarrow> f y = g y" by auto
  with Cons have "list f xs = list g xs" by auto
  with Cons have "list f (x # xs) = list g (x # xs)" by auto
  with Cons show "list f (x # xs) = list g ys" by auto
qed

lemma list_yield_cong [fundef_cong, recdef_cong]:
  "\<lbrakk> \<And>x. x \<in> set xs \<Longrightarrow> f x = g x; xs = ys \<rbrakk>
    \<Longrightarrow> list_yield f xs = list_yield g ys"
proof (induct xs arbitrary: ys)
  case Nil then show ?case by simp
next
  case (Cons x xs)
  from Cons have "\<And>y. y \<in> set (x # xs) \<Longrightarrow> f y = g y" by auto
  then have "\<And>y. y \<in> set xs \<Longrightarrow> f y = g y" by auto
  with Cons have "list_yield f xs = list_yield g xs" by auto
  with Cons have "list_yield f (x # xs) = list_yield g (x # xs)" by auto
  with Cons show "list_yield f (x # xs) = list_yield g ys" by auto
qed

text {*
  For an example, see HOL/ex/Random.thy.
*}

end
