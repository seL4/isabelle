(*  Title:      HOL/Product_Type.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge
*)

header {* Cartesian products *}

theory Product_Type
imports Typedef Inductive Fun
uses
  ("Tools/split_rule.ML")
  ("Tools/inductive_set.ML")
begin

subsection {* @{typ bool} is a datatype *}

rep_datatype True False by (auto intro: bool_induct)

declare case_split [cases type: bool]
  -- "prefer plain propositional version"

lemma
  shows [code]: "HOL.equal False P \<longleftrightarrow> \<not> P"
    and [code]: "HOL.equal True P \<longleftrightarrow> P" 
    and [code]: "HOL.equal P False \<longleftrightarrow> \<not> P" 
    and [code]: "HOL.equal P True \<longleftrightarrow> P"
    and [code nbe]: "HOL.equal P P \<longleftrightarrow> True"
  by (simp_all add: equal)

lemma If_case_cert:
  assumes "CASE \<equiv> (\<lambda>b. If b f g)"
  shows "(CASE True \<equiv> f) &&& (CASE False \<equiv> g)"
  using assms by simp_all

setup {*
  Code.add_case @{thm If_case_cert}
*}

code_const "HOL.equal \<Colon> bool \<Rightarrow> bool \<Rightarrow> bool"
  (Haskell infix 4 "==")

code_instance bool :: equal
  (Haskell -)


subsection {* The @{text unit} type *}

typedef (open) unit = "{True}"
  by auto

definition Unity :: unit  ("'(')")
  where "() = Abs_unit True"

lemma unit_eq [no_atp]: "u = ()"
  by (induct u) (simp add: Unity_def)

text {*
  Simplification procedure for @{thm [source] unit_eq}.  Cannot use
  this rule directly --- it loops!
*}

simproc_setup unit_eq ("x::unit") = {*
  fn _ => fn _ => fn ct =>
    if HOLogic.is_unit (term_of ct) then NONE
    else SOME (mk_meta_eq @{thm unit_eq})
*}

rep_datatype "()" by simp

lemma unit_all_eq1: "(!!x::unit. PROP P x) == PROP P ()"
  by simp

lemma unit_all_eq2: "(!!x::unit. PROP P) == PROP P"
  by (rule triv_forall_equality)

text {*
  This rewrite counters the effect of simproc @{text unit_eq} on @{term
  [source] "%u::unit. f u"}, replacing it by @{term [source]
  f} rather than by @{term [source] "%u. f ()"}.
*}

lemma unit_abs_eta_conv [simp, no_atp]: "(%u::unit. f ()) = f"
  by (rule ext) simp

lemma UNIV_unit [no_atp]:
  "UNIV = {()}" by auto

instantiation unit :: default
begin

definition "default = ()"

instance ..

end

lemma [code]:
  "HOL.equal (u\<Colon>unit) v \<longleftrightarrow> True" unfolding equal unit_eq [of u] unit_eq [of v] by rule+

code_type unit
  (SML "unit")
  (OCaml "unit")
  (Haskell "()")
  (Scala "Unit")

code_const Unity
  (SML "()")
  (OCaml "()")
  (Haskell "()")
  (Scala "()")

code_instance unit :: equal
  (Haskell -)

code_const "HOL.equal \<Colon> unit \<Rightarrow> unit \<Rightarrow> bool"
  (Haskell infix 4 "==")

code_reserved SML
  unit

code_reserved OCaml
  unit

code_reserved Scala
  Unit


subsection {* The product type *}

subsubsection {* Type definition *}

definition Pair_Rep :: "'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool" where
  "Pair_Rep a b = (\<lambda>x y. x = a \<and> y = b)"

definition "prod = {f. \<exists>a b. f = Pair_Rep (a\<Colon>'a) (b\<Colon>'b)}"

typedef (open) ('a, 'b) prod (infixr "*" 20) = "prod :: ('a \<Rightarrow> 'b \<Rightarrow> bool) set"
  unfolding prod_def by auto

type_notation (xsymbols)
  "prod"  ("(_ \<times>/ _)" [21, 20] 20)
type_notation (HTML output)
  "prod"  ("(_ \<times>/ _)" [21, 20] 20)

definition Pair :: "'a \<Rightarrow> 'b \<Rightarrow> 'a \<times> 'b" where
  "Pair a b = Abs_prod (Pair_Rep a b)"

rep_datatype Pair proof -
  fix P :: "'a \<times> 'b \<Rightarrow> bool" and p
  assume "\<And>a b. P (Pair a b)"
  then show "P p" by (cases p) (auto simp add: prod_def Pair_def Pair_Rep_def)
next
  fix a c :: 'a and b d :: 'b
  have "Pair_Rep a b = Pair_Rep c d \<longleftrightarrow> a = c \<and> b = d"
    by (auto simp add: Pair_Rep_def fun_eq_iff)
  moreover have "Pair_Rep a b \<in> prod" and "Pair_Rep c d \<in> prod"
    by (auto simp add: prod_def)
  ultimately show "Pair a b = Pair c d \<longleftrightarrow> a = c \<and> b = d"
    by (simp add: Pair_def Abs_prod_inject)
qed

declare prod.simps(2) [nitpick_simp del]

declare prod.weak_case_cong [cong del]


subsubsection {* Tuple syntax *}

abbreviation (input) split :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'c" where
  "split \<equiv> prod_case"

text {*
  Patterns -- extends pre-defined type @{typ pttrn} used in
  abstractions.
*}

nonterminal tuple_args and patterns

syntax
  "_tuple"      :: "'a => tuple_args => 'a * 'b"        ("(1'(_,/ _'))")
  "_tuple_arg"  :: "'a => tuple_args"                   ("_")
  "_tuple_args" :: "'a => tuple_args => tuple_args"     ("_,/ _")
  "_pattern"    :: "[pttrn, patterns] => pttrn"         ("'(_,/ _')")
  ""            :: "pttrn => patterns"                  ("_")
  "_patterns"   :: "[pttrn, patterns] => patterns"      ("_,/ _")

translations
  "(x, y)" == "CONST Pair x y"
  "_tuple x (_tuple_args y z)" == "_tuple x (_tuple_arg (_tuple y z))"
  "%(x, y, zs). b" == "CONST prod_case (%x (y, zs). b)"
  "%(x, y). b" == "CONST prod_case (%x y. b)"
  "_abs (CONST Pair x y) t" => "%(x, y). t"
  -- {* The last rule accommodates tuples in `case C ... (x,y) ... => ...'
     The (x,y) is parsed as `Pair x y' because it is logic, not pttrn *}

(*reconstruct pattern from (nested) splits, avoiding eta-contraction of body;
  works best with enclosing "let", if "let" does not avoid eta-contraction*)
print_translation {*
let
  fun split_tr' [Abs (x, T, t as (Abs abs))] =
        (* split (%x y. t) => %(x,y) t *)
        let
          val (y, t') = Syntax_Trans.atomic_abs_tr' abs;
          val (x', t'') = Syntax_Trans.atomic_abs_tr' (x, T, t');
        in
          Syntax.const @{syntax_const "_abs"} $
            (Syntax.const @{syntax_const "_pattern"} $ x' $ y) $ t''
        end
    | split_tr' [Abs (x, T, (s as Const (@{const_syntax prod_case}, _) $ t))] =
        (* split (%x. (split (%y z. t))) => %(x,y,z). t *)
        let
          val Const (@{syntax_const "_abs"}, _) $
            (Const (@{syntax_const "_pattern"}, _) $ y $ z) $ t' = split_tr' [t];
          val (x', t'') = Syntax_Trans.atomic_abs_tr' (x, T, t');
        in
          Syntax.const @{syntax_const "_abs"} $
            (Syntax.const @{syntax_const "_pattern"} $ x' $
              (Syntax.const @{syntax_const "_patterns"} $ y $ z)) $ t''
        end
    | split_tr' [Const (@{const_syntax prod_case}, _) $ t] =
        (* split (split (%x y z. t)) => %((x, y), z). t *)
        split_tr' [(split_tr' [t])] (* inner split_tr' creates next pattern *)
    | split_tr' [Const (@{syntax_const "_abs"}, _) $ x_y $ Abs abs] =
        (* split (%pttrn z. t) => %(pttrn,z). t *)
        let val (z, t) = Syntax_Trans.atomic_abs_tr' abs in
          Syntax.const @{syntax_const "_abs"} $
            (Syntax.const @{syntax_const "_pattern"} $ x_y $ z) $ t
        end
    | split_tr' _ = raise Match;
in [(@{const_syntax prod_case}, split_tr')] end
*}

(* print "split f" as "\<lambda>(x,y). f x y" and "split (\<lambda>x. f x)" as "\<lambda>(x,y). f x y" *) 
typed_print_translation {*
let
  fun split_guess_names_tr' T [Abs (x, _, Abs _)] = raise Match
    | split_guess_names_tr' T [Abs (x, xT, t)] =
        (case (head_of t) of
          Const (@{const_syntax prod_case}, _) => raise Match
        | _ =>
          let 
            val (_ :: yT :: _) = binder_types (domain_type T) handle Bind => raise Match;
            val (y, t') = Syntax_Trans.atomic_abs_tr' ("y", yT, incr_boundvars 1 t $ Bound 0);
            val (x', t'') = Syntax_Trans.atomic_abs_tr' (x, xT, t');
          in
            Syntax.const @{syntax_const "_abs"} $
              (Syntax.const @{syntax_const "_pattern"} $ x' $ y) $ t''
          end)
    | split_guess_names_tr' T [t] =
        (case head_of t of
          Const (@{const_syntax prod_case}, _) => raise Match
        | _ =>
          let
            val (xT :: yT :: _) = binder_types (domain_type T) handle Bind => raise Match;
            val (y, t') =
              Syntax_Trans.atomic_abs_tr' ("y", yT, incr_boundvars 2 t $ Bound 1 $ Bound 0);
            val (x', t'') = Syntax_Trans.atomic_abs_tr' ("x", xT, t');
          in
            Syntax.const @{syntax_const "_abs"} $
              (Syntax.const @{syntax_const "_pattern"} $ x' $ y) $ t''
          end)
    | split_guess_names_tr' _ _ = raise Match;
in [(@{const_syntax prod_case}, split_guess_names_tr')] end
*}

(* Force eta-contraction for terms of the form "Q A (%p. prod_case P p)"
   where Q is some bounded quantifier or set operator.
   Reason: the above prints as "Q p : A. case p of (x,y) \<Rightarrow> P x y"
   whereas we want "Q (x,y):A. P x y".
   Otherwise prevent eta-contraction.
*)
print_translation {*
let
  fun contract Q f ts =
    case ts of
      [A, Abs(_, _, (s as Const (@{const_syntax prod_case},_) $ t) $ Bound 0)]
      => if Term.is_dependent t then f ts else Syntax.const Q $ A $ s
    | _ => f ts;
  fun contract2 (Q,f) = (Q, contract Q f);
  val pairs =
    [Syntax_Trans.preserve_binder_abs2_tr' @{const_syntax Ball} @{syntax_const "_Ball"},
     Syntax_Trans.preserve_binder_abs2_tr' @{const_syntax Bex} @{syntax_const "_Bex"},
     Syntax_Trans.preserve_binder_abs2_tr' @{const_syntax INFI} @{syntax_const "_INF"},
     Syntax_Trans.preserve_binder_abs2_tr' @{const_syntax SUPR} @{syntax_const "_SUP"}]
in map contract2 pairs end
*}

subsubsection {* Code generator setup *}

code_type prod
  (SML infix 2 "*")
  (OCaml infix 2 "*")
  (Haskell "!((_),/ (_))")
  (Scala "((_),/ (_))")

code_const Pair
  (SML "!((_),/ (_))")
  (OCaml "!((_),/ (_))")
  (Haskell "!((_),/ (_))")
  (Scala "!((_),/ (_))")

code_instance prod :: equal
  (Haskell -)

code_const "HOL.equal \<Colon> 'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool"
  (Haskell infix 4 "==")


subsubsection {* Fundamental operations and properties *}

lemma surj_pair [simp]: "EX x y. p = (x, y)"
  by (cases p) simp

definition fst :: "'a \<times> 'b \<Rightarrow> 'a" where
  "fst p = (case p of (a, b) \<Rightarrow> a)"

definition snd :: "'a \<times> 'b \<Rightarrow> 'b" where
  "snd p = (case p of (a, b) \<Rightarrow> b)"

lemma fst_conv [simp, code]: "fst (a, b) = a"
  unfolding fst_def by simp

lemma snd_conv [simp, code]: "snd (a, b) = b"
  unfolding snd_def by simp

code_const fst and snd
  (Haskell "fst" and "snd")

lemma prod_case_unfold [nitpick_unfold]: "prod_case = (%c p. c (fst p) (snd p))"
  by (simp add: fun_eq_iff split: prod.split)

lemma fst_eqD: "fst (x, y) = a ==> x = a"
  by simp

lemma snd_eqD: "snd (x, y) = a ==> y = a"
  by simp

lemma pair_collapse [simp]: "(fst p, snd p) = p"
  by (cases p) simp

lemmas surjective_pairing = pair_collapse [symmetric]

lemma prod_eq_iff: "s = t \<longleftrightarrow> fst s = fst t \<and> snd s = snd t"
  by (cases s, cases t) simp

lemma prod_eqI [intro?]: "fst p = fst q \<Longrightarrow> snd p = snd q \<Longrightarrow> p = q"
  by (simp add: prod_eq_iff)

lemma split_conv [simp, code]: "split f (a, b) = f a b"
  by (fact prod.cases)

lemma splitI: "f a b \<Longrightarrow> split f (a, b)"
  by (rule split_conv [THEN iffD2])

lemma splitD: "split f (a, b) \<Longrightarrow> f a b"
  by (rule split_conv [THEN iffD1])

lemma split_Pair [simp]: "(\<lambda>(x, y). (x, y)) = id"
  by (simp add: fun_eq_iff split: prod.split)

lemma split_eta: "(\<lambda>(x, y). f (x, y)) = f"
  -- {* Subsumes the old @{text split_Pair} when @{term f} is the identity function. *}
  by (simp add: fun_eq_iff split: prod.split)

lemma split_comp: "split (f \<circ> g) x = f (g (fst x)) (snd x)"
  by (cases x) simp

lemma split_twice: "split f (split g p) = split (\<lambda>x y. split f (g x y)) p"
  by (cases p) simp

lemma The_split: "The (split P) = (THE xy. P (fst xy) (snd xy))"
  by (simp add: prod_case_unfold)

lemma split_weak_cong: "p = q \<Longrightarrow> split c p = split c q"
  -- {* Prevents simplification of @{term c}: much faster *}
  by (fact prod.weak_case_cong)

lemma cond_split_eta: "(!!x y. f x y = g (x, y)) ==> (%(x, y). f x y) = g"
  by (simp add: split_eta)

lemma split_paired_all: "(!!x. PROP P x) == (!!a b. PROP P (a, b))"
proof
  fix a b
  assume "!!x. PROP P x"
  then show "PROP P (a, b)" .
next
  fix x
  assume "!!a b. PROP P (a, b)"
  from `PROP P (fst x, snd x)` show "PROP P x" by simp
qed

text {*
  The rule @{thm [source] split_paired_all} does not work with the
  Simplifier because it also affects premises in congrence rules,
  where this can lead to premises of the form @{text "!!a b. ... =
  ?P(a, b)"} which cannot be solved by reflexivity.
*}

lemmas split_tupled_all = split_paired_all unit_all_eq2

ML {*
  (* replace parameters of product type by individual component parameters *)
  val safe_full_simp_tac = generic_simp_tac true (true, false, false);
  local (* filtering with exists_paired_all is an essential optimization *)
    fun exists_paired_all (Const ("all", _) $ Abs (_, T, t)) =
          can HOLogic.dest_prodT T orelse exists_paired_all t
      | exists_paired_all (t $ u) = exists_paired_all t orelse exists_paired_all u
      | exists_paired_all (Abs (_, _, t)) = exists_paired_all t
      | exists_paired_all _ = false;
    val ss = HOL_basic_ss
      addsimps [@{thm split_paired_all}, @{thm unit_all_eq2}, @{thm unit_abs_eta_conv}]
      addsimprocs [@{simproc unit_eq}];
  in
    val split_all_tac = SUBGOAL (fn (t, i) =>
      if exists_paired_all t then safe_full_simp_tac ss i else no_tac);
    val unsafe_split_all_tac = SUBGOAL (fn (t, i) =>
      if exists_paired_all t then full_simp_tac ss i else no_tac);
    fun split_all th =
   if exists_paired_all (Thm.prop_of th) then full_simplify ss th else th;
  end;
*}

declaration {* fn _ =>
  Classical.map_cs (fn cs => cs addSbefore ("split_all_tac", split_all_tac))
*}

lemma split_paired_All [simp]: "(ALL x. P x) = (ALL a b. P (a, b))"
  -- {* @{text "[iff]"} is not a good idea because it makes @{text blast} loop *}
  by fast

lemma split_paired_Ex [simp]: "(EX x. P x) = (EX a b. P (a, b))"
  by fast

lemma split_paired_The: "(THE x. P x) = (THE (a, b). P (a, b))"
  -- {* Can't be added to simpset: loops! *}
  by (simp add: split_eta)

text {*
  Simplification procedure for @{thm [source] cond_split_eta}.  Using
  @{thm [source] split_eta} as a rewrite rule is not general enough,
  and using @{thm [source] cond_split_eta} directly would render some
  existing proofs very inefficient; similarly for @{text
  split_beta}.
*}

ML {*
local
  val cond_split_eta_ss = HOL_basic_ss addsimps @{thms cond_split_eta};
  fun Pair_pat k 0 (Bound m) = (m = k)
    | Pair_pat k i (Const (@{const_name Pair},  _) $ Bound m $ t) =
        i > 0 andalso m = k + i andalso Pair_pat k (i - 1) t
    | Pair_pat _ _ _ = false;
  fun no_args k i (Abs (_, _, t)) = no_args (k + 1) i t
    | no_args k i (t $ u) = no_args k i t andalso no_args k i u
    | no_args k i (Bound m) = m < k orelse m > k + i
    | no_args _ _ _ = true;
  fun split_pat tp i (Abs  (_, _, t)) = if tp 0 i t then SOME (i, t) else NONE
    | split_pat tp i (Const (@{const_name prod_case}, _) $ Abs (_, _, t)) = split_pat tp (i + 1) t
    | split_pat tp i _ = NONE;
  fun metaeq ss lhs rhs = mk_meta_eq (Goal.prove (Simplifier.the_context ss) [] []
        (HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs)))
        (K (simp_tac (Simplifier.inherit_context ss cond_split_eta_ss) 1)));

  fun beta_term_pat k i (Abs (_, _, t)) = beta_term_pat (k + 1) i t
    | beta_term_pat k i (t $ u) =
        Pair_pat k i (t $ u) orelse (beta_term_pat k i t andalso beta_term_pat k i u)
    | beta_term_pat k i t = no_args k i t;
  fun eta_term_pat k i (f $ arg) = no_args k i f andalso Pair_pat k i arg
    | eta_term_pat _ _ _ = false;
  fun subst arg k i (Abs (x, T, t)) = Abs (x, T, subst arg (k+1) i t)
    | subst arg k i (t $ u) =
        if Pair_pat k i (t $ u) then incr_boundvars k arg
        else (subst arg k i t $ subst arg k i u)
    | subst arg k i t = t;
in
  fun beta_proc ss (s as Const (@{const_name prod_case}, _) $ Abs (_, _, t) $ arg) =
        (case split_pat beta_term_pat 1 t of
          SOME (i, f) => SOME (metaeq ss s (subst arg 0 i f))
        | NONE => NONE)
    | beta_proc _ _ = NONE;
  fun eta_proc ss (s as Const (@{const_name prod_case}, _) $ Abs (_, _, t)) =
        (case split_pat eta_term_pat 1 t of
          SOME (_, ft) => SOME (metaeq ss s (let val (f $ arg) = ft in f end))
        | NONE => NONE)
    | eta_proc _ _ = NONE;
end;
*}
simproc_setup split_beta ("split f z") = {* fn _ => fn ss => fn ct => beta_proc ss (term_of ct) *}
simproc_setup split_eta ("split f") = {* fn _ => fn ss => fn ct => eta_proc ss (term_of ct) *}

lemma split_beta [mono]: "(%(x, y). P x y) z = P (fst z) (snd z)"
  by (subst surjective_pairing, rule split_conv)

lemma split_split [no_atp]: "R(split c p) = (ALL x y. p = (x, y) --> R(c x y))"
  -- {* For use with @{text split} and the Simplifier. *}
  by (insert surj_pair [of p], clarify, simp)

text {*
  @{thm [source] split_split} could be declared as @{text "[split]"}
  done after the Splitter has been speeded up significantly;
  precompute the constants involved and don't do anything unless the
  current goal contains one of those constants.
*}

lemma split_split_asm [no_atp]: "R (split c p) = (~(EX x y. p = (x, y) & (~R (c x y))))"
by (subst split_split, simp)

text {*
  \medskip @{term split} used as a logical connective or set former.

  \medskip These rules are for use with @{text blast}; could instead
  call @{text simp} using @{thm [source] prod.split} as rewrite. *}

lemma splitI2: "!!p. [| !!a b. p = (a, b) ==> c a b |] ==> split c p"
  apply (simp only: split_tupled_all)
  apply (simp (no_asm_simp))
  done

lemma splitI2': "!!p. [| !!a b. (a, b) = p ==> c a b x |] ==> split c p x"
  apply (simp only: split_tupled_all)
  apply (simp (no_asm_simp))
  done

lemma splitE: "split c p ==> (!!x y. p = (x, y) ==> c x y ==> Q) ==> Q"
  by (induct p) auto

lemma splitE': "split c p z ==> (!!x y. p = (x, y) ==> c x y z ==> Q) ==> Q"
  by (induct p) auto

lemma splitE2:
  "[| Q (split P z);  !!x y. [|z = (x, y); Q (P x y)|] ==> R |] ==> R"
proof -
  assume q: "Q (split P z)"
  assume r: "!!x y. [|z = (x, y); Q (P x y)|] ==> R"
  show R
    apply (rule r surjective_pairing)+
    apply (rule split_beta [THEN subst], rule q)
    done
qed

lemma splitD': "split R (a,b) c ==> R a b c"
  by simp

lemma mem_splitI: "z: c a b ==> z: split c (a, b)"
  by simp

lemma mem_splitI2: "!!p. [| !!a b. p = (a, b) ==> z: c a b |] ==> z: split c p"
by (simp only: split_tupled_all, simp)

lemma mem_splitE:
  assumes major: "z \<in> split c p"
    and cases: "\<And>x y. p = (x, y) \<Longrightarrow> z \<in> c x y \<Longrightarrow> Q"
  shows Q
  by (rule major [unfolded prod_case_unfold] cases surjective_pairing)+

declare mem_splitI2 [intro!] mem_splitI [intro!] splitI2' [intro!] splitI2 [intro!] splitI [intro!]
declare mem_splitE [elim!] splitE' [elim!] splitE [elim!]

ML {*
local (* filtering with exists_p_split is an essential optimization *)
  fun exists_p_split (Const (@{const_name prod_case},_) $ _ $ (Const (@{const_name Pair},_)$_$_)) = true
    | exists_p_split (t $ u) = exists_p_split t orelse exists_p_split u
    | exists_p_split (Abs (_, _, t)) = exists_p_split t
    | exists_p_split _ = false;
  val ss = HOL_basic_ss addsimps @{thms split_conv};
in
val split_conv_tac = SUBGOAL (fn (t, i) =>
    if exists_p_split t then safe_full_simp_tac ss i else no_tac);
end;
*}

(* This prevents applications of splitE for already splitted arguments leading
   to quite time-consuming computations (in particular for nested tuples) *)
declaration {* fn _ =>
  Classical.map_cs (fn cs => cs addSbefore ("split_conv_tac", split_conv_tac))
*}

lemma split_eta_SetCompr [simp,no_atp]: "(%u. EX x y. u = (x, y) & P (x, y)) = P"
  by (rule ext) fast

lemma split_eta_SetCompr2 [simp,no_atp]: "(%u. EX x y. u = (x, y) & P x y) = split P"
  by (rule ext) fast

lemma split_part [simp]: "(%(a,b). P & Q a b) = (%ab. P & split Q ab)"
  -- {* Allows simplifications of nested splits in case of independent predicates. *}
  by (rule ext) blast

(* Do NOT make this a simp rule as it
   a) only helps in special situations
   b) can lead to nontermination in the presence of split_def
*)
lemma split_comp_eq: 
  fixes f :: "'a => 'b => 'c" and g :: "'d => 'a"
  shows "(%u. f (g (fst u)) (snd u)) = (split (%x. f (g x)))"
  by (rule ext) auto

lemma pair_imageI [intro]: "(a, b) : A ==> f a b : (%(a, b). f a b) ` A"
  apply (rule_tac x = "(a, b)" in image_eqI)
   apply auto
  done

lemma The_split_eq [simp]: "(THE (x',y'). x = x' & y = y') = (x, y)"
  by blast

(*
the following  would be slightly more general,
but cannot be used as rewrite rule:
### Cannot add premise as rewrite rule because it contains (type) unknowns:
### ?y = .x
Goal "[| P y; !!x. P x ==> x = y |] ==> (@(x',y). x = x' & P y) = (x,y)"
by (rtac some_equality 1)
by ( Simp_tac 1)
by (split_all_tac 1)
by (Asm_full_simp_tac 1)
qed "The_split_eq";
*)

text {*
  Setup of internal @{text split_rule}.
*}

lemmas prod_caseI = prod.cases [THEN iffD2]

lemma prod_caseI2: "!!p. [| !!a b. p = (a, b) ==> c a b |] ==> prod_case c p"
  by (fact splitI2)

lemma prod_caseI2': "!!p. [| !!a b. (a, b) = p ==> c a b x |] ==> prod_case c p x"
  by (fact splitI2')

lemma prod_caseE: "prod_case c p ==> (!!x y. p = (x, y) ==> c x y ==> Q) ==> Q"
  by (fact splitE)

lemma prod_caseE': "prod_case c p z ==> (!!x y. p = (x, y) ==> c x y z ==> Q) ==> Q"
  by (fact splitE')

declare prod_caseI [intro!]

lemma prod_case_beta:
  "prod_case f p = f (fst p) (snd p)"
  by (fact split_beta)

lemma prod_cases3 [cases type]:
  obtains (fields) a b c where "y = (a, b, c)"
  by (cases y, case_tac b) blast

lemma prod_induct3 [case_names fields, induct type]:
    "(!!a b c. P (a, b, c)) ==> P x"
  by (cases x) blast

lemma prod_cases4 [cases type]:
  obtains (fields) a b c d where "y = (a, b, c, d)"
  by (cases y, case_tac c) blast

lemma prod_induct4 [case_names fields, induct type]:
    "(!!a b c d. P (a, b, c, d)) ==> P x"
  by (cases x) blast

lemma prod_cases5 [cases type]:
  obtains (fields) a b c d e where "y = (a, b, c, d, e)"
  by (cases y, case_tac d) blast

lemma prod_induct5 [case_names fields, induct type]:
    "(!!a b c d e. P (a, b, c, d, e)) ==> P x"
  by (cases x) blast

lemma prod_cases6 [cases type]:
  obtains (fields) a b c d e f where "y = (a, b, c, d, e, f)"
  by (cases y, case_tac e) blast

lemma prod_induct6 [case_names fields, induct type]:
    "(!!a b c d e f. P (a, b, c, d, e, f)) ==> P x"
  by (cases x) blast

lemma prod_cases7 [cases type]:
  obtains (fields) a b c d e f g where "y = (a, b, c, d, e, f, g)"
  by (cases y, case_tac f) blast

lemma prod_induct7 [case_names fields, induct type]:
    "(!!a b c d e f g. P (a, b, c, d, e, f, g)) ==> P x"
  by (cases x) blast

lemma split_def:
  "split = (\<lambda>c p. c (fst p) (snd p))"
  by (fact prod_case_unfold)

definition internal_split :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'c" where
  "internal_split == split"

lemma internal_split_conv: "internal_split c (a, b) = c a b"
  by (simp only: internal_split_def split_conv)

use "Tools/split_rule.ML"
setup Split_Rule.setup

hide_const internal_split


subsubsection {* Derived operations *}

definition curry    :: "('a \<times> 'b \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c" where
  "curry = (\<lambda>c x y. c (x, y))"

lemma curry_conv [simp, code]: "curry f a b = f (a, b)"
  by (simp add: curry_def)

lemma curryI [intro!]: "f (a, b) \<Longrightarrow> curry f a b"
  by (simp add: curry_def)

lemma curryD [dest!]: "curry f a b \<Longrightarrow> f (a, b)"
  by (simp add: curry_def)

lemma curryE: "curry f a b \<Longrightarrow> (f (a, b) \<Longrightarrow> Q) \<Longrightarrow> Q"
  by (simp add: curry_def)

lemma curry_split [simp]: "curry (split f) = f"
  by (simp add: curry_def split_def)

lemma split_curry [simp]: "split (curry f) = f"
  by (simp add: curry_def split_def)

text {*
  The composition-uncurry combinator.
*}

notation fcomp (infixl "\<circ>>" 60)

definition scomp :: "('a \<Rightarrow> 'b \<times> 'c) \<Rightarrow> ('b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> 'a \<Rightarrow> 'd" (infixl "\<circ>\<rightarrow>" 60) where
  "f \<circ>\<rightarrow> g = (\<lambda>x. prod_case g (f x))"

lemma scomp_unfold: "scomp = (\<lambda>f g x. g (fst (f x)) (snd (f x)))"
  by (simp add: fun_eq_iff scomp_def prod_case_unfold)

lemma scomp_apply [simp]: "(f \<circ>\<rightarrow> g) x = prod_case g (f x)"
  by (simp add: scomp_unfold prod_case_unfold)

lemma Pair_scomp: "Pair x \<circ>\<rightarrow> f = f x"
  by (simp add: fun_eq_iff)

lemma scomp_Pair: "x \<circ>\<rightarrow> Pair = x"
  by (simp add: fun_eq_iff)

lemma scomp_scomp: "(f \<circ>\<rightarrow> g) \<circ>\<rightarrow> h = f \<circ>\<rightarrow> (\<lambda>x. g x \<circ>\<rightarrow> h)"
  by (simp add: fun_eq_iff scomp_unfold)

lemma scomp_fcomp: "(f \<circ>\<rightarrow> g) \<circ>> h = f \<circ>\<rightarrow> (\<lambda>x. g x \<circ>> h)"
  by (simp add: fun_eq_iff scomp_unfold fcomp_def)

lemma fcomp_scomp: "(f \<circ>> g) \<circ>\<rightarrow> h = f \<circ>> (g \<circ>\<rightarrow> h)"
  by (simp add: fun_eq_iff scomp_unfold)

code_const scomp
  (Eval infixl 3 "#->")

no_notation fcomp (infixl "\<circ>>" 60)
no_notation scomp (infixl "\<circ>\<rightarrow>" 60)

text {*
  @{term map_pair} --- action of the product functor upon
  functions.
*}

definition map_pair :: "('a \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'd) \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'c \<times> 'd" where
  "map_pair f g = (\<lambda>(x, y). (f x, g y))"

lemma map_pair_simp [simp, code]:
  "map_pair f g (a, b) = (f a, g b)"
  by (simp add: map_pair_def)

enriched_type map_pair: map_pair
  by (auto simp add: split_paired_all)

lemma fst_map_pair [simp]:
  "fst (map_pair f g x) = f (fst x)"
  by (cases x) simp_all

lemma snd_prod_fun [simp]:
  "snd (map_pair f g x) = g (snd x)"
  by (cases x) simp_all

lemma fst_comp_map_pair [simp]:
  "fst \<circ> map_pair f g = f \<circ> fst"
  by (rule ext) simp_all

lemma snd_comp_map_pair [simp]:
  "snd \<circ> map_pair f g = g \<circ> snd"
  by (rule ext) simp_all

lemma map_pair_compose:
  "map_pair (f1 o f2) (g1 o g2) = (map_pair f1 g1 o map_pair f2 g2)"
  by (rule ext) (simp add: map_pair.compositionality comp_def)

lemma map_pair_ident [simp]:
  "map_pair (%x. x) (%y. y) = (%z. z)"
  by (rule ext) (simp add: map_pair.identity)

lemma map_pair_imageI [intro]:
  "(a, b) \<in> R \<Longrightarrow> (f a, g b) \<in> map_pair f g ` R"
  by (rule image_eqI) simp_all

lemma prod_fun_imageE [elim!]:
  assumes major: "c \<in> map_pair f g ` R"
    and cases: "\<And>x y. c = (f x, g y) \<Longrightarrow> (x, y) \<in> R \<Longrightarrow> P"
  shows P
  apply (rule major [THEN imageE])
  apply (case_tac x)
  apply (rule cases)
  apply simp_all
  done

definition apfst :: "('a \<Rightarrow> 'c) \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'c \<times> 'b" where
  "apfst f = map_pair f id"

definition apsnd :: "('b \<Rightarrow> 'c) \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'a \<times> 'c" where
  "apsnd f = map_pair id f"

lemma apfst_conv [simp, code]:
  "apfst f (x, y) = (f x, y)" 
  by (simp add: apfst_def)

lemma apsnd_conv [simp, code]:
  "apsnd f (x, y) = (x, f y)" 
  by (simp add: apsnd_def)

lemma fst_apfst [simp]:
  "fst (apfst f x) = f (fst x)"
  by (cases x) simp

lemma fst_apsnd [simp]:
  "fst (apsnd f x) = fst x"
  by (cases x) simp

lemma snd_apfst [simp]:
  "snd (apfst f x) = snd x"
  by (cases x) simp

lemma snd_apsnd [simp]:
  "snd (apsnd f x) = f (snd x)"
  by (cases x) simp

lemma apfst_compose:
  "apfst f (apfst g x) = apfst (f \<circ> g) x"
  by (cases x) simp

lemma apsnd_compose:
  "apsnd f (apsnd g x) = apsnd (f \<circ> g) x"
  by (cases x) simp

lemma apfst_apsnd [simp]:
  "apfst f (apsnd g x) = (f (fst x), g (snd x))"
  by (cases x) simp

lemma apsnd_apfst [simp]:
  "apsnd f (apfst g x) = (g (fst x), f (snd x))"
  by (cases x) simp

lemma apfst_id [simp] :
  "apfst id = id"
  by (simp add: fun_eq_iff)

lemma apsnd_id [simp] :
  "apsnd id = id"
  by (simp add: fun_eq_iff)

lemma apfst_eq_conv [simp]:
  "apfst f x = apfst g x \<longleftrightarrow> f (fst x) = g (fst x)"
  by (cases x) simp

lemma apsnd_eq_conv [simp]:
  "apsnd f x = apsnd g x \<longleftrightarrow> f (snd x) = g (snd x)"
  by (cases x) simp

lemma apsnd_apfst_commute:
  "apsnd f (apfst g p) = apfst g (apsnd f p)"
  by simp

text {*
  Disjoint union of a family of sets -- Sigma.
*}

definition Sigma :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> ('a \<times> 'b) set" where
  Sigma_def: "Sigma A B == UN x:A. UN y:B x. {Pair x y}"

abbreviation
  Times :: "'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<times> 'b) set"
    (infixr "<*>" 80) where
  "A <*> B == Sigma A (%_. B)"

notation (xsymbols)
  Times  (infixr "\<times>" 80)

notation (HTML output)
  Times  (infixr "\<times>" 80)

hide_const (open) Times

syntax
  "_Sigma" :: "[pttrn, 'a set, 'b set] => ('a * 'b) set"  ("(3SIGMA _:_./ _)" [0, 0, 10] 10)
translations
  "SIGMA x:A. B" == "CONST Sigma A (%x. B)"

lemma SigmaI [intro!]: "[| a:A;  b:B(a) |] ==> (a,b) : Sigma A B"
  by (unfold Sigma_def) blast

lemma SigmaE [elim!]:
    "[| c: Sigma A B;
        !!x y.[| x:A;  y:B(x);  c=(x,y) |] ==> P
     |] ==> P"
  -- {* The general elimination rule. *}
  by (unfold Sigma_def) blast

text {*
  Elimination of @{term "(a, b) : A \<times> B"} -- introduces no
  eigenvariables.
*}

lemma SigmaD1: "(a, b) : Sigma A B ==> a : A"
  by blast

lemma SigmaD2: "(a, b) : Sigma A B ==> b : B a"
  by blast

lemma SigmaE2:
    "[| (a, b) : Sigma A B;
        [| a:A;  b:B(a) |] ==> P
     |] ==> P"
  by blast

lemma Sigma_cong:
     "\<lbrakk>A = B; !!x. x \<in> B \<Longrightarrow> C x = D x\<rbrakk>
      \<Longrightarrow> (SIGMA x: A. C x) = (SIGMA x: B. D x)"
  by auto

lemma Sigma_mono: "[| A <= C; !!x. x:A ==> B x <= D x |] ==> Sigma A B <= Sigma C D"
  by blast

lemma Sigma_empty1 [simp]: "Sigma {} B = {}"
  by blast

lemma Sigma_empty2 [simp]: "A <*> {} = {}"
  by blast

lemma UNIV_Times_UNIV [simp]: "UNIV <*> UNIV = UNIV"
  by auto

lemma Compl_Times_UNIV1 [simp]: "- (UNIV <*> A) = UNIV <*> (-A)"
  by auto

lemma Compl_Times_UNIV2 [simp]: "- (A <*> UNIV) = (-A) <*> UNIV"
  by auto

lemma mem_Sigma_iff [iff]: "((a,b): Sigma A B) = (a:A & b:B(a))"
  by blast

lemma Times_subset_cancel2: "x:C ==> (A <*> C <= B <*> C) = (A <= B)"
  by blast

lemma Times_eq_cancel2: "x:C ==> (A <*> C = B <*> C) = (A = B)"
  by (blast elim: equalityE)

lemma SetCompr_Sigma_eq:
    "Collect (split (%x y. P x & Q x y)) = (SIGMA x:Collect P. Collect (Q x))"
  by blast

lemma Collect_split [simp]: "{(a,b). P a & Q b} = Collect P <*> Collect Q"
  by blast

lemma UN_Times_distrib:
  "(UN (a,b):(A <*> B). E a <*> F b) = (UNION A E) <*> (UNION B F)"
  -- {* Suggested by Pierre Chartier *}
  by blast

lemma split_paired_Ball_Sigma [simp,no_atp]:
    "(ALL z: Sigma A B. P z) = (ALL x:A. ALL y: B x. P(x,y))"
  by blast

lemma split_paired_Bex_Sigma [simp,no_atp]:
    "(EX z: Sigma A B. P z) = (EX x:A. EX y: B x. P(x,y))"
  by blast

lemma Sigma_Un_distrib1: "(SIGMA i:I Un J. C(i)) = (SIGMA i:I. C(i)) Un (SIGMA j:J. C(j))"
  by blast

lemma Sigma_Un_distrib2: "(SIGMA i:I. A(i) Un B(i)) = (SIGMA i:I. A(i)) Un (SIGMA i:I. B(i))"
  by blast

lemma Sigma_Int_distrib1: "(SIGMA i:I Int J. C(i)) = (SIGMA i:I. C(i)) Int (SIGMA j:J. C(j))"
  by blast

lemma Sigma_Int_distrib2: "(SIGMA i:I. A(i) Int B(i)) = (SIGMA i:I. A(i)) Int (SIGMA i:I. B(i))"
  by blast

lemma Sigma_Diff_distrib1: "(SIGMA i:I - J. C(i)) = (SIGMA i:I. C(i)) - (SIGMA j:J. C(j))"
  by blast

lemma Sigma_Diff_distrib2: "(SIGMA i:I. A(i) - B(i)) = (SIGMA i:I. A(i)) - (SIGMA i:I. B(i))"
  by blast

lemma Sigma_Union: "Sigma (Union X) B = (UN A:X. Sigma A B)"
  by blast

text {*
  Non-dependent versions are needed to avoid the need for higher-order
  matching, especially when the rules are re-oriented.
*}

lemma Times_Un_distrib1: "(A Un B) <*> C = (A <*> C) Un (B <*> C)"
by blast

lemma Times_Int_distrib1: "(A Int B) <*> C = (A <*> C) Int (B <*> C)"
by blast

lemma Times_Diff_distrib1: "(A - B) <*> C = (A <*> C) - (B <*> C)"
by blast

lemma Times_empty[simp]: "A \<times> B = {} \<longleftrightarrow> A = {} \<or> B = {}"
  by auto

lemma fst_image_times[simp]: "fst ` (A \<times> B) = (if B = {} then {} else A)"
  by force

lemma snd_image_times[simp]: "snd ` (A \<times> B) = (if A = {} then {} else B)"
  by force

lemma insert_times_insert[simp]:
  "insert a A \<times> insert b B =
   insert (a,b) (A \<times> insert b B \<union> insert a A \<times> B)"
by blast

lemma vimage_Times: "f -` (A \<times> B) = ((fst \<circ> f) -` A) \<inter> ((snd \<circ> f) -` B)"
  by (auto, case_tac "f x", auto)

lemma swap_inj_on:
  "inj_on (\<lambda>(i, j). (j, i)) A"
  by (auto intro!: inj_onI)

lemma swap_product:
  "(%(i, j). (j, i)) ` (A \<times> B) = B \<times> A"
  by (simp add: split_def image_def) blast

lemma image_split_eq_Sigma:
  "(\<lambda>x. (f x, g x)) ` A = Sigma (f ` A) (\<lambda>x. g ` (f -` {x} \<inter> A))"
proof (safe intro!: imageI)
  fix a b assume *: "a \<in> A" "b \<in> A" and eq: "f a = f b"
  show "(f b, g a) \<in> (\<lambda>x. (f x, g x)) ` A"
    using * eq[symmetric] by auto
qed simp_all

definition product :: "'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<times> 'b) set" where
  [code_abbrev]: "product A B = A \<times> B"

hide_const (open) product

lemma member_product:
  "x \<in> Product_Type.product A B \<longleftrightarrow> x \<in> A \<times> B"
  by (simp add: product_def)

text {* The following @{const map_pair} lemmas are due to Joachim Breitner: *}

lemma map_pair_inj_on:
  assumes "inj_on f A" and "inj_on g B"
  shows "inj_on (map_pair f g) (A \<times> B)"
proof (rule inj_onI)
  fix x :: "'a \<times> 'c" and y :: "'a \<times> 'c"
  assume "x \<in> A \<times> B" hence "fst x \<in> A" and "snd x \<in> B" by auto
  assume "y \<in> A \<times> B" hence "fst y \<in> A" and "snd y \<in> B" by auto
  assume "map_pair f g x = map_pair f g y"
  hence "fst (map_pair f g x) = fst (map_pair f g y)" by (auto)
  hence "f (fst x) = f (fst y)" by (cases x,cases y,auto)
  with `inj_on f A` and `fst x \<in> A` and `fst y \<in> A`
  have "fst x = fst y" by (auto dest:dest:inj_onD)
  moreover from `map_pair f g x = map_pair f g y`
  have "snd (map_pair f g x) = snd (map_pair f g y)" by (auto)
  hence "g (snd x) = g (snd y)" by (cases x,cases y,auto)
  with `inj_on g B` and `snd x \<in> B` and `snd y \<in> B`
  have "snd x = snd y" by (auto dest:dest:inj_onD)
  ultimately show "x = y" by(rule prod_eqI)
qed

lemma map_pair_surj:
  fixes f :: "'a \<Rightarrow> 'b" and g :: "'c \<Rightarrow> 'd"
  assumes "surj f" and "surj g"
  shows "surj (map_pair f g)"
unfolding surj_def
proof
  fix y :: "'b \<times> 'd"
  from `surj f` obtain a where "fst y = f a" by (auto elim:surjE)
  moreover
  from `surj g` obtain b where "snd y = g b" by (auto elim:surjE)
  ultimately have "(fst y, snd y) = map_pair f g (a,b)" by auto
  thus "\<exists>x. y = map_pair f g x" by auto
qed

lemma map_pair_surj_on:
  assumes "f ` A = A'" and "g ` B = B'"
  shows "map_pair f g ` (A \<times> B) = A' \<times> B'"
unfolding image_def
proof(rule set_eqI,rule iffI)
  fix x :: "'a \<times> 'c"
  assume "x \<in> {y\<Colon>'a \<times> 'c. \<exists>x\<Colon>'b \<times> 'd\<in>A \<times> B. y = map_pair f g x}"
  then obtain y where "y \<in> A \<times> B" and "x = map_pair f g y" by blast
  from `image f A = A'` and `y \<in> A \<times> B` have "f (fst y) \<in> A'" by auto
  moreover from `image g B = B'` and `y \<in> A \<times> B` have "g (snd y) \<in> B'" by auto
  ultimately have "(f (fst y), g (snd y)) \<in> (A' \<times> B')" by auto
  with `x = map_pair f g y` show "x \<in> A' \<times> B'" by (cases y, auto)
next
  fix x :: "'a \<times> 'c"
  assume "x \<in> A' \<times> B'" hence "fst x \<in> A'" and "snd x \<in> B'" by auto
  from `image f A = A'` and `fst x \<in> A'` have "fst x \<in> image f A" by auto
  then obtain a where "a \<in> A" and "fst x = f a" by (rule imageE)
  moreover from `image g B = B'` and `snd x \<in> B'`
  obtain b where "b \<in> B" and "snd x = g b" by auto
  ultimately have "(fst x, snd x) = map_pair f g (a,b)" by auto
  moreover from `a \<in> A` and  `b \<in> B` have "(a , b) \<in> A \<times> B" by auto
  ultimately have "\<exists>y \<in> A \<times> B. x = map_pair f g y" by auto
  thus "x \<in> {x. \<exists>y \<in> A \<times> B. x = map_pair f g y}" by auto
qed


subsection {* Inductively defined sets *}

use "Tools/inductive_set.ML"
setup Inductive_Set.setup


subsection {* Legacy theorem bindings and duplicates *}

lemma PairE:
  obtains x y where "p = (x, y)"
  by (fact prod.exhaust)

lemma Pair_inject:
  assumes "(a, b) = (a', b')"
    and "a = a' ==> b = b' ==> R"
  shows R
  using assms by simp

lemmas Pair_eq = prod.inject

lemmas split = split_conv  -- {* for backwards compatibility *}

lemmas Pair_fst_snd_eq = prod_eq_iff

hide_const (open) prod

end
