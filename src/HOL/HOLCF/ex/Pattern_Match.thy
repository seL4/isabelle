(*  Title:      HOL/HOLCF/ex/Pattern_Match.thy
    Author:     Brian Huffman
*)

header {* An experimental pattern-matching notation *}

theory Pattern_Match
imports HOLCF
begin

default_sort pcpo

text {* FIXME: Find a proper way to un-hide constants. *}

abbreviation fail :: "'a match"
where "fail \<equiv> Fixrec.fail"

abbreviation succeed :: "'a \<rightarrow> 'a match"
where "succeed \<equiv> Fixrec.succeed"

abbreviation run :: "'a match \<rightarrow> 'a"
where "run \<equiv> Fixrec.run"

subsection {* Fatbar combinator *}

definition
  fatbar :: "('a \<rightarrow> 'b match) \<rightarrow> ('a \<rightarrow> 'b match) \<rightarrow> ('a \<rightarrow> 'b match)" where
  "fatbar = (\<Lambda> a b x. a\<cdot>x +++ b\<cdot>x)"

abbreviation
  fatbar_syn :: "['a \<rightarrow> 'b match, 'a \<rightarrow> 'b match] \<Rightarrow> 'a \<rightarrow> 'b match" (infixr "\<parallel>" 60)  where
  "m1 \<parallel> m2 == fatbar\<cdot>m1\<cdot>m2"

lemma fatbar1: "m\<cdot>x = \<bottom> \<Longrightarrow> (m \<parallel> ms)\<cdot>x = \<bottom>"
by (simp add: fatbar_def)

lemma fatbar2: "m\<cdot>x = fail \<Longrightarrow> (m \<parallel> ms)\<cdot>x = ms\<cdot>x"
by (simp add: fatbar_def)

lemma fatbar3: "m\<cdot>x = succeed\<cdot>y \<Longrightarrow> (m \<parallel> ms)\<cdot>x = succeed\<cdot>y"
by (simp add: fatbar_def)

lemmas fatbar_simps = fatbar1 fatbar2 fatbar3

lemma run_fatbar1: "m\<cdot>x = \<bottom> \<Longrightarrow> run\<cdot>((m \<parallel> ms)\<cdot>x) = \<bottom>"
by (simp add: fatbar_def)

lemma run_fatbar2: "m\<cdot>x = fail \<Longrightarrow> run\<cdot>((m \<parallel> ms)\<cdot>x) = run\<cdot>(ms\<cdot>x)"
by (simp add: fatbar_def)

lemma run_fatbar3: "m\<cdot>x = succeed\<cdot>y \<Longrightarrow> run\<cdot>((m \<parallel> ms)\<cdot>x) = y"
by (simp add: fatbar_def)

lemmas run_fatbar_simps [simp] = run_fatbar1 run_fatbar2 run_fatbar3

subsection {* Bind operator for match monad *}

definition match_bind :: "'a match \<rightarrow> ('a \<rightarrow> 'b match) \<rightarrow> 'b match" where
  "match_bind = (\<Lambda> m k. sscase\<cdot>(\<Lambda> _. fail)\<cdot>(fup\<cdot>k)\<cdot>(Rep_match m))"

lemma match_bind_simps [simp]:
  "match_bind\<cdot>\<bottom>\<cdot>k = \<bottom>"
  "match_bind\<cdot>fail\<cdot>k = fail"
  "match_bind\<cdot>(succeed\<cdot>x)\<cdot>k = k\<cdot>x"
unfolding match_bind_def fail_def succeed_def
by (simp_all add: cont_Rep_match cont_Abs_match
  Rep_match_strict Abs_match_inverse)

subsection {* Case branch combinator *}

definition
  branch :: "('a \<rightarrow> 'b match) \<Rightarrow> ('b \<rightarrow> 'c) \<rightarrow> ('a \<rightarrow> 'c match)" where
  "branch p \<equiv> \<Lambda> r x. match_bind\<cdot>(p\<cdot>x)\<cdot>(\<Lambda> y. succeed\<cdot>(r\<cdot>y))"

lemma branch_simps:
  "p\<cdot>x = \<bottom> \<Longrightarrow> branch p\<cdot>r\<cdot>x = \<bottom>"
  "p\<cdot>x = fail \<Longrightarrow> branch p\<cdot>r\<cdot>x = fail"
  "p\<cdot>x = succeed\<cdot>y \<Longrightarrow> branch p\<cdot>r\<cdot>x = succeed\<cdot>(r\<cdot>y)"
by (simp_all add: branch_def)

lemma branch_succeed [simp]: "branch succeed\<cdot>r\<cdot>x = succeed\<cdot>(r\<cdot>x)"
by (simp add: branch_def)

subsection {* Cases operator *}

definition
  cases :: "'a match \<rightarrow> 'a::pcpo" where
  "cases = Fixrec.run"

text {* rewrite rules for cases *}

lemma cases_strict [simp]: "cases\<cdot>\<bottom> = \<bottom>"
by (simp add: cases_def)

lemma cases_fail [simp]: "cases\<cdot>fail = \<bottom>"
by (simp add: cases_def)

lemma cases_succeed [simp]: "cases\<cdot>(succeed\<cdot>x) = x"
by (simp add: cases_def)

subsection {* Case syntax *}

nonterminal Case_pat and Case_syn and Cases_syn

syntax
  "_Case_syntax":: "['a, Cases_syn] => 'b"               ("(Case _ of/ _)" 10)
  "_Case1"      :: "[Case_pat, 'b] => Case_syn"          ("(2_ =>/ _)" 10)
  ""            :: "Case_syn => Cases_syn"               ("_")
  "_Case2"      :: "[Case_syn, Cases_syn] => Cases_syn"  ("_/ | _")
  "_strip_positions" :: "'a => Case_pat"                 ("_")

syntax (xsymbols)
  "_Case1"      :: "[Case_pat, 'b] => Case_syn"          ("(2_ \<Rightarrow>/ _)" 10)

translations
  "_Case_syntax x ms" == "CONST cases\<cdot>(ms\<cdot>x)"
  "_Case2 m ms" == "m \<parallel> ms"

text {* Parsing Case expressions *}

syntax
  "_pat" :: "'a"
  "_variable" :: "'a"
  "_noargs" :: "'a"

translations
  "_Case1 p r" => "CONST branch (_pat p)\<cdot>(_variable p r)"
  "_variable (_args x y) r" => "CONST csplit\<cdot>(_variable x (_variable y r))"
  "_variable _noargs r" => "CONST unit_when\<cdot>r"

parse_translation {*
(* rewrite (_pat x) => (succeed) *)
(* rewrite (_variable x t) => (Abs_cfun (%x. t)) *)
 [(@{syntax_const "_pat"}, fn _ => Syntax.const @{const_syntax Fixrec.succeed}),
  Syntax_Trans.mk_binder_tr (@{syntax_const "_variable"}, @{const_syntax Abs_cfun})];
*}

text {* Printing Case expressions *}

syntax
  "_match" :: "'a"

print_translation {*
  let
    fun dest_LAM (Const (@{const_syntax Rep_cfun},_) $ Const (@{const_syntax unit_when},_) $ t) =
          (Syntax.const @{syntax_const "_noargs"}, t)
    |   dest_LAM (Const (@{const_syntax Rep_cfun},_) $ Const (@{const_syntax csplit},_) $ t) =
          let
            val (v1, t1) = dest_LAM t;
            val (v2, t2) = dest_LAM t1;
          in (Syntax.const @{syntax_const "_args"} $ v1 $ v2, t2) end
    |   dest_LAM (Const (@{const_syntax Abs_cfun},_) $ t) =
          let
            val abs =
              case t of Abs abs => abs
                | _ => ("x", dummyT, incr_boundvars 1 t $ Bound 0);
            val (x, t') = Syntax_Trans.atomic_abs_tr' abs;
          in (Syntax.const @{syntax_const "_variable"} $ x, t') end
    |   dest_LAM _ = raise Match; (* too few vars: abort translation *)

    fun Case1_tr' [Const(@{const_syntax branch},_) $ p, r] =
          let val (v, t) = dest_LAM r in
            Syntax.const @{syntax_const "_Case1"} $
              (Syntax.const @{syntax_const "_match"} $ p $ v) $ t
          end;

  in [(@{const_syntax Rep_cfun}, Case1_tr')] end;
*}

translations
  "x" <= "_match (CONST succeed) (_variable x)"


subsection {* Pattern combinators for data constructors *}

type_synonym ('a, 'b) pat = "'a \<rightarrow> 'b match"

definition
  cpair_pat :: "('a, 'c) pat \<Rightarrow> ('b, 'd) pat \<Rightarrow> ('a \<times> 'b, 'c \<times> 'd) pat" where
  "cpair_pat p1 p2 = (\<Lambda>(x, y).
    match_bind\<cdot>(p1\<cdot>x)\<cdot>(\<Lambda> a. match_bind\<cdot>(p2\<cdot>y)\<cdot>(\<Lambda> b. succeed\<cdot>(a, b))))"

definition
  spair_pat ::
  "('a, 'c) pat \<Rightarrow> ('b, 'd) pat \<Rightarrow> ('a::pcpo \<otimes> 'b::pcpo, 'c \<times> 'd) pat" where
  "spair_pat p1 p2 = (\<Lambda>(:x, y:). cpair_pat p1 p2\<cdot>(x, y))"

definition
  sinl_pat :: "('a, 'c) pat \<Rightarrow> ('a::pcpo \<oplus> 'b::pcpo, 'c) pat" where
  "sinl_pat p = sscase\<cdot>p\<cdot>(\<Lambda> x. fail)"

definition
  sinr_pat :: "('b, 'c) pat \<Rightarrow> ('a::pcpo \<oplus> 'b::pcpo, 'c) pat" where
  "sinr_pat p = sscase\<cdot>(\<Lambda> x. fail)\<cdot>p"

definition
  up_pat :: "('a, 'b) pat \<Rightarrow> ('a u, 'b) pat" where
  "up_pat p = fup\<cdot>p"

definition
  TT_pat :: "(tr, unit) pat" where
  "TT_pat = (\<Lambda> b. If b then succeed\<cdot>() else fail)"

definition
  FF_pat :: "(tr, unit) pat" where
  "FF_pat = (\<Lambda> b. If b then fail else succeed\<cdot>())"

definition
  ONE_pat :: "(one, unit) pat" where
  "ONE_pat = (\<Lambda> ONE. succeed\<cdot>())"

text {* Parse translations (patterns) *}
translations
  "_pat (XCONST Pair x y)" => "CONST cpair_pat (_pat x) (_pat y)"
  "_pat (XCONST spair\<cdot>x\<cdot>y)" => "CONST spair_pat (_pat x) (_pat y)"
  "_pat (XCONST sinl\<cdot>x)" => "CONST sinl_pat (_pat x)"
  "_pat (XCONST sinr\<cdot>x)" => "CONST sinr_pat (_pat x)"
  "_pat (XCONST up\<cdot>x)" => "CONST up_pat (_pat x)"
  "_pat (XCONST TT)" => "CONST TT_pat"
  "_pat (XCONST FF)" => "CONST FF_pat"
  "_pat (XCONST ONE)" => "CONST ONE_pat"

text {* CONST version is also needed for constructors with special syntax *}
translations
  "_pat (CONST Pair x y)" => "CONST cpair_pat (_pat x) (_pat y)"
  "_pat (CONST spair\<cdot>x\<cdot>y)" => "CONST spair_pat (_pat x) (_pat y)"

text {* Parse translations (variables) *}
translations
  "_variable (XCONST Pair x y) r" => "_variable (_args x y) r"
  "_variable (XCONST spair\<cdot>x\<cdot>y) r" => "_variable (_args x y) r"
  "_variable (XCONST sinl\<cdot>x) r" => "_variable x r"
  "_variable (XCONST sinr\<cdot>x) r" => "_variable x r"
  "_variable (XCONST up\<cdot>x) r" => "_variable x r"
  "_variable (XCONST TT) r" => "_variable _noargs r"
  "_variable (XCONST FF) r" => "_variable _noargs r"
  "_variable (XCONST ONE) r" => "_variable _noargs r"

translations
  "_variable (CONST Pair x y) r" => "_variable (_args x y) r"
  "_variable (CONST spair\<cdot>x\<cdot>y) r" => "_variable (_args x y) r"

text {* Print translations *}
translations
  "CONST Pair (_match p1 v1) (_match p2 v2)"
      <= "_match (CONST cpair_pat p1 p2) (_args v1 v2)"
  "CONST spair\<cdot>(_match p1 v1)\<cdot>(_match p2 v2)"
      <= "_match (CONST spair_pat p1 p2) (_args v1 v2)"
  "CONST sinl\<cdot>(_match p1 v1)" <= "_match (CONST sinl_pat p1) v1"
  "CONST sinr\<cdot>(_match p1 v1)" <= "_match (CONST sinr_pat p1) v1"
  "CONST up\<cdot>(_match p1 v1)" <= "_match (CONST up_pat p1) v1"
  "CONST TT" <= "_match (CONST TT_pat) _noargs"
  "CONST FF" <= "_match (CONST FF_pat) _noargs"
  "CONST ONE" <= "_match (CONST ONE_pat) _noargs"

lemma cpair_pat1:
  "branch p\<cdot>r\<cdot>x = \<bottom> \<Longrightarrow> branch (cpair_pat p q)\<cdot>(csplit\<cdot>r)\<cdot>(x, y) = \<bottom>"
apply (simp add: branch_def cpair_pat_def)
apply (cases "p\<cdot>x", simp_all)
done

lemma cpair_pat2:
  "branch p\<cdot>r\<cdot>x = fail \<Longrightarrow> branch (cpair_pat p q)\<cdot>(csplit\<cdot>r)\<cdot>(x, y) = fail"
apply (simp add: branch_def cpair_pat_def)
apply (cases "p\<cdot>x", simp_all)
done

lemma cpair_pat3:
  "branch p\<cdot>r\<cdot>x = succeed\<cdot>s \<Longrightarrow>
   branch (cpair_pat p q)\<cdot>(csplit\<cdot>r)\<cdot>(x, y) = branch q\<cdot>s\<cdot>y"
apply (simp add: branch_def cpair_pat_def)
apply (cases "p\<cdot>x", simp_all)
apply (cases "q\<cdot>y", simp_all)
done

lemmas cpair_pat [simp] =
  cpair_pat1 cpair_pat2 cpair_pat3

lemma spair_pat [simp]:
  "branch (spair_pat p1 p2)\<cdot>r\<cdot>\<bottom> = \<bottom>"
  "\<lbrakk>x \<noteq> \<bottom>; y \<noteq> \<bottom>\<rbrakk>
     \<Longrightarrow> branch (spair_pat p1 p2)\<cdot>r\<cdot>(:x, y:) =
         branch (cpair_pat p1 p2)\<cdot>r\<cdot>(x, y)"
by (simp_all add: branch_def spair_pat_def)

lemma sinl_pat [simp]:
  "branch (sinl_pat p)\<cdot>r\<cdot>\<bottom> = \<bottom>"
  "x \<noteq> \<bottom> \<Longrightarrow> branch (sinl_pat p)\<cdot>r\<cdot>(sinl\<cdot>x) = branch p\<cdot>r\<cdot>x"
  "y \<noteq> \<bottom> \<Longrightarrow> branch (sinl_pat p)\<cdot>r\<cdot>(sinr\<cdot>y) = fail"
by (simp_all add: branch_def sinl_pat_def)

lemma sinr_pat [simp]:
  "branch (sinr_pat p)\<cdot>r\<cdot>\<bottom> = \<bottom>"
  "x \<noteq> \<bottom> \<Longrightarrow> branch (sinr_pat p)\<cdot>r\<cdot>(sinl\<cdot>x) = fail"
  "y \<noteq> \<bottom> \<Longrightarrow> branch (sinr_pat p)\<cdot>r\<cdot>(sinr\<cdot>y) = branch p\<cdot>r\<cdot>y"
by (simp_all add: branch_def sinr_pat_def)

lemma up_pat [simp]:
  "branch (up_pat p)\<cdot>r\<cdot>\<bottom> = \<bottom>"
  "branch (up_pat p)\<cdot>r\<cdot>(up\<cdot>x) = branch p\<cdot>r\<cdot>x"
by (simp_all add: branch_def up_pat_def)

lemma TT_pat [simp]:
  "branch TT_pat\<cdot>(unit_when\<cdot>r)\<cdot>\<bottom> = \<bottom>"
  "branch TT_pat\<cdot>(unit_when\<cdot>r)\<cdot>TT = succeed\<cdot>r"
  "branch TT_pat\<cdot>(unit_when\<cdot>r)\<cdot>FF = fail"
by (simp_all add: branch_def TT_pat_def)

lemma FF_pat [simp]:
  "branch FF_pat\<cdot>(unit_when\<cdot>r)\<cdot>\<bottom> = \<bottom>"
  "branch FF_pat\<cdot>(unit_when\<cdot>r)\<cdot>TT = fail"
  "branch FF_pat\<cdot>(unit_when\<cdot>r)\<cdot>FF = succeed\<cdot>r"
by (simp_all add: branch_def FF_pat_def)

lemma ONE_pat [simp]:
  "branch ONE_pat\<cdot>(unit_when\<cdot>r)\<cdot>\<bottom> = \<bottom>"
  "branch ONE_pat\<cdot>(unit_when\<cdot>r)\<cdot>ONE = succeed\<cdot>r"
by (simp_all add: branch_def ONE_pat_def)


subsection {* Wildcards, as-patterns, and lazy patterns *}

definition
  wild_pat :: "'a \<rightarrow> unit match" where
  "wild_pat = (\<Lambda> x. succeed\<cdot>())"

definition
  as_pat :: "('a \<rightarrow> 'b match) \<Rightarrow> 'a \<rightarrow> ('a \<times> 'b) match" where
  "as_pat p = (\<Lambda> x. match_bind\<cdot>(p\<cdot>x)\<cdot>(\<Lambda> a. succeed\<cdot>(x, a)))"

definition
  lazy_pat :: "('a \<rightarrow> 'b::pcpo match) \<Rightarrow> ('a \<rightarrow> 'b match)" where
  "lazy_pat p = (\<Lambda> x. succeed\<cdot>(cases\<cdot>(p\<cdot>x)))"

text {* Parse translations (patterns) *}
translations
  "_pat _" => "CONST wild_pat"

text {* Parse translations (variables) *}
translations
  "_variable _ r" => "_variable _noargs r"

text {* Print translations *}
translations
  "_" <= "_match (CONST wild_pat) _noargs"

lemma wild_pat [simp]: "branch wild_pat\<cdot>(unit_when\<cdot>r)\<cdot>x = succeed\<cdot>r"
by (simp add: branch_def wild_pat_def)

lemma as_pat [simp]:
  "branch (as_pat p)\<cdot>(csplit\<cdot>r)\<cdot>x = branch p\<cdot>(r\<cdot>x)\<cdot>x"
apply (simp add: branch_def as_pat_def)
apply (cases "p\<cdot>x", simp_all)
done

lemma lazy_pat [simp]:
  "branch p\<cdot>r\<cdot>x = \<bottom> \<Longrightarrow> branch (lazy_pat p)\<cdot>r\<cdot>x = succeed\<cdot>(r\<cdot>\<bottom>)"
  "branch p\<cdot>r\<cdot>x = fail \<Longrightarrow> branch (lazy_pat p)\<cdot>r\<cdot>x = succeed\<cdot>(r\<cdot>\<bottom>)"
  "branch p\<cdot>r\<cdot>x = succeed\<cdot>s \<Longrightarrow> branch (lazy_pat p)\<cdot>r\<cdot>x = succeed\<cdot>s"
apply (simp_all add: branch_def lazy_pat_def)
apply (cases "p\<cdot>x", simp_all)+
done

subsection {* Examples *}

term "Case t of (:up\<cdot>(sinl\<cdot>x), sinr\<cdot>y:) \<Rightarrow> (x, y)"

term "\<Lambda> t. Case t of up\<cdot>(sinl\<cdot>a) \<Rightarrow> a | up\<cdot>(sinr\<cdot>b) \<Rightarrow> b"

term "\<Lambda> t. Case t of (:up\<cdot>(sinl\<cdot>_), sinr\<cdot>x:) \<Rightarrow> x"

subsection {* ML code for generating definitions *}

ML {*
local open HOLCF_Library in

infixr 6 ->>;
infix 9 ` ;

val beta_rules =
  @{thms beta_cfun cont_id cont_const cont2cont_APP cont2cont_LAM'} @
  @{thms cont2cont_fst cont2cont_snd cont2cont_Pair};

val beta_ss = HOL_basic_ss addsimps (@{thms simp_thms} @ beta_rules);

fun define_consts
    (specs : (binding * term * mixfix) list)
    (thy : theory)
    : (term list * thm list) * theory =
  let
    fun mk_decl (b, t, mx) = (b, fastype_of t, mx);
    val decls = map mk_decl specs;
    val thy = Cont_Consts.add_consts decls thy;
    fun mk_const (b, T, mx) = Const (Sign.full_name thy b, T);
    val consts = map mk_const decls;
    fun mk_def c (b, t, mx) =
      (Thm.def_binding b, Logic.mk_equals (c, t));
    val defs = map2 mk_def consts specs;
    val (def_thms, thy) =
      Global_Theory.add_defs false (map Thm.no_attributes defs) thy;
  in
    ((consts, def_thms), thy)
  end;

fun prove
    (thy : theory)
    (defs : thm list)
    (goal : term)
    (tacs : {prems: thm list, context: Proof.context} -> tactic list)
    : thm =
  let
    fun tac {prems, context} =
      rewrite_goals_tac defs THEN
      EVERY (tacs {prems = map (rewrite_rule defs) prems, context = context})
  in
    Goal.prove_global thy [] [] goal tac
  end;

fun get_vars_avoiding
    (taken : string list)
    (args : (bool * typ) list)
    : (term list * term list) =
  let
    val Ts = map snd args;
    val ns = Name.variant_list taken (Datatype_Prop.make_tnames Ts);
    val vs = map Free (ns ~~ Ts);
    val nonlazy = map snd (filter_out (fst o fst) (args ~~ vs));
  in
    (vs, nonlazy)
  end;

(******************************************************************************)
(************** definitions and theorems for pattern combinators **************)
(******************************************************************************)

fun add_pattern_combinators
    (bindings : binding list)
    (spec : (term * (bool * typ) list) list)
    (lhsT : typ)
    (exhaust : thm)
    (case_const : typ -> term)
    (case_rews : thm list)
    (thy : theory) =
  let

    (* utility functions *)
    fun mk_pair_pat (p1, p2) =
      let
        val T1 = fastype_of p1;
        val T2 = fastype_of p2;
        val (U1, V1) = apsnd dest_matchT (dest_cfunT T1);
        val (U2, V2) = apsnd dest_matchT (dest_cfunT T2);
        val pat_typ = [T1, T2] --->
            (mk_prodT (U1, U2) ->> mk_matchT (mk_prodT (V1, V2)));
        val pat_const = Const (@{const_name cpair_pat}, pat_typ);
      in
        pat_const $ p1 $ p2
      end;
    fun mk_tuple_pat [] = succeed_const HOLogic.unitT
      | mk_tuple_pat ps = foldr1 mk_pair_pat ps;
    fun branch_const (T,U,V) = 
      Const (@{const_name branch},
        (T ->> mk_matchT U) --> (U ->> V) ->> T ->> mk_matchT V);

    (* define pattern combinators *)
    local
      val tns = map (fst o dest_TFree) (snd (dest_Type lhsT));

      fun pat_eqn (i, (bind, (con, args))) : binding * term * mixfix =
        let
          val pat_bind = Binding.suffix_name "_pat" bind;
          val Ts = map snd args;
          val Vs =
              (map (K "'t") args)
              |> Datatype_Prop.indexify_names
              |> Name.variant_list tns
              |> map (fn t => TFree (t, @{sort pcpo}));
          val patNs = Datatype_Prop.indexify_names (map (K "pat") args);
          val patTs = map2 (fn T => fn V => T ->> mk_matchT V) Ts Vs;
          val pats = map Free (patNs ~~ patTs);
          val fail = mk_fail (mk_tupleT Vs);
          val (vs, nonlazy) = get_vars_avoiding patNs args;
          val rhs = big_lambdas vs (mk_tuple_pat pats ` mk_tuple vs);
          fun one_fun (j, (_, args')) =
            let
              val (vs', nonlazy) = get_vars_avoiding patNs args';
            in if i = j then rhs else big_lambdas vs' fail end;
          val funs = map_index one_fun spec;
          val body = list_ccomb (case_const (mk_matchT (mk_tupleT Vs)), funs);
        in
          (pat_bind, lambdas pats body, NoSyn)
        end;
    in
      val ((pat_consts, pat_defs), thy) =
          define_consts (map_index pat_eqn (bindings ~~ spec)) thy
    end;

    (* syntax translations for pattern combinators *)
    local
      fun syntax c = Lexicon.mark_const (fst (dest_Const c));
      fun app s (l, r) = Ast.mk_appl (Ast.Constant s) [l, r];
      val capp = app @{const_syntax Rep_cfun};
      val capps = Library.foldl capp

      fun app_var x = Ast.mk_appl (Ast.Constant "_variable") [x, Ast.Variable "rhs"];
      fun app_pat x = Ast.mk_appl (Ast.Constant "_pat") [x];
      fun args_list [] = Ast.Constant "_noargs"
        | args_list xs = foldr1 (app "_args") xs;
      fun one_case_trans (pat, (con, args)) =
        let
          val cname = Ast.Constant (syntax con);
          val pname = Ast.Constant (syntax pat);
          val ns = 1 upto length args;
          val xs = map (fn n => Ast.Variable ("x"^(string_of_int n))) ns;
          val ps = map (fn n => Ast.Variable ("p"^(string_of_int n))) ns;
          val vs = map (fn n => Ast.Variable ("v"^(string_of_int n))) ns;
        in
          [Syntax.Parse_Rule (app_pat (capps (cname, xs)),
            Ast.mk_appl pname (map app_pat xs)),
           Syntax.Parse_Rule (app_var (capps (cname, xs)),
            app_var (args_list xs)),
           Syntax.Print_Rule (capps (cname, ListPair.map (app "_match") (ps,vs)),
            app "_match" (Ast.mk_appl pname ps, args_list vs))]
        end;
      val trans_rules : Ast.ast Syntax.trrule list =
          maps one_case_trans (pat_consts ~~ spec);
    in
      val thy = Sign.add_trrules trans_rules thy;
    end;

    (* prove strictness and reduction rules of pattern combinators *)
    local
      val tns = map (fst o dest_TFree) (snd (dest_Type lhsT));
      val rn = singleton (Name.variant_list tns) "'r";
      val R = TFree (rn, @{sort pcpo});
      fun pat_lhs (pat, args) =
        let
          val Ts = map snd args;
          val Vs =
              (map (K "'t") args)
              |> Datatype_Prop.indexify_names
              |> Name.variant_list (rn::tns)
              |> map (fn t => TFree (t, @{sort pcpo}));
          val patNs = Datatype_Prop.indexify_names (map (K "pat") args);
          val patTs = map2 (fn T => fn V => T ->> mk_matchT V) Ts Vs;
          val pats = map Free (patNs ~~ patTs);
          val k = Free ("rhs", mk_tupleT Vs ->> R);
          val branch1 = branch_const (lhsT, mk_tupleT Vs, R);
          val fun1 = (branch1 $ list_comb (pat, pats)) ` k;
          val branch2 = branch_const (mk_tupleT Ts, mk_tupleT Vs, R);
          val fun2 = (branch2 $ mk_tuple_pat pats) ` k;
          val taken = "rhs" :: patNs;
        in (fun1, fun2, taken) end;
      fun pat_strict (pat, (con, args)) =
        let
          val (fun1, fun2, taken) = pat_lhs (pat, args);
          val defs = @{thm branch_def} :: pat_defs;
          val goal = mk_trp (mk_strict fun1);
          val rules = @{thms match_bind_simps} @ case_rews;
          val tacs = [simp_tac (beta_ss addsimps rules) 1];
        in prove thy defs goal (K tacs) end;
      fun pat_apps (i, (pat, (con, args))) =
        let
          val (fun1, fun2, taken) = pat_lhs (pat, args);
          fun pat_app (j, (con', args')) =
            let
              val (vs, nonlazy) = get_vars_avoiding taken args';
              val con_app = list_ccomb (con', vs);
              val assms = map (mk_trp o mk_defined) nonlazy;
              val rhs = if i = j then fun2 ` mk_tuple vs else mk_fail R;
              val concl = mk_trp (mk_eq (fun1 ` con_app, rhs));
              val goal = Logic.list_implies (assms, concl);
              val defs = @{thm branch_def} :: pat_defs;
              val rules = @{thms match_bind_simps} @ case_rews;
              val tacs = [asm_simp_tac (beta_ss addsimps rules) 1];
            in prove thy defs goal (K tacs) end;
        in map_index pat_app spec end;
    in
      val pat_stricts = map pat_strict (pat_consts ~~ spec);
      val pat_apps = flat (map_index pat_apps (pat_consts ~~ spec));
    end;

  in
    (pat_stricts @ pat_apps, thy)
  end

end
*}

(*
Cut from HOLCF/Tools/domain_constructors.ML
in function add_domain_constructors:

    ( * define and prove theorems for pattern combinators * )
    val (pat_thms : thm list, thy : theory) =
      let
        val bindings = map #1 spec;
        fun prep_arg (lazy, sel, T) = (lazy, T);
        fun prep_con c (b, args, mx) = (c, map prep_arg args);
        val pat_spec = map2 prep_con con_consts spec;
      in
        add_pattern_combinators bindings pat_spec lhsT
          exhaust case_const cases thy
      end

*)

end
