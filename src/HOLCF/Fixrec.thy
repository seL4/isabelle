(*  Title:      HOLCF/Fixrec.thy
    Author:     Amber Telfer and Brian Huffman
*)

header "Package for defining recursive functions in HOLCF"

theory Fixrec
imports Sprod Ssum Up One Tr Fix
uses ("Tools/fixrec.ML")
begin

subsection {* Maybe monad type *}

defaultsort cpo

pcpodef (open) 'a maybe = "UNIV::(one ++ 'a u) set"
by simp_all

definition
  fail :: "'a maybe" where
  "fail = Abs_maybe (sinl\<cdot>ONE)"

definition
  return :: "'a \<rightarrow> 'a maybe" where
  "return = (\<Lambda> x. Abs_maybe (sinr\<cdot>(up\<cdot>x)))"

definition
  maybe_when :: "'b \<rightarrow> ('a \<rightarrow> 'b) \<rightarrow> 'a maybe \<rightarrow> 'b::pcpo" where
  "maybe_when = (\<Lambda> f r m. sscase\<cdot>(\<Lambda> x. f)\<cdot>(fup\<cdot>r)\<cdot>(Rep_maybe m))"

lemma maybeE:
  "\<lbrakk>p = \<bottom> \<Longrightarrow> Q; p = fail \<Longrightarrow> Q; \<And>x. p = return\<cdot>x \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
apply (unfold fail_def return_def)
apply (cases p, rename_tac r)
apply (rule_tac p=r in ssumE, simp add: Abs_maybe_strict)
apply (rule_tac p=x in oneE, simp, simp)
apply (rule_tac p=y in upE, simp, simp add: cont_Abs_maybe)
done

lemma return_defined [simp]: "return\<cdot>x \<noteq> \<bottom>"
by (simp add: return_def cont_Abs_maybe Abs_maybe_defined)

lemma fail_defined [simp]: "fail \<noteq> \<bottom>"
by (simp add: fail_def Abs_maybe_defined)

lemma return_eq [simp]: "(return\<cdot>x = return\<cdot>y) = (x = y)"
by (simp add: return_def cont_Abs_maybe Abs_maybe_inject)

lemma return_neq_fail [simp]:
  "return\<cdot>x \<noteq> fail" "fail \<noteq> return\<cdot>x"
by (simp_all add: return_def fail_def cont_Abs_maybe Abs_maybe_inject)

lemma maybe_when_rews [simp]:
  "maybe_when\<cdot>f\<cdot>r\<cdot>\<bottom> = \<bottom>"
  "maybe_when\<cdot>f\<cdot>r\<cdot>fail = f"
  "maybe_when\<cdot>f\<cdot>r\<cdot>(return\<cdot>x) = r\<cdot>x"
by (simp_all add: return_def fail_def maybe_when_def cont_Rep_maybe
                  cont2cont_LAM
                  cont_Abs_maybe Abs_maybe_inverse Rep_maybe_strict)

translations
  "case m of XCONST fail \<Rightarrow> t1 | XCONST return\<cdot>x \<Rightarrow> t2"
    == "CONST maybe_when\<cdot>t1\<cdot>(\<Lambda> x. t2)\<cdot>m"


subsubsection {* Monadic bind operator *}

definition
  bind :: "'a maybe \<rightarrow> ('a \<rightarrow> 'b maybe) \<rightarrow> 'b maybe" where
  "bind = (\<Lambda> m f. case m of fail \<Rightarrow> fail | return\<cdot>x \<Rightarrow> f\<cdot>x)"

text {* monad laws *}

lemma bind_strict [simp]: "bind\<cdot>\<bottom>\<cdot>f = \<bottom>"
by (simp add: bind_def)

lemma bind_fail [simp]: "bind\<cdot>fail\<cdot>f = fail"
by (simp add: bind_def)

lemma left_unit [simp]: "bind\<cdot>(return\<cdot>a)\<cdot>k = k\<cdot>a"
by (simp add: bind_def)

lemma right_unit [simp]: "bind\<cdot>m\<cdot>return = m"
by (rule_tac p=m in maybeE, simp_all)

lemma bind_assoc:
 "bind\<cdot>(bind\<cdot>m\<cdot>k)\<cdot>h = bind\<cdot>m\<cdot>(\<Lambda> a. bind\<cdot>(k\<cdot>a)\<cdot>h)"
by (rule_tac p=m in maybeE, simp_all)

subsubsection {* Run operator *}

definition
  run :: "'a maybe \<rightarrow> 'a::pcpo" where
  "run = maybe_when\<cdot>\<bottom>\<cdot>ID"

text {* rewrite rules for run *}

lemma run_strict [simp]: "run\<cdot>\<bottom> = \<bottom>"
by (simp add: run_def)

lemma run_fail [simp]: "run\<cdot>fail = \<bottom>"
by (simp add: run_def)

lemma run_return [simp]: "run\<cdot>(return\<cdot>x) = x"
by (simp add: run_def)

subsubsection {* Monad plus operator *}

definition
  mplus :: "'a maybe \<rightarrow> 'a maybe \<rightarrow> 'a maybe" where
  "mplus = (\<Lambda> m1 m2. case m1 of fail \<Rightarrow> m2 | return\<cdot>x \<Rightarrow> m1)"

abbreviation
  mplus_syn :: "['a maybe, 'a maybe] \<Rightarrow> 'a maybe"  (infixr "+++" 65)  where
  "m1 +++ m2 == mplus\<cdot>m1\<cdot>m2"

text {* rewrite rules for mplus *}

lemma mplus_strict [simp]: "\<bottom> +++ m = \<bottom>"
by (simp add: mplus_def)

lemma mplus_fail [simp]: "fail +++ m = m"
by (simp add: mplus_def)

lemma mplus_return [simp]: "return\<cdot>x +++ m = return\<cdot>x"
by (simp add: mplus_def)

lemma mplus_fail2 [simp]: "m +++ fail = m"
by (rule_tac p=m in maybeE, simp_all)

lemma mplus_assoc: "(x +++ y) +++ z = x +++ (y +++ z)"
by (rule_tac p=x in maybeE, simp_all)

subsubsection {* Fatbar combinator *}

definition
  fatbar :: "('a \<rightarrow> 'b maybe) \<rightarrow> ('a \<rightarrow> 'b maybe) \<rightarrow> ('a \<rightarrow> 'b maybe)" where
  "fatbar = (\<Lambda> a b x. a\<cdot>x +++ b\<cdot>x)"

abbreviation
  fatbar_syn :: "['a \<rightarrow> 'b maybe, 'a \<rightarrow> 'b maybe] \<Rightarrow> 'a \<rightarrow> 'b maybe" (infixr "\<parallel>" 60)  where
  "m1 \<parallel> m2 == fatbar\<cdot>m1\<cdot>m2"

lemma fatbar1: "m\<cdot>x = \<bottom> \<Longrightarrow> (m \<parallel> ms)\<cdot>x = \<bottom>"
by (simp add: fatbar_def)

lemma fatbar2: "m\<cdot>x = fail \<Longrightarrow> (m \<parallel> ms)\<cdot>x = ms\<cdot>x"
by (simp add: fatbar_def)

lemma fatbar3: "m\<cdot>x = return\<cdot>y \<Longrightarrow> (m \<parallel> ms)\<cdot>x = return\<cdot>y"
by (simp add: fatbar_def)

lemmas fatbar_simps = fatbar1 fatbar2 fatbar3

lemma run_fatbar1: "m\<cdot>x = \<bottom> \<Longrightarrow> run\<cdot>((m \<parallel> ms)\<cdot>x) = \<bottom>"
by (simp add: fatbar_def)

lemma run_fatbar2: "m\<cdot>x = fail \<Longrightarrow> run\<cdot>((m \<parallel> ms)\<cdot>x) = run\<cdot>(ms\<cdot>x)"
by (simp add: fatbar_def)

lemma run_fatbar3: "m\<cdot>x = return\<cdot>y \<Longrightarrow> run\<cdot>((m \<parallel> ms)\<cdot>x) = y"
by (simp add: fatbar_def)

lemmas run_fatbar_simps [simp] = run_fatbar1 run_fatbar2 run_fatbar3

subsection {* Case branch combinator *}

definition
  branch :: "('a \<rightarrow> 'b maybe) \<Rightarrow> ('b \<rightarrow> 'c) \<rightarrow> ('a \<rightarrow> 'c maybe)" where
  "branch p \<equiv> \<Lambda> r x. bind\<cdot>(p\<cdot>x)\<cdot>(\<Lambda> y. return\<cdot>(r\<cdot>y))"

lemma branch_rews:
  "p\<cdot>x = \<bottom> \<Longrightarrow> branch p\<cdot>r\<cdot>x = \<bottom>"
  "p\<cdot>x = fail \<Longrightarrow> branch p\<cdot>r\<cdot>x = fail"
  "p\<cdot>x = return\<cdot>y \<Longrightarrow> branch p\<cdot>r\<cdot>x = return\<cdot>(r\<cdot>y)"
by (simp_all add: branch_def)

lemma branch_return [simp]: "branch return\<cdot>r\<cdot>x = return\<cdot>(r\<cdot>x)"
by (simp add: branch_def)

subsubsection {* Cases operator *}

definition
  cases :: "'a maybe \<rightarrow> 'a::pcpo" where
  "cases = maybe_when\<cdot>\<bottom>\<cdot>ID"

text {* rewrite rules for cases *}

lemma cases_strict [simp]: "cases\<cdot>\<bottom> = \<bottom>"
by (simp add: cases_def)

lemma cases_fail [simp]: "cases\<cdot>fail = \<bottom>"
by (simp add: cases_def)

lemma cases_return [simp]: "cases\<cdot>(return\<cdot>x) = x"
by (simp add: cases_def)

subsection {* Case syntax *}

nonterminals
  Case_syn  Cases_syn

syntax
  "_Case_syntax":: "['a, Cases_syn] => 'b"               ("(Case _ of/ _)" 10)
  "_Case1"      :: "['a, 'b] => Case_syn"                ("(2_ =>/ _)" 10)
  ""            :: "Case_syn => Cases_syn"               ("_")
  "_Case2"      :: "[Case_syn, Cases_syn] => Cases_syn"  ("_/ | _")

syntax (xsymbols)
  "_Case1"      :: "['a, 'b] => Case_syn"                ("(2_ \<Rightarrow>/ _)" 10)

translations
  "_Case_syntax x ms" == "CONST Fixrec.cases\<cdot>(ms\<cdot>x)"
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
(* rewrites (_pat x) => (return) *)
(* rewrites (_variable x t) => (Abs_CFun (%x. t)) *)
  [("_pat", K (Syntax.const "Fixrec.return")),
   mk_binder_tr ("_variable", "Abs_CFun")];
*}

text {* Printing Case expressions *}

syntax
  "_match" :: "'a"

print_translation {*
  let
    fun dest_LAM (Const (@{const_syntax Rep_CFun},_) $ Const (@{const_syntax unit_when},_) $ t) =
          (Syntax.const "_noargs", t)
    |   dest_LAM (Const (@{const_syntax Rep_CFun},_) $ Const (@{const_syntax csplit},_) $ t) =
          let
            val (v1, t1) = dest_LAM t;
            val (v2, t2) = dest_LAM t1;
          in (Syntax.const "_args" $ v1 $ v2, t2) end 
    |   dest_LAM (Const (@{const_syntax Abs_CFun},_) $ t) =
          let
            val abs = case t of Abs abs => abs
                | _ => ("x", dummyT, incr_boundvars 1 t $ Bound 0);
            val (x, t') = atomic_abs_tr' abs;
          in (Syntax.const "_variable" $ x, t') end
    |   dest_LAM _ = raise Match; (* too few vars: abort translation *)

    fun Case1_tr' [Const(@{const_syntax branch},_) $ p, r] =
          let val (v, t) = dest_LAM r;
          in Syntax.const "_Case1" $ (Syntax.const "_match" $ p $ v) $ t end;

  in [(@{const_syntax Rep_CFun}, Case1_tr')] end;
*}

translations
  "x" <= "_match Fixrec.return (_variable x)"


subsection {* Pattern combinators for data constructors *}

types ('a, 'b) pat = "'a \<rightarrow> 'b maybe"

definition
  cpair_pat :: "('a, 'c) pat \<Rightarrow> ('b, 'd) pat \<Rightarrow> ('a \<times> 'b, 'c \<times> 'd) pat" where
  "cpair_pat p1 p2 = (\<Lambda>\<langle>x, y\<rangle>.
    bind\<cdot>(p1\<cdot>x)\<cdot>(\<Lambda> a. bind\<cdot>(p2\<cdot>y)\<cdot>(\<Lambda> b. return\<cdot>\<langle>a, b\<rangle>)))"

definition
  spair_pat ::
  "('a, 'c) pat \<Rightarrow> ('b, 'd) pat \<Rightarrow> ('a::pcpo \<otimes> 'b::pcpo, 'c \<times> 'd) pat" where
  "spair_pat p1 p2 = (\<Lambda>(:x, y:). cpair_pat p1 p2\<cdot>\<langle>x, y\<rangle>)"

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
  "TT_pat = (\<Lambda> b. If b then return\<cdot>() else fail fi)"

definition
  FF_pat :: "(tr, unit) pat" where
  "FF_pat = (\<Lambda> b. If b then fail else return\<cdot>() fi)"

definition
  ONE_pat :: "(one, unit) pat" where
  "ONE_pat = (\<Lambda> ONE. return\<cdot>())"

text {* Parse translations (patterns) *}
translations
  "_pat (XCONST cpair\<cdot>x\<cdot>y)" => "CONST cpair_pat (_pat x) (_pat y)"
  "_pat (XCONST spair\<cdot>x\<cdot>y)" => "CONST spair_pat (_pat x) (_pat y)"
  "_pat (XCONST sinl\<cdot>x)" => "CONST sinl_pat (_pat x)"
  "_pat (XCONST sinr\<cdot>x)" => "CONST sinr_pat (_pat x)"
  "_pat (XCONST up\<cdot>x)" => "CONST up_pat (_pat x)"
  "_pat (XCONST TT)" => "CONST TT_pat"
  "_pat (XCONST FF)" => "CONST FF_pat"
  "_pat (XCONST ONE)" => "CONST ONE_pat"

text {* CONST version is also needed for constructors with special syntax *}
translations
  "_pat (CONST cpair\<cdot>x\<cdot>y)" => "CONST cpair_pat (_pat x) (_pat y)"
  "_pat (CONST spair\<cdot>x\<cdot>y)" => "CONST spair_pat (_pat x) (_pat y)"

text {* Parse translations (variables) *}
translations
  "_variable (XCONST cpair\<cdot>x\<cdot>y) r" => "_variable (_args x y) r"
  "_variable (XCONST spair\<cdot>x\<cdot>y) r" => "_variable (_args x y) r"
  "_variable (XCONST sinl\<cdot>x) r" => "_variable x r"
  "_variable (XCONST sinr\<cdot>x) r" => "_variable x r"
  "_variable (XCONST up\<cdot>x) r" => "_variable x r"
  "_variable (XCONST TT) r" => "_variable _noargs r"
  "_variable (XCONST FF) r" => "_variable _noargs r"
  "_variable (XCONST ONE) r" => "_variable _noargs r"

translations
  "_variable (CONST cpair\<cdot>x\<cdot>y) r" => "_variable (_args x y) r"
  "_variable (CONST spair\<cdot>x\<cdot>y) r" => "_variable (_args x y) r"

text {* Print translations *}
translations
  "CONST cpair\<cdot>(_match p1 v1)\<cdot>(_match p2 v2)"
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
  "branch p\<cdot>r\<cdot>x = \<bottom> \<Longrightarrow> branch (cpair_pat p q)\<cdot>(csplit\<cdot>r)\<cdot>\<langle>x, y\<rangle> = \<bottom>"
apply (simp add: branch_def cpair_pat_def)
apply (rule_tac p="p\<cdot>x" in maybeE, simp_all)
done

lemma cpair_pat2:
  "branch p\<cdot>r\<cdot>x = fail \<Longrightarrow> branch (cpair_pat p q)\<cdot>(csplit\<cdot>r)\<cdot>\<langle>x, y\<rangle> = fail"
apply (simp add: branch_def cpair_pat_def)
apply (rule_tac p="p\<cdot>x" in maybeE, simp_all)
done

lemma cpair_pat3:
  "branch p\<cdot>r\<cdot>x = return\<cdot>s \<Longrightarrow>
   branch (cpair_pat p q)\<cdot>(csplit\<cdot>r)\<cdot>\<langle>x, y\<rangle> = branch q\<cdot>s\<cdot>y"
apply (simp add: branch_def cpair_pat_def)
apply (rule_tac p="p\<cdot>x" in maybeE, simp_all)
apply (rule_tac p="q\<cdot>y" in maybeE, simp_all)
done

lemmas cpair_pat [simp] =
  cpair_pat1 cpair_pat2 cpair_pat3

lemma spair_pat [simp]:
  "branch (spair_pat p1 p2)\<cdot>r\<cdot>\<bottom> = \<bottom>"
  "\<lbrakk>x \<noteq> \<bottom>; y \<noteq> \<bottom>\<rbrakk>
     \<Longrightarrow> branch (spair_pat p1 p2)\<cdot>r\<cdot>(:x, y:) =
         branch (cpair_pat p1 p2)\<cdot>r\<cdot>\<langle>x, y\<rangle>"
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
  "branch TT_pat\<cdot>(unit_when\<cdot>r)\<cdot>TT = return\<cdot>r"
  "branch TT_pat\<cdot>(unit_when\<cdot>r)\<cdot>FF = fail"
by (simp_all add: branch_def TT_pat_def)

lemma FF_pat [simp]:
  "branch FF_pat\<cdot>(unit_when\<cdot>r)\<cdot>\<bottom> = \<bottom>"
  "branch FF_pat\<cdot>(unit_when\<cdot>r)\<cdot>TT = fail"
  "branch FF_pat\<cdot>(unit_when\<cdot>r)\<cdot>FF = return\<cdot>r"
by (simp_all add: branch_def FF_pat_def)

lemma ONE_pat [simp]:
  "branch ONE_pat\<cdot>(unit_when\<cdot>r)\<cdot>\<bottom> = \<bottom>"
  "branch ONE_pat\<cdot>(unit_when\<cdot>r)\<cdot>ONE = return\<cdot>r"
by (simp_all add: branch_def ONE_pat_def)


subsection {* Wildcards, as-patterns, and lazy patterns *}

syntax
  "_as_pat" :: "[idt, 'a] \<Rightarrow> 'a" (infixr "\<as>" 10)
  "_lazy_pat" :: "'a \<Rightarrow> 'a" ("\<lazy> _" [1000] 1000)

definition
  wild_pat :: "'a \<rightarrow> unit maybe" where
  "wild_pat = (\<Lambda> x. return\<cdot>())"

definition
  as_pat :: "('a \<rightarrow> 'b maybe) \<Rightarrow> 'a \<rightarrow> ('a \<times> 'b) maybe" where
  "as_pat p = (\<Lambda> x. bind\<cdot>(p\<cdot>x)\<cdot>(\<Lambda> a. return\<cdot>\<langle>x, a\<rangle>))"

definition
  lazy_pat :: "('a \<rightarrow> 'b::pcpo maybe) \<Rightarrow> ('a \<rightarrow> 'b maybe)" where
  "lazy_pat p = (\<Lambda> x. return\<cdot>(cases\<cdot>(p\<cdot>x)))"

text {* Parse translations (patterns) *}
translations
  "_pat _" => "CONST wild_pat"
  "_pat (_as_pat x y)" => "CONST as_pat (_pat y)"
  "_pat (_lazy_pat x)" => "CONST lazy_pat (_pat x)"

text {* Parse translations (variables) *}
translations
  "_variable _ r" => "_variable _noargs r"
  "_variable (_as_pat x y) r" => "_variable (_args x y) r"
  "_variable (_lazy_pat x) r" => "_variable x r"

text {* Print translations *}
translations
  "_" <= "_match (CONST wild_pat) _noargs"
  "_as_pat x (_match p v)" <= "_match (CONST as_pat p) (_args (_variable x) v)"
  "_lazy_pat (_match p v)" <= "_match (CONST lazy_pat p) v"

text {* Lazy patterns in lambda abstractions *}
translations
  "_cabs (_lazy_pat p) r" == "CONST Fixrec.cases oo (_Case1 (_lazy_pat p) r)"

lemma wild_pat [simp]: "branch wild_pat\<cdot>(unit_when\<cdot>r)\<cdot>x = return\<cdot>r"
by (simp add: branch_def wild_pat_def)

lemma as_pat [simp]:
  "branch (as_pat p)\<cdot>(csplit\<cdot>r)\<cdot>x = branch p\<cdot>(r\<cdot>x)\<cdot>x"
apply (simp add: branch_def as_pat_def)
apply (rule_tac p="p\<cdot>x" in maybeE, simp_all)
done

lemma lazy_pat [simp]:
  "branch p\<cdot>r\<cdot>x = \<bottom> \<Longrightarrow> branch (lazy_pat p)\<cdot>r\<cdot>x = return\<cdot>(r\<cdot>\<bottom>)"
  "branch p\<cdot>r\<cdot>x = fail \<Longrightarrow> branch (lazy_pat p)\<cdot>r\<cdot>x = return\<cdot>(r\<cdot>\<bottom>)"
  "branch p\<cdot>r\<cdot>x = return\<cdot>s \<Longrightarrow> branch (lazy_pat p)\<cdot>r\<cdot>x = return\<cdot>s"
apply (simp_all add: branch_def lazy_pat_def)
apply (rule_tac [!] p="p\<cdot>x" in maybeE, simp_all)
done


subsection {* Match functions for built-in types *}

defaultsort pcpo

definition
  match_UU :: "'a \<rightarrow> 'c maybe \<rightarrow> 'c maybe"
where
  "match_UU = strictify\<cdot>(\<Lambda> x k. fail)"

definition
  match_cpair :: "'a::cpo \<times> 'b::cpo \<rightarrow> ('a \<rightarrow> 'b \<rightarrow> 'c maybe) \<rightarrow> 'c maybe"
where
  "match_cpair = (\<Lambda> x k. csplit\<cdot>k\<cdot>x)"

definition
  match_spair :: "'a \<otimes> 'b \<rightarrow> ('a \<rightarrow> 'b \<rightarrow> 'c maybe) \<rightarrow> 'c maybe"
where
  "match_spair = (\<Lambda> x k. ssplit\<cdot>k\<cdot>x)"

definition
  match_sinl :: "'a \<oplus> 'b \<rightarrow> ('a \<rightarrow> 'c maybe) \<rightarrow> 'c maybe"
where
  "match_sinl = (\<Lambda> x k. sscase\<cdot>k\<cdot>(\<Lambda> b. fail)\<cdot>x)"

definition
  match_sinr :: "'a \<oplus> 'b \<rightarrow> ('b \<rightarrow> 'c maybe) \<rightarrow> 'c maybe"
where
  "match_sinr = (\<Lambda> x k. sscase\<cdot>(\<Lambda> a. fail)\<cdot>k\<cdot>x)"

definition
  match_up :: "'a::cpo u \<rightarrow> ('a \<rightarrow> 'c maybe) \<rightarrow> 'c maybe"
where
  "match_up = (\<Lambda> x k. fup\<cdot>k\<cdot>x)"

definition
  match_ONE :: "one \<rightarrow> 'c maybe \<rightarrow> 'c maybe"
where
  "match_ONE = (\<Lambda> ONE k. k)"

definition
  match_TT :: "tr \<rightarrow> 'c maybe \<rightarrow> 'c maybe"
where
  "match_TT = (\<Lambda> x k. If x then k else fail fi)"
 
definition
  match_FF :: "tr \<rightarrow> 'c maybe \<rightarrow> 'c maybe"
where
  "match_FF = (\<Lambda> x k. If x then fail else k fi)"

lemma match_UU_simps [simp]:
  "match_UU\<cdot>\<bottom>\<cdot>k = \<bottom>"
  "x \<noteq> \<bottom> \<Longrightarrow> match_UU\<cdot>x\<cdot>k = fail"
by (simp_all add: match_UU_def)

lemma match_cpair_simps [simp]:
  "match_cpair\<cdot>\<langle>x, y\<rangle>\<cdot>k = k\<cdot>x\<cdot>y"
  "match_cpair\<cdot>(x, y)\<cdot>k = k\<cdot>x\<cdot>y"
by (simp_all add: match_cpair_def)

lemma match_spair_simps [simp]:
  "\<lbrakk>x \<noteq> \<bottom>; y \<noteq> \<bottom>\<rbrakk> \<Longrightarrow> match_spair\<cdot>(:x, y:)\<cdot>k = k\<cdot>x\<cdot>y"
  "match_spair\<cdot>\<bottom>\<cdot>k = \<bottom>"
by (simp_all add: match_spair_def)

lemma match_sinl_simps [simp]:
  "x \<noteq> \<bottom> \<Longrightarrow> match_sinl\<cdot>(sinl\<cdot>x)\<cdot>k = k\<cdot>x"
  "y \<noteq> \<bottom> \<Longrightarrow> match_sinl\<cdot>(sinr\<cdot>y)\<cdot>k = fail"
  "match_sinl\<cdot>\<bottom>\<cdot>k = \<bottom>"
by (simp_all add: match_sinl_def)

lemma match_sinr_simps [simp]:
  "x \<noteq> \<bottom> \<Longrightarrow> match_sinr\<cdot>(sinl\<cdot>x)\<cdot>k = fail"
  "y \<noteq> \<bottom> \<Longrightarrow> match_sinr\<cdot>(sinr\<cdot>y)\<cdot>k = k\<cdot>y"
  "match_sinr\<cdot>\<bottom>\<cdot>k = \<bottom>"
by (simp_all add: match_sinr_def)

lemma match_up_simps [simp]:
  "match_up\<cdot>(up\<cdot>x)\<cdot>k = k\<cdot>x"
  "match_up\<cdot>\<bottom>\<cdot>k = \<bottom>"
by (simp_all add: match_up_def)

lemma match_ONE_simps [simp]:
  "match_ONE\<cdot>ONE\<cdot>k = k"
  "match_ONE\<cdot>\<bottom>\<cdot>k = \<bottom>"
by (simp_all add: match_ONE_def)

lemma match_TT_simps [simp]:
  "match_TT\<cdot>TT\<cdot>k = k"
  "match_TT\<cdot>FF\<cdot>k = fail"
  "match_TT\<cdot>\<bottom>\<cdot>k = \<bottom>"
by (simp_all add: match_TT_def)

lemma match_FF_simps [simp]:
  "match_FF\<cdot>FF\<cdot>k = k"
  "match_FF\<cdot>TT\<cdot>k = fail"
  "match_FF\<cdot>\<bottom>\<cdot>k = \<bottom>"
by (simp_all add: match_FF_def)

subsection {* Mutual recursion *}

text {*
  The following rules are used to prove unfolding theorems from
  fixed-point definitions of mutually recursive functions.
*}

lemma Pair_equalI: "\<lbrakk>x \<equiv> fst p; y \<equiv> snd p\<rbrakk> \<Longrightarrow> (x, y) \<equiv> p"
by simp

lemma Pair_eqD1: "(x, y) = (x', y') \<Longrightarrow> x = x'"
by simp

lemma Pair_eqD2: "(x, y) = (x', y') \<Longrightarrow> y = y'"
by simp

lemma def_cont_fix_eq:
  "\<lbrakk>f \<equiv> fix\<cdot>(Abs_CFun F); cont F\<rbrakk> \<Longrightarrow> f = F f"
by (simp, subst fix_eq, simp)

lemma def_cont_fix_ind:
  "\<lbrakk>f \<equiv> fix\<cdot>(Abs_CFun F); cont F; adm P; P \<bottom>; \<And>x. P x \<Longrightarrow> P (F x)\<rbrakk> \<Longrightarrow> P f"
by (simp add: fix_ind)

text {* lemma for proving rewrite rules *}

lemma ssubst_lhs: "\<lbrakk>t = s; P s = Q\<rbrakk> \<Longrightarrow> P t = Q"
by simp


subsection {* Initializing the fixrec package *}

use "Tools/fixrec.ML"

setup {* Fixrec.setup *}

setup {*
  Fixrec.add_matchers
    [ (@{const_name up}, @{const_name match_up}),
      (@{const_name sinl}, @{const_name match_sinl}),
      (@{const_name sinr}, @{const_name match_sinr}),
      (@{const_name spair}, @{const_name match_spair}),
      (@{const_name cpair}, @{const_name match_cpair}),
      (@{const_name Pair}, @{const_name match_cpair}),
      (@{const_name ONE}, @{const_name match_ONE}),
      (@{const_name TT}, @{const_name match_TT}),
      (@{const_name FF}, @{const_name match_FF}),
      (@{const_name UU}, @{const_name match_UU}) ]
*}

hide (open) const return bind fail run cases

end
