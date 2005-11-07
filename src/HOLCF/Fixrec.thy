(*  Title:      HOLCF/Fixrec.thy
    ID:         $Id$
    Author:     Amber Telfer and Brian Huffman
*)

header "Package for defining recursive functions in HOLCF"

theory Fixrec
imports Sprod Ssum Up One Tr Fix
uses ("fixrec_package.ML")
begin

subsection {* Maybe monad type *}

defaultsort cpo

types 'a maybe = "one ++ 'a u"

constdefs
  fail :: "'a maybe"
  "fail \<equiv> sinl\<cdot>ONE"

  return :: "'a \<rightarrow> 'a maybe"
  "return \<equiv> sinr oo up"

lemma maybeE:
  "\<lbrakk>p = \<bottom> \<Longrightarrow> Q; p = fail \<Longrightarrow> Q; \<And>x. p = return\<cdot>x \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
apply (unfold fail_def return_def)
apply (rule_tac p=p in ssumE, simp)
apply (rule_tac p=x in oneE, simp, simp)
apply (rule_tac p=y in upE, simp, simp)
done

subsubsection {* Monadic bind operator *}

constdefs
  bind :: "'a maybe \<rightarrow> ('a \<rightarrow> 'b maybe) \<rightarrow> 'b maybe"
  "bind \<equiv> \<Lambda> m f. sscase\<cdot>sinl\<cdot>(fup\<cdot>f)\<cdot>m"

syntax ">>=" :: "['a maybe, 'a \<rightarrow> 'b maybe] \<Rightarrow> 'b maybe" (infixl ">>=" 50)
translations "m >>= f" == "bind\<cdot>m\<cdot>f"

nonterminals
  maybebind maybebinds

syntax 
  "_MBIND"  :: "pttrn \<Rightarrow> 'a maybe \<Rightarrow> maybebind"         ("(2_ <-/ _)" 10)
  ""        :: "maybebind \<Rightarrow> maybebinds"                ("_")

  "_MBINDS" :: "[maybebind, maybebinds] \<Rightarrow> maybebinds"  ("_;/ _")
  "_MDO"    :: "[maybebinds, 'a maybe] \<Rightarrow> 'a maybe"     ("(do _;/ (_))" 10)

translations
  "_MDO (_MBINDS b bs) e" == "_MDO b (_MDO bs e)"
  "do (x,y) <- m; e" == "m >>= (LAM <x,y>. e)" 
  "do x <- m; e"            == "m >>= (LAM x. e)"

text {* monad laws *}

lemma bind_strict [simp]: "UU >>= f = UU"
by (simp add: bind_def)

lemma bind_fail [simp]: "fail >>= f = fail"
by (simp add: bind_def fail_def)

lemma left_unit [simp]: "(return\<cdot>a) >>= k = k\<cdot>a"
by (simp add: bind_def return_def)

lemma right_unit [simp]: "m >>= return = m"
by (rule_tac p=m in maybeE, simp_all)

lemma bind_assoc [simp]:
 "(do b <- (do a <- m; k\<cdot>a); h\<cdot>b) = (do a <- m; b <- k\<cdot>a; h\<cdot>b)"
by (rule_tac p=m in maybeE, simp_all)

subsubsection {* Run operator *}

constdefs
  run:: "'a::pcpo maybe \<rightarrow> 'a"
  "run \<equiv> sscase\<cdot>\<bottom>\<cdot>(fup\<cdot>ID)"

text {* rewrite rules for run *}

lemma run_strict [simp]: "run\<cdot>\<bottom> = \<bottom>"
by (simp add: run_def)

lemma run_fail [simp]: "run\<cdot>fail = \<bottom>"
by (simp add: run_def fail_def)

lemma run_return [simp]: "run\<cdot>(return\<cdot>x) = x"
by (simp add: run_def return_def)

subsubsection {* Monad plus operator *}

constdefs
  mplus :: "'a maybe \<rightarrow> 'a maybe \<rightarrow> 'a maybe"
  "mplus \<equiv> \<Lambda> m1 m2. sscase\<cdot>(\<Lambda> x. m2)\<cdot>(fup\<cdot>return)\<cdot>m1"

syntax "+++" :: "['a maybe, 'a maybe] \<Rightarrow> 'a maybe" (infixr "+++" 65)
translations "m1 +++ m2" == "mplus\<cdot>m1\<cdot>m2"

text {* rewrite rules for mplus *}

lemma mplus_strict [simp]: "\<bottom> +++ m = \<bottom>"
by (simp add: mplus_def)

lemma mplus_fail [simp]: "fail +++ m = m"
by (simp add: mplus_def fail_def)

lemma mplus_return [simp]: "return\<cdot>x +++ m = return\<cdot>x"
by (simp add: mplus_def return_def)

lemma mplus_fail2 [simp]: "m +++ fail = m"
by (rule_tac p=m in maybeE, simp_all)

lemma mplus_assoc: "(x +++ y) +++ z = x +++ (y +++ z)"
by (rule_tac p=x in maybeE, simp_all)

subsubsection {* Fatbar combinator *}

constdefs
  fatbar :: "('a \<rightarrow> 'b maybe) \<rightarrow> ('a \<rightarrow> 'b maybe) \<rightarrow> ('a \<rightarrow> 'b maybe)"
  "fatbar \<equiv> \<Lambda> a b x. a\<cdot>x +++ b\<cdot>x"

syntax
  "\<parallel>" :: "['a \<rightarrow> 'b maybe, 'a \<rightarrow> 'b maybe] \<Rightarrow> 'a \<rightarrow> 'b maybe" (infixr "\<parallel>" 60)
translations
  "m1 \<parallel> m2" == "fatbar\<cdot>m1\<cdot>m2"

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

subsection {* Pattern combinators *}

types ('a,'b,'c) pat = "'b \<rightarrow> 'a \<rightarrow> 'c maybe"

constdefs
  wild_pat :: "('a, 'b, 'b) pat"
  "wild_pat \<equiv> \<Lambda> r a. return\<cdot>r"

  var_pat :: "('a, 'a \<rightarrow> 'b, 'b) pat"
  "var_pat \<equiv> \<Lambda> r a. return\<cdot>(r\<cdot>a)"

lemma wild_pat [simp]: "wild_pat\<cdot>r\<cdot>a = return\<cdot>r"
by (simp add: wild_pat_def)

lemma var_pat [simp]: "var_pat\<cdot>r\<cdot>a = return\<cdot>(r\<cdot>a)"
by (simp add: var_pat_def)

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

text {* Intermediate tags for parsing/printing *}
syntax
  "_pat" :: "'a"
  "_var" :: "'a"
  "_match" :: "'a"

text {* Parsing Case expressions *}

translations
  "_Case_syntax x cs" => "run\<cdot>(cs\<cdot>x)"
  "_Case2 c cs" => "fatbar\<cdot>c\<cdot>cs"
  "_Case1 p r" => "_match (_var p) r"
  "_var _" => "wild_pat"

parse_translation {*
  let
    fun capp (t,u) = Syntax.const "Rep_CFun" $ t $ u;
    fun cabs (x,t) = (snd (mk_binder_tr ("_cabs", "Abs_CFun"))) [x,t];

    fun get_vars (Const ("_var",_) $ x) = [x]
    |   get_vars (t $ u) = get_vars t @ get_vars u
    |   get_vars t = [];

    fun rem_vars (Const ("_var",_) $ x) = Syntax.const "var_pat"
    |   rem_vars (t $ u) = rem_vars t $ rem_vars u
    |   rem_vars t = t;

    fun match_tr [pat, rhs] =
          capp (rem_vars pat, foldr cabs rhs (get_vars pat))
    |   match_tr ts = raise TERM ("match_tr", ts);

  in [("_match", match_tr)] end;
*}

text {* Printing Case expressions *}

translations
  "_" <= "_pat wild_pat"
  "x" <= "_pat (_var x)"

print_translation {*
  let
    fun dest_cabs (Const ("Abs_CFun",_) $ t) =
          let val abs = case t of Abs abs => abs
                  | _ => ("x", dummyT, incr_boundvars 1 t $ Bound 0);
          in atomic_abs_tr' abs end
    |   dest_cabs _ = raise Match; (* too few vars: abort translation *)

    fun put_vars (Const ("var_pat",_), rhs) =
          let val (x, rhs') = dest_cabs rhs;
          in (Syntax.const "_var" $ x, rhs') end
    |   put_vars (t $ u, rhs) =
          let
            val (t', rhs') = put_vars (t,rhs);
            val (u', rhs'') = put_vars (u,rhs');
          in (t' $ u', rhs'') end
    |   put_vars (t, rhs) = (t, rhs);

    fun Case1_tr' (_ $ pat $ rhs) = let
          val (pat', rhs') = put_vars (pat, rhs);
        in Syntax.const "_Case1" $ (Syntax.const "_pat" $ pat') $ rhs' end;

    fun Case2_tr' (_ $ (_ $ Const ("fatbar",_) $ m) $ ms) =
          Syntax.const "_Case2" $ Case1_tr' m $ Case2_tr' ms
    |   Case2_tr' t = Case1_tr' t;

    fun Case_syntax_tr' [Const ("run",_), _ $ ms $ x] =
          Syntax.const "_Case_syntax" $ x $ Case2_tr' ms;

  in [("Rep_CFun", Case_syntax_tr')] end;
*}

subsection {* Pattern combinators for built-in types *}

constdefs
  cpair_pat :: "('a, _, _) pat \<Rightarrow> ('b, _, _) pat \<Rightarrow> ('a \<times> 'b, _, _) pat"
  "cpair_pat p1 p2 \<equiv> \<Lambda> r1 \<langle>x1,x2\<rangle>. bind\<cdot>(p1\<cdot>r1\<cdot>x1)\<cdot>(\<Lambda> r2. p2\<cdot>r2\<cdot>x2)"

  spair_pat :: "(_, _, _) pat \<Rightarrow> (_, _, _) pat \<Rightarrow> (_, _, _) pat"
  "spair_pat p1 p2 \<equiv> \<Lambda> r (:x,y:). cpair_pat p1 p2\<cdot>r\<cdot>\<langle>x,y\<rangle>"

  sinl_pat :: "(_, _, _) pat \<Rightarrow> (_, _, _) pat"
  "sinl_pat p \<equiv> \<Lambda> r a. case a of sinl\<cdot>x \<Rightarrow> p\<cdot>r\<cdot>x | sinr\<cdot>y \<Rightarrow> fail"

  sinr_pat :: "(_, _, _) pat \<Rightarrow> (_, _, _) pat"
  "sinr_pat p \<equiv> \<Lambda> r a. case a of sinl\<cdot>x \<Rightarrow> fail | sinr\<cdot>y \<Rightarrow> p\<cdot>r\<cdot>y"

  up_pat :: "('a, _, _) pat \<Rightarrow> ('a u, _, _) pat"
  "up_pat p \<equiv> \<Lambda> r a. case a of up\<cdot>x \<Rightarrow> p\<cdot>r\<cdot>x"

  Def_pat :: "'a::type \<Rightarrow> ('a lift, _, _) pat"
  "Def_pat x \<equiv> \<Lambda> r. FLIFT y. if x = y then return\<cdot>r else fail"

  ONE_pat :: "(one, _, _) pat"
  "ONE_pat \<equiv> \<Lambda> r ONE. return\<cdot>r"

  TT_pat :: "(tr, _, _) pat"
  "TT_pat \<equiv> \<Lambda> r b. If b then return\<cdot>r else fail fi"

  FF_pat :: "(tr, _, _) pat"
  "FF_pat \<equiv> \<Lambda> r b. If b then fail else return\<cdot>r fi"

text {* Parse translations *}
translations
  "_var (cpair\<cdot>p1\<cdot>p2)" => "cpair_pat (_var p1) (_var p2)"
  "_var (spair\<cdot>p1\<cdot>p2)" => "spair_pat (_var p1) (_var p2)"
  "_var (sinl\<cdot>p1)"     => "sinl_pat (_var p1)"
  "_var (sinr\<cdot>p1)"     => "sinr_pat (_var p1)"
  "_var (up\<cdot>p1)"       => "up_pat (_var p1)"
  "_var (Def x)"       => "Def_pat x"
  "_var ONE"           => "ONE_pat"
  "_var TT"            => "TT_pat"
  "_var FF"            => "FF_pat"

text {* Print translations *}
translations
  "cpair\<cdot>(_pat p1)\<cdot>(_pat p2)" <= "_pat (cpair_pat p1 p2)"
  "spair\<cdot>(_pat p1)\<cdot>(_pat p2)" <= "_pat (spair_pat p1 p2)"
  "sinl\<cdot>(_pat p1)"            <= "_pat (sinl_pat p1)"
  "sinr\<cdot>(_pat p1)"            <= "_pat (sinr_pat p1)"
  "up\<cdot>(_pat p1)"              <= "_pat (up_pat p1)"
  "Def x"                     <= "_pat (Def_pat x)"
  "TT"                        <= "_pat (TT_pat)"
  "FF"                        <= "_pat (FF_pat)"

lemma cpair_pat_simps [simp]:
  "p1\<cdot>r\<cdot>x = \<bottom> \<Longrightarrow> cpair_pat p1 p2\<cdot>r\<cdot><x,y> = \<bottom>"
  "p1\<cdot>r\<cdot>x = fail \<Longrightarrow> cpair_pat p1 p2\<cdot>r\<cdot><x,y> = fail"
  "p1\<cdot>r\<cdot>x = return\<cdot>r' \<Longrightarrow> cpair_pat p1 p2\<cdot>r\<cdot><x,y> = p2\<cdot>r'\<cdot>y"
by (simp_all add: cpair_pat_def)

lemma spair_pat_simps [simp]:
  "spair_pat p1 p2\<cdot>r\<cdot>\<bottom> = \<bottom>"
  "\<lbrakk>x \<noteq> \<bottom>; y \<noteq> \<bottom>\<rbrakk> \<Longrightarrow> spair_pat p1 p2\<cdot>r\<cdot>(:x, y:) = cpair_pat p1 p2\<cdot>r\<cdot>\<langle>x, y\<rangle>"
by (simp_all add: spair_pat_def)

lemma sinl_pat_simps [simp]:
  "sinl_pat p\<cdot>r\<cdot>\<bottom> = \<bottom>"
  "x \<noteq> \<bottom> \<Longrightarrow> sinl_pat p\<cdot>r\<cdot>(sinl\<cdot>x) = p\<cdot>r\<cdot>x"
  "x \<noteq> \<bottom> \<Longrightarrow> sinl_pat p\<cdot>r\<cdot>(sinr\<cdot>x) = fail"
by (simp_all add: sinl_pat_def)

lemma sinr_pat_simps [simp]:
  "sinr_pat p\<cdot>r\<cdot>\<bottom> = \<bottom>"
  "x \<noteq> \<bottom> \<Longrightarrow> sinr_pat p\<cdot>r\<cdot>(sinl\<cdot>x) = fail"
  "x \<noteq> \<bottom> \<Longrightarrow> sinr_pat p\<cdot>r\<cdot>(sinr\<cdot>x) = p\<cdot>r\<cdot>x"
by (simp_all add: sinr_pat_def)

lemma up_pat_simps [simp]:
  "up_pat p\<cdot>r\<cdot>\<bottom> = \<bottom>"
  "up_pat p\<cdot>r\<cdot>(up\<cdot>x) = p\<cdot>r\<cdot>x"
by (simp_all add: up_pat_def)

lemma Def_pat_simps [simp]:
  "Def_pat x\<cdot>r\<cdot>\<bottom> = \<bottom>"
  "Def_pat x\<cdot>r\<cdot>(Def x) = return\<cdot>r"
  "x \<noteq> y \<Longrightarrow> Def_pat x\<cdot>r\<cdot>(Def y) = fail"
by (simp_all add: Def_pat_def)

lemma ONE_pat_simps [simp]:
  "ONE_pat\<cdot>r\<cdot>\<bottom> = \<bottom>"
  "ONE_pat\<cdot>r\<cdot>ONE = return\<cdot>r"
by (simp_all add: ONE_pat_def)

lemma TT_pat_simps [simp]:
  "TT_pat\<cdot>r\<cdot>\<bottom> = \<bottom>"
  "TT_pat\<cdot>r\<cdot>TT = return\<cdot>r"
  "TT_pat\<cdot>r\<cdot>FF = fail"
by (simp_all add: TT_pat_def)

lemma FF_pat_simps [simp]:
  "FF_pat\<cdot>r\<cdot>\<bottom> = \<bottom>"
  "FF_pat\<cdot>r\<cdot>TT = fail"
  "FF_pat\<cdot>r\<cdot>FF = return\<cdot>r"
by (simp_all add: FF_pat_def)

subsection {* As-patterns *}

syntax
  "_as_pattern" :: "['a, 'a] \<Rightarrow> 'a" (* infixr "as" 10 *)
  (* TODO: choose a non-ambiguous syntax for as-patterns *)

constdefs
  as_pat :: "('a,'b,'c) pat \<Rightarrow> ('a,'c,'d) pat \<Rightarrow> ('a,'b,'d) pat"
  "as_pat p1 p2 \<equiv> \<Lambda> r a. cpair_pat p1 p2\<cdot>r\<cdot>\<langle>a, a\<rangle>"

translations
  "_var (_as_pattern p1 p2)" => "as_pat (_var p1) (_var p2)"
  "_as_pattern (_pat p1) (_pat p2)" <= "_pat (as_pat p1 p2)"

lemma as_pat [simp]: "as_pat p1 p2\<cdot>r\<cdot>a = cpair_pat p1 p2\<cdot>r\<cdot>\<langle>a, a\<rangle>"
by (simp add: as_pat_def)

subsection {* Match functions for built-in types *}

defaultsort pcpo

constdefs
  match_UU :: "'a \<rightarrow> unit maybe"
  "match_UU \<equiv> \<Lambda> x. fail"

  match_cpair :: "'a::cpo \<times> 'b::cpo \<rightarrow> ('a \<times> 'b) maybe"
  "match_cpair \<equiv> csplit\<cdot>(\<Lambda> x y. return\<cdot><x,y>)"

  match_spair :: "'a \<otimes> 'b \<rightarrow> ('a \<times> 'b) maybe"
  "match_spair \<equiv> ssplit\<cdot>(\<Lambda> x y. return\<cdot><x,y>)"

  match_sinl :: "'a \<oplus> 'b \<rightarrow> 'a maybe"
  "match_sinl \<equiv> sscase\<cdot>return\<cdot>(\<Lambda> y. fail)"

  match_sinr :: "'a \<oplus> 'b \<rightarrow> 'b maybe"
  "match_sinr \<equiv> sscase\<cdot>(\<Lambda> x. fail)\<cdot>return"

  match_up :: "'a::cpo u \<rightarrow> 'a maybe"
  "match_up \<equiv> fup\<cdot>return"

  match_ONE :: "one \<rightarrow> unit maybe"
  "match_ONE \<equiv> \<Lambda> ONE. return\<cdot>()"
 
  match_TT :: "tr \<rightarrow> unit maybe"
  "match_TT \<equiv> \<Lambda> b. If b then return\<cdot>() else fail fi"
 
  match_FF :: "tr \<rightarrow> unit maybe"
  "match_FF \<equiv> \<Lambda> b. If b then fail else return\<cdot>() fi"

lemma match_UU_simps [simp]:
  "match_UU\<cdot>x = fail"
by (simp add: match_UU_def)

lemma match_cpair_simps [simp]:
  "match_cpair\<cdot><x,y> = return\<cdot><x,y>"
by (simp add: match_cpair_def)

lemma match_spair_simps [simp]:
  "\<lbrakk>x \<noteq> \<bottom>; y \<noteq> \<bottom>\<rbrakk> \<Longrightarrow> match_spair\<cdot>(:x,y:) = return\<cdot><x,y>"
  "match_spair\<cdot>\<bottom> = \<bottom>"
by (simp_all add: match_spair_def)

lemma match_sinl_simps [simp]:
  "x \<noteq> \<bottom> \<Longrightarrow> match_sinl\<cdot>(sinl\<cdot>x) = return\<cdot>x"
  "x \<noteq> \<bottom> \<Longrightarrow> match_sinl\<cdot>(sinr\<cdot>x) = fail"
  "match_sinl\<cdot>\<bottom> = \<bottom>"
by (simp_all add: match_sinl_def)

lemma match_sinr_simps [simp]:
  "x \<noteq> \<bottom> \<Longrightarrow> match_sinr\<cdot>(sinr\<cdot>x) = return\<cdot>x"
  "x \<noteq> \<bottom> \<Longrightarrow> match_sinr\<cdot>(sinl\<cdot>x) = fail"
  "match_sinr\<cdot>\<bottom> = \<bottom>"
by (simp_all add: match_sinr_def)

lemma match_up_simps [simp]:
  "match_up\<cdot>(up\<cdot>x) = return\<cdot>x"
  "match_up\<cdot>\<bottom> = \<bottom>"
by (simp_all add: match_up_def)

lemma match_ONE_simps [simp]:
  "match_ONE\<cdot>ONE = return\<cdot>()"
  "match_ONE\<cdot>\<bottom> = \<bottom>"
by (simp_all add: match_ONE_def)

lemma match_TT_simps [simp]:
  "match_TT\<cdot>TT = return\<cdot>()"
  "match_TT\<cdot>FF = fail"
  "match_TT\<cdot>\<bottom> = \<bottom>"
by (simp_all add: match_TT_def)

lemma match_FF_simps [simp]:
  "match_FF\<cdot>FF = return\<cdot>()"
  "match_FF\<cdot>TT = fail"
  "match_FF\<cdot>\<bottom> = \<bottom>"
by (simp_all add: match_FF_def)

subsection {* Mutual recursion *}

text {*
  The following rules are used to prove unfolding theorems from
  fixed-point definitions of mutually recursive functions.
*}

lemma cpair_equalI: "\<lbrakk>x \<equiv> cfst\<cdot>p; y \<equiv> csnd\<cdot>p\<rbrakk> \<Longrightarrow> <x,y> \<equiv> p"
by (simp add: surjective_pairing_Cprod2)

lemma cpair_eqD1: "<x,y> = <x',y'> \<Longrightarrow> x = x'"
by simp

lemma cpair_eqD2: "<x,y> = <x',y'> \<Longrightarrow> y = y'"
by simp

text {* lemma for proving rewrite rules *}

lemma ssubst_lhs: "\<lbrakk>t = s; P s = Q\<rbrakk> \<Longrightarrow> P t = Q"
by simp

ML {*
val cpair_equalI = thm "cpair_equalI";
val cpair_eqD1 = thm "cpair_eqD1";
val cpair_eqD2 = thm "cpair_eqD2";
val ssubst_lhs = thm "ssubst_lhs";
*}

subsection {* Initializing the fixrec package *}

use "fixrec_package.ML"

end
