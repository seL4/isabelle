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

subsection {* Pattern combinators *}

types ('a,'b,'c) pattern = "'b \<rightarrow> 'a \<rightarrow> 'c maybe"

constdefs
  wild_pat :: "('a, 'b, 'b) pattern"
  "wild_pat \<equiv> \<Lambda> r a. return\<cdot>r"

  var_pat :: "('a, 'a \<rightarrow> 'b, 'b) pattern"
  "var_pat \<equiv> \<Lambda> r a. return\<cdot>(r\<cdot>a)"

  as_pat :: "('a, 'b, 'c) pattern \<Rightarrow> ('a, 'a \<rightarrow> 'b, 'c) pattern"
  "as_pat p \<equiv> \<Lambda> r a. p\<cdot>(r\<cdot>a)\<cdot>a"

lemma wild_pat [simp]: "wild_pat\<cdot>r\<cdot>a = return\<cdot>r"
by (simp add: wild_pat_def)

lemma var_pat [simp]: "var_pat\<cdot>r\<cdot>a = return\<cdot>(r\<cdot>a)"
by (simp add: var_pat_def)

lemma as_pat [simp]: "as_pat p\<cdot>r\<cdot>a = p\<cdot>(r\<cdot>a)\<cdot>a"
by (simp add: as_pat_def)

subsection {* Case syntax *}

nonterminals
  Case_syn  Cases_syn

syntax
  "_Case_syntax":: "['a, Cases_syn] => 'b"               ("(Case _ of/ _)" 10)
  "_Case1"      :: "['a, 'b] => Case_syn"                ("(2_ =>/ _)" 10)
  ""            :: "Case_syn => Cases_syn"               ("_")
  "_Case2"      :: "[Case_syn, Cases_syn] => Cases_syn"  ("_/ | _")
  "_as_pattern" :: "[idt, 'a] \<Rightarrow> 'a"                     (infixr "as" 10)

syntax (xsymbols)
  "_Case1"      :: "['a, 'b] => Case_syn"                ("(2_ \<Rightarrow>/ _)" 10)

syntax
  "_match"   :: "'a \<Rightarrow> Case_syn" (* or Cases_syn *)
  "_as"      :: "[pttrn, Case_syn] \<Rightarrow> Case_syn"
  "_matches" :: "['a, Case_syn, 'a list] \<Rightarrow> Case_syn"
  "_cons"    :: "['a, 'a list] \<Rightarrow> 'a list"
  "_nil"     :: "'a list"

translations
  "_Case_syntax x (_match m)"     == "run\<cdot>(m\<cdot>x)"
  "_Case2 (_match c) (_match cs)" == "_match (c \<parallel> cs)"
  "_Case1 dummy_pattern r"        == "_match (wild_pat\<cdot>r)"
  "_as x (_match (p\<cdot>t))"          == "_match ((as_pat p)\<cdot>(\<Lambda> x. t))"
  "_Case1 (_as_pattern x e) r"    == "_as x (_Case1 e r)"
  "_Case1 x t"                    == "_match (var_pat\<cdot>(\<Lambda> x. t))"
  "_Case1 (f\<cdot>e) r" == "_matches f (_Case1 e r) _nil"
  "_matches (f\<cdot>e) (_match (p\<cdot>r)) ps" == "_matches f (_Case1 e r) (_cons p ps)"

lemma run_fatbar1: "m\<cdot>x = \<bottom> \<Longrightarrow> run\<cdot>((m \<parallel> ms)\<cdot>x) = \<bottom>"
by (simp add: fatbar_def)

lemma run_fatbar2: "m\<cdot>x = fail \<Longrightarrow> run\<cdot>((m \<parallel> ms)\<cdot>x) = run\<cdot>(ms\<cdot>x)"
by (simp add: fatbar_def)

lemma run_fatbar3: "m\<cdot>x = return\<cdot>y \<Longrightarrow> run\<cdot>((m \<parallel> ms)\<cdot>x) = y"
by (simp add: fatbar_def)

lemmas run_fatbar_simps [simp] = run_fatbar1 run_fatbar2 run_fatbar3

subsection {* Pattern combinators for built-in types *}

constdefs
  cpair_pat :: "_"
  "cpair_pat p1 p2 \<equiv> \<Lambda> r1 \<langle>x1,x2\<rangle>. bind\<cdot>(p1\<cdot>r1\<cdot>x1)\<cdot>(\<Lambda> r2. p2\<cdot>r2\<cdot>x2)"

  spair_pat :: "_"
  "spair_pat p1 p2 \<equiv> \<Lambda> r (:x,y:). cpair_pat p1 p2\<cdot>r\<cdot>\<langle>x,y\<rangle>"

  sinl_pat :: "_"
  "sinl_pat p \<equiv> \<Lambda> r a. case a of sinl\<cdot>x \<Rightarrow> p\<cdot>r\<cdot>x | sinr\<cdot>y \<Rightarrow> fail"

  sinr_pat :: "_"
  "sinr_pat p \<equiv> \<Lambda> r a. case a of sinl\<cdot>x \<Rightarrow> fail | sinr\<cdot>y \<Rightarrow> p\<cdot>r\<cdot>y"

  up_pat :: "_"
  "up_pat p \<equiv> \<Lambda> r a. case a of up\<cdot>x \<Rightarrow> p\<cdot>r\<cdot>x"

  Def_pat :: "'a::type \<Rightarrow> ('a lift, 'b, 'b) pattern"
  "Def_pat x \<equiv> \<Lambda> r. FLIFT y. if x = y then return\<cdot>r else fail"

  ONE_pat :: "_"
  "ONE_pat \<equiv> \<Lambda> r ONE. return\<cdot>r"

  TT_pat :: "(tr, _, _) pattern"
  "TT_pat \<equiv> \<Lambda> r b. If b then return\<cdot>r else fail fi"

  FF_pat :: "(tr, _, _) pattern"
  "FF_pat \<equiv> \<Lambda> r b. If b then fail else return\<cdot>r fi"

translations
  "_matches cpair (_match (p1\<cdot>r)) (_cons p2 _nil)"
    == "_match ((cpair_pat p1 p2)\<cdot>r)"

  "_matches spair (_match (p1\<cdot>r)) (_cons p2 _nil)"
    == "_match ((spair_pat p1 p2)\<cdot>r)"

translations
  "_matches sinl (_match (p1\<cdot>r)) _nil" == "_match ((sinl_pat p1)\<cdot>r)"
  "_matches sinr (_match (p1\<cdot>r)) _nil" == "_match ((sinr_pat p1)\<cdot>r)"
  "_matches up (_match (p1\<cdot>r)) _nil" == "_match ((up_pat p1)\<cdot>r)"

translations
  "_Case1 (Def x) r" == "_match (Def_pat x\<cdot>r)"
  "_Case1 ONE r" == "_match (ONE_pat\<cdot>r)"
  "_Case1 TT r" == "_match (TT_pat\<cdot>r)"
  "_Case1 FF r" == "_match (FF_pat\<cdot>r)"

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
