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

subsection {* Monadic bind operator *}

constdefs
  bind :: "'a maybe \<rightarrow> ('a \<rightarrow> 'b maybe) \<rightarrow> 'b maybe"
  "bind \<equiv> \<Lambda> m f. sscase\<cdot>sinl\<cdot>(fup\<cdot>f)\<cdot>m"

syntax
  "_bind" :: "'a maybe \<Rightarrow> ('a \<rightarrow> 'b maybe) \<Rightarrow> 'b maybe"
    ("(_ >>= _)" [50, 51] 50)

translations "m >>= k" == "bind\<cdot>m\<cdot>k"

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
 "(do a <- m; b <- k\<cdot>a; h\<cdot>b) = (do b <- (do a <- m; k\<cdot>a); h\<cdot>b)"
by (rule_tac p=m in maybeE, simp_all)

subsection {* Run operator *}

constdefs
  run:: "'a maybe \<rightarrow> 'a"
  "run \<equiv> sscase\<cdot>\<bottom>\<cdot>(fup\<cdot>ID)"

text {* rewrite rules for run *}

lemma run_strict [simp]: "run\<cdot>\<bottom> = \<bottom>"
by (simp add: run_def)

lemma run_fail [simp]: "run\<cdot>fail = \<bottom>"
by (simp add: run_def fail_def)

lemma run_return [simp]: "run\<cdot>(return\<cdot>x) = x"
by (simp add: run_def return_def)

subsection {* Monad plus operator *}

constdefs
  mplus :: "'a maybe \<rightarrow> 'a maybe \<rightarrow> 'a maybe"
  "mplus \<equiv> \<Lambda> m1 m2. sscase\<cdot>(\<Lambda> x. m2)\<cdot>(fup\<cdot>return)\<cdot>m1"

syntax "+++" :: "'a maybe \<Rightarrow> 'a maybe \<Rightarrow> 'a maybe" (infixr 65)
translations "x +++ y" == "mplus\<cdot>x\<cdot>y"

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

subsection {* Match functions for built-in types *}

constdefs
  match_cpair :: "'a \<times> 'b \<rightarrow> ('a \<times> 'b) maybe"
  "match_cpair \<equiv> csplit\<cdot>(\<Lambda> x y. return\<cdot><x,y>)"

  match_spair :: "'a \<otimes> 'b \<rightarrow> ('a \<times> 'b) maybe"
  "match_spair \<equiv> ssplit\<cdot>(\<Lambda> x y. return\<cdot><x,y>)"

  match_sinl :: "'a \<oplus> 'b \<rightarrow> 'a maybe"
  "match_sinl \<equiv> sscase\<cdot>return\<cdot>(\<Lambda> y. fail)"

  match_sinr :: "'a \<oplus> 'b \<rightarrow> 'b maybe"
  "match_sinr \<equiv> sscase\<cdot>(\<Lambda> x. fail)\<cdot>return"

  match_up :: "'a u \<rightarrow> 'a maybe"
  "match_up \<equiv> fup\<cdot>return"

  match_ONE :: "one \<rightarrow> unit maybe"
  "match_ONE \<equiv> flift1 (\<lambda>u. return\<cdot>())"

  match_TT :: "tr \<rightarrow> unit maybe"
  "match_TT \<equiv> flift1 (\<lambda>b. if b then return\<cdot>() else fail)"

  match_FF :: "tr \<rightarrow> unit maybe"
  "match_FF \<equiv> flift1 (\<lambda>b. if b then fail else return\<cdot>())"

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
by (simp_all add: ONE_def match_ONE_def)

lemma match_TT_simps [simp]:
  "match_TT\<cdot>TT = return\<cdot>()"
  "match_TT\<cdot>FF = fail"
  "match_TT\<cdot>\<bottom> = \<bottom>"
by (simp_all add: TT_def FF_def match_TT_def)

lemma match_FF_simps [simp]:
  "match_FF\<cdot>FF = return\<cdot>()"
  "match_FF\<cdot>TT = fail"
  "match_FF\<cdot>\<bottom> = \<bottom>"
by (simp_all add: TT_def FF_def match_FF_def)

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
