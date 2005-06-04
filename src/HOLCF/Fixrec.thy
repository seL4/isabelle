(*  Title:      HOLCF/Fixrec.thy
    ID:         $Id$
    Author:     Amber Telfer and Brian Huffman
*)

header "Package for defining recursive functions in HOLCF"

theory Fixrec
imports Ssum One Up Fix
files ("fixrec_package.ML")
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
apply (rule_tac p=y in upE1, simp, simp)
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

lemma mplus_assoc: "(x +++ y) +++ z = x +++ (y +++ z)"
by (rule_tac p=x in maybeE, simp_all)

subsection {* Match functions for built-in types *}

text {* Currently the package only supports lazy constructors *}

constdefs
  match_cpair :: "'a \<times> 'b \<rightarrow> ('a \<times> 'b) maybe"
  "match_cpair \<equiv> csplit\<cdot>(\<Lambda> x y. return\<cdot><x,y>)"

  match_up :: "'a u \<rightarrow> 'a maybe"
  "match_up \<equiv> fup\<cdot>return"

lemma match_cpair_simps [simp]:
  "match_cpair\<cdot><x,y> = return\<cdot><x,y>"
by (simp add: match_cpair_def)

lemma match_up_simps [simp]:
  "match_up\<cdot>(up\<cdot>x) = return\<cdot>x"
  "match_up\<cdot>\<bottom> = \<bottom>"
by (simp_all add: match_up_def)


subsection {* Intitializing the fixrec package *}

use "fixrec_package.ML"

end
