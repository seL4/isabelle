(*  Title:      HOLCF/Cprod.thy
    ID:         $Id$
    Author:     Franz Regensburger
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Partial ordering for cartesian product of HOL theory prod.thy
*)

header {* The cpo of cartesian products *}

theory Cprod
imports Cfun
begin

defaultsort cpo

subsection {* Type @{typ unit} is a pcpo *}

instance unit :: sq_ord ..

defs (overloaded)
  less_unit_def [simp]: "x \<sqsubseteq> (y::unit) \<equiv> True"

instance unit :: po
by intro_classes simp_all

instance unit :: cpo
by intro_classes (simp add: is_lub_def is_ub_def)

instance unit :: pcpo
by intro_classes simp


subsection {* Ordering on @{typ "'a * 'b"} *}

instance "*" :: (sq_ord, sq_ord) sq_ord ..

defs (overloaded)
  less_cprod_def: "p1 << p2 == (fst p1<<fst p2 & snd p1 << snd p2)"

subsection {* Type @{typ "'a * 'b"} is a partial order *}

lemma refl_less_cprod: "(p::'a*'b) << p"
apply (unfold less_cprod_def)
apply simp
done

lemma antisym_less_cprod: "[|(p1::'a * 'b) << p2;p2 << p1|] ==> p1=p2"
apply (unfold less_cprod_def)
apply (rule injective_fst_snd)
apply (fast intro: antisym_less)
apply (fast intro: antisym_less)
done

lemma trans_less_cprod: 
        "[|(p1::'a*'b) << p2;p2 << p3|] ==> p1 << p3"
apply (unfold less_cprod_def)
apply (rule conjI)
apply (fast intro: trans_less)
apply (fast intro: trans_less)
done

defaultsort pcpo

instance "*" :: (cpo, cpo) po
by intro_classes
  (assumption | rule refl_less_cprod antisym_less_cprod trans_less_cprod)+

text {* for compatibility with old HOLCF-Version *}
lemma inst_cprod_po: "(op <<)=(%x y. fst x<<fst y & snd x<<snd y)"
apply (fold less_cprod_def)
apply (rule refl)
done

lemma less_cprod4c: "(x1,y1) << (x2,y2) ==> x1 << x2 & y1 << y2"
apply (simp add: inst_cprod_po)
done

subsection {* Monotonicity of @{text "(_,_)"}, @{term fst}, @{term snd} *}

text {* Pair @{text "(_,_)"}  is monotone in both arguments *}

lemma monofun_pair1: "monofun Pair"
by (simp add: monofun less_fun inst_cprod_po)

lemma monofun_pair2: "monofun(Pair x)"
by (simp add: monofun inst_cprod_po)

lemma monofun_pair: "[|x1<<x2; y1<<y2|] ==> (x1::'a::cpo,y1::'b::cpo)<<(x2,y2)"
by (simp add: inst_cprod_po)

text {* @{term fst} and @{term snd} are monotone *}

lemma monofun_fst: "monofun fst"
by (simp add: monofun inst_cprod_po)

lemma monofun_snd: "monofun snd"
by (simp add: monofun inst_cprod_po)

subsection {* Type @{typ "'a * 'b"} is a cpo *}

lemma lub_cprod: 
"chain S ==> range S<<|(lub(range(%i. fst(S i))),lub(range(%i. snd(S i))))"
apply (rule is_lubI)
apply (rule ub_rangeI)
apply (rule_tac t = "S i" in surjective_pairing [THEN ssubst])
apply (rule monofun_pair)
apply (rule is_ub_thelub)
apply (erule monofun_fst [THEN ch2ch_monofun])
apply (rule is_ub_thelub)
apply (erule monofun_snd [THEN ch2ch_monofun])
apply (rule_tac t = "u" in surjective_pairing [THEN ssubst])
apply (rule monofun_pair)
apply (rule is_lub_thelub)
apply (erule monofun_fst [THEN ch2ch_monofun])
apply (erule monofun_fst [THEN ub2ub_monofun])
apply (rule is_lub_thelub)
apply (erule monofun_snd [THEN ch2ch_monofun])
apply (erule monofun_snd [THEN ub2ub_monofun])
done

lemmas thelub_cprod = lub_cprod [THEN thelubI, standard]
(*
"chain ?S1 ==>
 lub (range ?S1) =
 (lub (range (%i. fst (?S1 i))), lub (range (%i. snd (?S1 i))))" : thm

*)

lemma cpo_cprod: "chain(S::nat=>'a::cpo*'b::cpo)==>EX x. range S<<| x"
by (rule exI, erule lub_cprod)

instance "*" :: (cpo, cpo) cpo
by intro_classes (rule cpo_cprod)

subsection {* Type @{typ "'a * 'b"} is pointed *}

lemma minimal_cprod: "(UU,UU)<<p"
by (simp add: inst_cprod_po)

lemmas UU_cprod_def = minimal_cprod [THEN minimal2UU, symmetric, standard]

lemma least_cprod: "EX x::'a*'b. ALL y. x<<y"
apply (rule_tac x = " (UU,UU) " in exI)
apply (rule minimal_cprod [THEN allI])
done

instance "*" :: (pcpo, pcpo) pcpo
by intro_classes (rule least_cprod)

text {* for compatibility with old HOLCF-Version *}
lemma inst_cprod_pcpo: "UU = (UU,UU)"
apply (simp add: UU_cprod_def[folded UU_def])
done

subsection {* Continuity of @{text "(_,_)"}, @{term fst}, @{term snd} *}

lemma contlub_pair1: "contlub(Pair)"
apply (rule contlubI [rule_format])
apply (rule ext)
apply (subst lub_fun [THEN thelubI])
apply (erule monofun_pair1 [THEN ch2ch_monofun])
apply (subst thelub_cprod)
apply (rule ch2ch_fun)
apply (erule monofun_pair1 [THEN ch2ch_monofun])
apply (simp add: lub_const [THEN thelubI])
done

lemma contlub_pair2: "contlub(Pair(x))"
apply (rule contlubI [rule_format])
apply (subst thelub_cprod)
apply (erule monofun_pair2 [THEN ch2ch_monofun])
apply (simp add: lub_const [THEN thelubI])
done

lemma cont_pair1: "cont(Pair)"
apply (rule monocontlub2cont)
apply (rule monofun_pair1)
apply (rule contlub_pair1)
done

lemma cont_pair2: "cont(Pair(x))"
apply (rule monocontlub2cont)
apply (rule monofun_pair2)
apply (rule contlub_pair2)
done

lemma contlub_fst: "contlub(fst)"
apply (rule contlubI [rule_format])
apply (simp add: lub_cprod [THEN thelubI])
done

lemma contlub_snd: "contlub(snd)"
apply (rule contlubI [rule_format])
apply (simp add: lub_cprod [THEN thelubI])
done

lemma cont_fst: "cont(fst)"
apply (rule monocontlub2cont)
apply (rule monofun_fst)
apply (rule contlub_fst)
done

lemma cont_snd: "cont(snd)"
apply (rule monocontlub2cont)
apply (rule monofun_snd)
apply (rule contlub_snd)
done

subsection {* Continuous versions of constants *}

consts
        cpair        :: "'a::cpo -> 'b::cpo -> ('a*'b)" (* continuous pairing *)
        cfst         :: "('a::cpo*'b::cpo)->'a"
        csnd         :: "('a::cpo*'b::cpo)->'b"
        csplit       :: "('a::cpo->'b::cpo->'c::cpo)->('a*'b)->'c"

syntax
        "@ctuple"    :: "['a, args] => 'a * 'b"         ("(1<_,/ _>)")

translations
        "<x, y, z>"   == "<x, <y, z>>"
        "<x, y>"      == "cpair$x$y"

defs
cpair_def:       "cpair  == (LAM x y.(x,y))"
cfst_def:        "cfst   == (LAM p. fst(p))"
csnd_def:        "csnd   == (LAM p. snd(p))"      
csplit_def:      "csplit == (LAM f p. f$(cfst$p)$(csnd$p))"

subsection {* Syntax *}

text {* syntax for @{text "LAM <x,y,z>.e"} *}

syntax
  "_LAM"    :: "[patterns, 'a => 'b] => ('a -> 'b)"  ("(3LAM <_>./ _)" [0, 10] 10)

translations
  "LAM <x,y,zs>.b"        == "csplit$(LAM x. LAM <y,zs>.b)"
  "LAM <x,y>. LAM zs. b"  <= "csplit$(LAM x y zs. b)"
  "LAM <x,y>.b"           == "csplit$(LAM x y. b)"

syntax (xsymbols)
  "_LAM"    :: "[patterns, 'a => 'b] => ('a -> 'b)"  ("(3\<Lambda>()<_>./ _)" [0, 10] 10)

text {* syntax for Let *}

constdefs
  CLet           :: "'a::cpo -> ('a -> 'b::cpo) -> 'b"
  "CLet == LAM s f. f$s"

nonterminals
  Cletbinds  Cletbind

syntax
  "_Cbind"  :: "[pttrn, 'a] => Cletbind"             ("(2_ =/ _)" 10)
  "_Cbindp" :: "[patterns, 'a] => Cletbind"          ("(2<_> =/ _)" 10)
  ""        :: "Cletbind => Cletbinds"               ("_")
  "_Cbinds" :: "[Cletbind, Cletbinds] => Cletbinds"  ("_;/ _")
  "_CLet"   :: "[Cletbinds, 'a] => 'a"               ("(Let (_)/ in (_))" 10)

translations
  "_CLet (_Cbinds b bs) e"  == "_CLet b (_CLet bs e)"
  "Let x = a in LAM ys. e"  == "CLet$a$(LAM x ys. e)"
  "Let x = a in e"          == "CLet$a$(LAM x. e)"
  "Let <xs> = a in e"       == "CLet$a$(LAM <xs>. e)"

subsection {* Convert all lemmas to the continuous versions *}

lemma beta_cfun_cprod: 
        "(LAM x y.(x,y))$a$b = (a,b)"
apply (subst beta_cfun)
apply (simp add: cont_pair1 cont_pair2 cont2cont_CF1L)
apply (subst beta_cfun)
apply (rule cont_pair2)
apply (rule refl)
done

lemma inject_cpair: 
        "<a,b> = <aa,ba>  ==> a=aa & b=ba"
by (simp add: cpair_def beta_cfun_cprod)

lemma inst_cprod_pcpo2: "UU = <UU,UU>"
by (simp add: cpair_def beta_cfun_cprod inst_cprod_pcpo)

lemma defined_cpair_rev: 
 "<a,b> = UU ==> a = UU & b = UU"
apply (drule inst_cprod_pcpo2 [THEN subst])
apply (erule inject_cpair)
done

lemma Exh_Cprod2: "? a b. z=<a,b>"
apply (unfold cpair_def)
apply (rule PairE)
apply (rule exI)
apply (rule exI)
apply (erule beta_cfun_cprod [THEN ssubst])
done

lemma cprodE:
assumes prems: "!!x y. [| p = <x,y> |] ==> Q"
shows "Q"
apply (rule PairE)
apply (rule prems)
apply (simp add: cpair_def beta_cfun_cprod)
done

lemma cfst2 [simp]: "cfst$<x,y> = x"
by (simp add: cpair_def cfst_def beta_cfun_cprod cont_fst)

lemma csnd2 [simp]: "csnd$<x,y> = y"
by (simp add: cpair_def csnd_def beta_cfun_cprod cont_snd)

lemma cfst_strict: "cfst$UU = UU"
by (simp add: inst_cprod_pcpo2)

lemma csnd_strict: "csnd$UU = UU"
by (simp add: inst_cprod_pcpo2)

lemma surjective_pairing_Cprod2: "<cfst$p, csnd$p> = p"
apply (unfold cfst_def csnd_def cpair_def)
apply (simp add: cont_fst cont_snd beta_cfun_cprod)
done

lemma less_cprod5c: 
 "<xa,ya> << <x,y> ==> xa<<x & ya << y"
by (simp add: cpair_def beta_cfun_cprod inst_cprod_po)

lemma lub_cprod2: 
"[|chain(S)|] ==> range(S) <<|  
  <(lub(range(%i. cfst$(S i)))) , lub(range(%i. csnd$(S i)))>"
apply (simp add: cpair_def beta_cfun_cprod)
apply (simp add: cfst_def csnd_def cont_fst cont_snd)
apply (erule lub_cprod)
done

lemmas thelub_cprod2 = lub_cprod2 [THEN thelubI, standard]
(*
chain ?S1 ==>
 lub (range ?S1) =
 <lub (range (%i. cfst$(?S1 i))), lub (range (%i. csnd$(?S1 i)))>" 
*)

lemma csplit2 [simp]: "csplit$f$<x,y> = f$x$y"
by (simp add: csplit_def)

lemma csplit3: "csplit$cpair$z=z"
by (simp add: csplit_def surjective_pairing_Cprod2)

lemmas Cprod_rews = cfst2 csnd2 csplit2

end
