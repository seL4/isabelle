(*  Title:      HOLCF/Cprod1.thy
    ID:         $Id$
    Author:     Franz Regensburger
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Partial ordering for cartesian product of HOL theory prod.thy
*)

header {* The cpo of cartesian products *}

theory Cprod = Cfun:

defaultsort cpo

instance "*"::(sq_ord,sq_ord)sq_ord ..

defs (overloaded)

  less_cprod_def: "p1 << p2 == (fst p1<<fst p2 & snd p1 << snd p2)"

(* ------------------------------------------------------------------------ *)
(* less_cprod is a partial order on 'a * 'b                                 *)
(* ------------------------------------------------------------------------ *)

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

(* Class Instance *::(pcpo,pcpo)po *)

defaultsort pcpo

instance "*"::(cpo,cpo)po
apply (intro_classes)
apply (rule refl_less_cprod)
apply (rule antisym_less_cprod, assumption+)
apply (rule trans_less_cprod, assumption+)
done

(* for compatibility with old HOLCF-Version *)
lemma inst_cprod_po: "(op <<)=(%x y. fst x<<fst y & snd x<<snd y)"
apply (fold less_cprod_def)
apply (rule refl)
done

lemma less_cprod4c: "(x1,y1) << (x2,y2) ==> x1 << x2 & y1 << y2"
apply (simp add: inst_cprod_po)
done

(* ------------------------------------------------------------------------ *)
(* type cprod is pointed                                                    *)
(* ------------------------------------------------------------------------ *)

lemma minimal_cprod: "(UU,UU)<<p"
apply (simp (no_asm) add: inst_cprod_po)
done

lemmas UU_cprod_def = minimal_cprod [THEN minimal2UU, symmetric, standard]

lemma least_cprod: "EX x::'a*'b. ALL y. x<<y"
apply (rule_tac x = " (UU,UU) " in exI)
apply (rule minimal_cprod [THEN allI])
done

(* ------------------------------------------------------------------------ *)
(* Pair <_,_>  is monotone in both arguments                                *)
(* ------------------------------------------------------------------------ *)

lemma monofun_pair1: "monofun Pair"

apply (unfold monofun)
apply (intro strip)
apply (rule less_fun [THEN iffD2])
apply (intro strip)
apply (simp (no_asm_simp) add: inst_cprod_po)
done

lemma monofun_pair2: "monofun(Pair x)"
apply (unfold monofun)
apply (simp (no_asm_simp) add: inst_cprod_po)
done

lemma monofun_pair: "[|x1<<x2; y1<<y2|] ==> (x1::'a::cpo,y1::'b::cpo)<<(x2,y2)"
apply (rule trans_less)
apply (erule monofun_pair1 [THEN monofunE, THEN spec, THEN spec, THEN mp, THEN less_fun [THEN iffD1, THEN spec]])
apply (erule monofun_pair2 [THEN monofunE, THEN spec, THEN spec, THEN mp])
done

(* ------------------------------------------------------------------------ *)
(* fst and snd are monotone                                                 *)
(* ------------------------------------------------------------------------ *)

lemma monofun_fst: "monofun fst"
apply (unfold monofun)
apply (intro strip)
apply (rule_tac p = "x" in PairE)
apply (rule_tac p = "y" in PairE)
apply simp
apply (erule less_cprod4c [THEN conjunct1])
done

lemma monofun_snd: "monofun snd"
apply (unfold monofun)
apply (intro strip)
apply (rule_tac p = "x" in PairE)
apply (rule_tac p = "y" in PairE)
apply simp
apply (erule less_cprod4c [THEN conjunct2])
done

(* ------------------------------------------------------------------------ *)
(* the type 'a * 'b is a cpo                                                *)
(* ------------------------------------------------------------------------ *)

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
apply (rule exI)
apply (erule lub_cprod)
done

(* Class instance of * for class pcpo and cpo. *)

instance "*" :: (cpo,cpo)cpo
by (intro_classes, rule cpo_cprod)

instance "*" :: (pcpo,pcpo)pcpo
by (intro_classes, rule least_cprod)

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



(* introduce syntax for

   Let <x,y> = e1; z = E2 in E3

   and

   LAM <x,y,z>.e
*)

constdefs
  CLet           :: "'a -> ('a -> 'b) -> 'b"
  "CLet == LAM s f. f$s"


(* syntax for Let *)

nonterminals
  Cletbinds  Cletbind

syntax
  "_Cbind"  :: "[pttrn, 'a] => Cletbind"             ("(2_ =/ _)" 10)
  ""        :: "Cletbind => Cletbinds"               ("_")
  "_Cbinds" :: "[Cletbind, Cletbinds] => Cletbinds"  ("_;/ _")
  "_CLet"   :: "[Cletbinds, 'a] => 'a"               ("(Let (_)/ in (_))" 10)

translations
  "_CLet (_Cbinds b bs) e"  == "_CLet b (_CLet bs e)"
  "Let x = a in e"          == "CLet$a$(LAM x. e)"


(* syntax for LAM <x,y,z>.e *)

syntax
  "_LAM"    :: "[patterns, 'a => 'b] => ('a -> 'b)"  ("(3LAM <_>./ _)" [0, 10] 10)

translations
  "LAM <x,y,zs>.b"        == "csplit$(LAM x. LAM <y,zs>.b)"
  "LAM <x,y>. LAM zs. b"  <= "csplit$(LAM x y zs. b)"
  "LAM <x,y>.b"           == "csplit$(LAM x y. b)"

syntax (xsymbols)
  "_LAM"    :: "[patterns, 'a => 'b] => ('a -> 'b)"  ("(3\\<Lambda>()<_>./ _)" [0, 10] 10)

(* for compatibility with old HOLCF-Version *)
lemma inst_cprod_pcpo: "UU = (UU,UU)"
apply (simp add: UU_cprod_def[folded UU_def])
done

(* ------------------------------------------------------------------------ *)
(* continuity of (_,_) , fst, snd                                           *)
(* ------------------------------------------------------------------------ *)

lemma Cprod3_lemma1: 
"chain(Y::(nat=>'a::cpo)) ==> 
  (lub(range(Y)),(x::'b::cpo)) = 
  (lub(range(%i. fst(Y i,x))),lub(range(%i. snd(Y i,x))))"
apply (rule_tac f1 = "Pair" in arg_cong [THEN cong])
apply (rule lub_equal)
apply assumption
apply (rule monofun_fst [THEN ch2ch_monofun])
apply (rule ch2ch_fun)
apply (rule monofun_pair1 [THEN ch2ch_monofun])
apply assumption
apply (rule allI)
apply (simp (no_asm))
apply (rule sym)
apply (simp (no_asm))
apply (rule lub_const [THEN thelubI])
done

lemma contlub_pair1: "contlub(Pair)"
apply (rule contlubI)
apply (intro strip)
apply (rule expand_fun_eq [THEN iffD2])
apply (intro strip)
apply (subst lub_fun [THEN thelubI])
apply (erule monofun_pair1 [THEN ch2ch_monofun])
apply (rule trans)
apply (rule_tac [2] thelub_cprod [symmetric])
apply (rule_tac [2] ch2ch_fun)
apply (erule_tac [2] monofun_pair1 [THEN ch2ch_monofun])
apply (erule Cprod3_lemma1)
done

lemma Cprod3_lemma2: 
"chain(Y::(nat=>'a::cpo)) ==> 
  ((x::'b::cpo),lub(range Y)) = 
  (lub(range(%i. fst(x,Y i))),lub(range(%i. snd(x, Y i))))"
apply (rule_tac f1 = "Pair" in arg_cong [THEN cong])
apply (rule sym)
apply (simp (no_asm))
apply (rule lub_const [THEN thelubI])
apply (rule lub_equal)
apply assumption
apply (rule monofun_snd [THEN ch2ch_monofun])
apply (rule monofun_pair2 [THEN ch2ch_monofun])
apply assumption
apply (rule allI)
apply (simp (no_asm))
done

lemma contlub_pair2: "contlub(Pair(x))"
apply (rule contlubI)
apply (intro strip)
apply (rule trans)
apply (rule_tac [2] thelub_cprod [symmetric])
apply (erule_tac [2] monofun_pair2 [THEN ch2ch_monofun])
apply (erule Cprod3_lemma2)
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
apply (rule contlubI)
apply (intro strip)
apply (subst lub_cprod [THEN thelubI])
apply assumption
apply (simp (no_asm))
done

lemma contlub_snd: "contlub(snd)"
apply (rule contlubI)
apply (intro strip)
apply (subst lub_cprod [THEN thelubI])
apply assumption
apply (simp (no_asm))
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

(* 
 -------------------------------------------------------------------------- 
 more lemmas for Cprod3.thy 
 
 -------------------------------------------------------------------------- 
*)

(* ------------------------------------------------------------------------ *)
(* convert all lemmas to the continuous versions                            *)
(* ------------------------------------------------------------------------ *)

lemma beta_cfun_cprod: 
        "(LAM x y.(x,y))$a$b = (a,b)"
apply (subst beta_cfun)
apply (simp (no_asm) add: cont_pair1 cont_pair2 cont2cont_CF1L)
apply (subst beta_cfun)
apply (rule cont_pair2)
apply (rule refl)
done

lemma inject_cpair: 
        "<a,b> = <aa,ba>  ==> a=aa & b=ba"
apply (unfold cpair_def)
apply (drule beta_cfun_cprod [THEN subst])
apply (drule beta_cfun_cprod [THEN subst])
apply (erule Pair_inject)
apply fast
done

lemma inst_cprod_pcpo2: "UU = <UU,UU>"
apply (unfold cpair_def)
apply (rule sym)
apply (rule trans)
apply (rule beta_cfun_cprod)
apply (rule sym)
apply (rule inst_cprod_pcpo)
done

lemma defined_cpair_rev: 
 "<a,b> = UU ==> a = UU & b = UU"
apply (drule inst_cprod_pcpo2 [THEN subst])
apply (erule inject_cpair)
done

lemma Exh_Cprod2:
        "? a b. z=<a,b>"
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
apply (unfold cpair_def)
apply (erule beta_cfun_cprod [THEN ssubst])
done

lemma cfst2: 
        "cfst$<x,y> = x"
apply (unfold cfst_def cpair_def)
apply (subst beta_cfun_cprod)
apply (subst beta_cfun)
apply (rule cont_fst)
apply (simp (no_asm))
done

lemma csnd2: 
        "csnd$<x,y> = y"
apply (unfold csnd_def cpair_def)
apply (subst beta_cfun_cprod)
apply (subst beta_cfun)
apply (rule cont_snd)
apply (simp (no_asm))
done

lemma cfst_strict: "cfst$UU = UU"
apply (simp add: inst_cprod_pcpo2 cfst2)
done

lemma csnd_strict: "csnd$UU = UU"
apply (simp add: inst_cprod_pcpo2 csnd2)
done

lemma surjective_pairing_Cprod2: "<cfst$p , csnd$p> = p"
apply (unfold cfst_def csnd_def cpair_def)
apply (subst beta_cfun_cprod)
apply (simplesubst beta_cfun)
apply (rule cont_snd)
apply (subst beta_cfun)
apply (rule cont_fst)
apply (rule surjective_pairing [symmetric])
done

lemma less_cprod5c: 
 "<xa,ya> << <x,y> ==> xa<<x & ya << y"
apply (unfold cfst_def csnd_def cpair_def)
apply (rule less_cprod4c)
apply (drule beta_cfun_cprod [THEN subst])
apply (drule beta_cfun_cprod [THEN subst])
apply assumption
done

lemma lub_cprod2: 
"[|chain(S)|] ==> range(S) <<|  
  <(lub(range(%i. cfst$(S i)))) , lub(range(%i. csnd$(S i)))>"
apply (unfold cfst_def csnd_def cpair_def)
apply (subst beta_cfun_cprod)
apply (simplesubst beta_cfun [THEN ext])
apply (rule cont_snd)
apply (subst beta_cfun [THEN ext])
apply (rule cont_fst)
apply (rule lub_cprod)
apply assumption
done

lemmas thelub_cprod2 = lub_cprod2 [THEN thelubI, standard]
(*
chain ?S1 ==>
 lub (range ?S1) =
 <lub (range (%i. cfst$(?S1 i))), lub (range (%i. csnd$(?S1 i)))>" 
*)
lemma csplit2: 
        "csplit$f$<x,y> = f$x$y"
apply (unfold csplit_def)
apply (subst beta_cfun)
apply (simp (no_asm))
apply (simp (no_asm) add: cfst2 csnd2)
done

lemma csplit3: 
  "csplit$cpair$z=z"
apply (unfold csplit_def)
apply (subst beta_cfun)
apply (simp (no_asm))
apply (simp (no_asm) add: surjective_pairing_Cprod2)
done

(* ------------------------------------------------------------------------ *)
(* install simplifier for Cprod                                             *)
(* ------------------------------------------------------------------------ *)

declare cfst2 [simp] csnd2 [simp] csplit2 [simp]

lemmas Cprod_rews = cfst2 csnd2 csplit2

end
