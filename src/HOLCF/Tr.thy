(*  Title:      HOLCF/Tr.thy
    ID:         $Id$
    Author:     Franz Regensburger

Introduce infix if_then_else_fi and boolean connectives andalso, orelse.
*)

header {* The type of lifted booleans *}

theory Tr
imports Lift Fix
begin

types
  tr = "bool lift"

translations
  "tr" <= (type) "bool lift" 

consts
	TT              :: "tr"
	FF              :: "tr"
        Icifte          :: "tr -> 'c -> 'c -> 'c"
        trand           :: "tr -> tr -> tr"
        tror            :: "tr -> tr -> tr"
        neg             :: "tr -> tr"
        If2             :: "tr=>'c=>'c=>'c"

syntax  "@cifte"        :: "tr=>'c=>'c=>'c" ("(3If _/ (then _/ else _) fi)" 60)
        "@andalso"      :: "tr => tr => tr" ("_ andalso _" [36,35] 35)
        "@orelse"       :: "tr => tr => tr" ("_ orelse _"  [31,30] 30)
 
translations 
	     "x andalso y" == "trand$x$y"
             "x orelse y"  == "tror$x$y"
             "If b then e1 else e2 fi" == "Icifte$b$e1$e2"
defs
  TT_def:      "TT==Def True"
  FF_def:      "FF==Def False"
  neg_def:     "neg == flift2 Not"
  ifte_def:    "Icifte == (LAM b t e. flift1(%b. if b then t else e)$b)"
  andalso_def: "trand == (LAM x y. If x then y else FF fi)"
  orelse_def:  "tror == (LAM x y. If x then TT else y fi)"
  If2_def:     "If2 Q x y == If Q then x else y fi"

text {* Exhaustion and Elimination for type @{typ tr} *}

lemma Exh_tr: "t=UU | t = TT | t = FF"
apply (unfold FF_def TT_def)
apply (induct_tac "t")
apply fast
apply fast
done

lemma trE: "[| p=UU ==> Q; p = TT ==>Q; p = FF ==>Q|] ==>Q"
apply (rule Exh_tr [THEN disjE])
apply fast
apply (erule disjE)
apply fast
apply fast
done

text {* tactic for tr-thms with case split *}

lemmas tr_defs = andalso_def orelse_def neg_def ifte_def TT_def FF_def
(*
fun prover t =  prove_goal thy t
 (fn prems =>
        [
        (res_inst_tac [("p","y")] trE 1),
	(REPEAT(asm_simp_tac (simpset() addsimps 
		[o_def,flift1_def,flift2_def,inst_lift_po]@tr_defs) 1))
	])
*)
text {* distinctness for type @{typ tr} *}

lemma dist_less_tr [simp]: "~TT << UU" "~FF << UU" "~TT << FF" "~FF << TT"
by (simp_all add: tr_defs)

lemma dist_eq_tr [simp]: "TT~=UU" "FF~=UU" "TT~=FF" "UU~=TT" "UU~=FF" "FF~=TT"
by (simp_all add: tr_defs)

text {* lemmas about andalso, orelse, neg and if *}

lemma ifte_simp:
  "If x then e1 else e2 fi =
    flift1 (%b. if b then e1 else e2)$x"
apply (unfold ifte_def TT_def FF_def flift1_def)
apply (simp add: cont_flift1_arg cont_if)
done

lemma ifte_thms [simp]:
  "If UU then e1 else e2 fi = UU"
  "If FF then e1 else e2 fi = e2"
  "If TT then e1 else e2 fi = e1"
by (simp_all add: ifte_simp TT_def FF_def)

lemma andalso_thms [simp]:
  "(TT andalso y) = y"
  "(FF andalso y) = FF"
  "(UU andalso y) = UU"
  "(y andalso TT) = y"
  "(y andalso y) = y"
apply (unfold andalso_def, simp_all)
apply (rule_tac p=y in trE, simp_all)
apply (rule_tac p=y in trE, simp_all)
done

lemma orelse_thms [simp]:
  "(TT orelse y) = TT"
  "(FF orelse y) = y"
  "(UU orelse y) = UU"
  "(y orelse FF) = y"
  "(y orelse y) = y"
apply (unfold orelse_def, simp_all)
apply (rule_tac p=y in trE, simp_all)
apply (rule_tac p=y in trE, simp_all)
done

lemma neg_thms [simp]:
  "neg$TT = FF"
  "neg$FF = TT"
  "neg$UU = UU"
by (simp_all add: neg_def TT_def FF_def)

text {* split-tac for If via If2 because the constant has to be a constant *}
  
lemma split_If2: 
  "P (If2 Q x y ) = ((Q=UU --> P UU) & (Q=TT --> P x) & (Q=FF --> P y))"  
apply (unfold If2_def)
apply (rule_tac p = "Q" in trE)
apply (simp_all)
done

ML {*
val split_If_tac =
  simp_tac (HOL_basic_ss addsimps [symmetric (thm "If2_def")])
    THEN' (split_tac [thm "split_If2"])
*}

subsection "Rewriting of HOLCF operations to HOL functions"

lemma andalso_or: 
"!!t.[|t~=UU|]==> ((t andalso s)=FF)=(t=FF | s=FF)"
apply (rule_tac p = "t" in trE)
apply simp_all
done

lemma andalso_and: "[|t~=UU|]==> ((t andalso s)~=FF)=(t~=FF & s~=FF)"
apply (rule_tac p = "t" in trE)
apply simp_all
done

lemma Def_bool1 [simp]: "(Def x ~= FF) = x"
by (simp add: FF_def)

lemma Def_bool2 [simp]: "(Def x = FF) = (~x)"
by (simp add: FF_def)

lemma Def_bool3 [simp]: "(Def x = TT) = x"
by (simp add: TT_def)

lemma Def_bool4 [simp]: "(Def x ~= TT) = (~x)"
by (simp add: TT_def)

lemma If_and_if: 
  "(If Def P then A else B fi)= (if P then A else B)"
apply (rule_tac p = "Def P" in trE)
apply (auto simp add: TT_def[symmetric] FF_def[symmetric])
done

subsection "admissibility"

text {*
   The following rewrite rules for admissibility should in the future be 
   replaced by a more general admissibility test that also checks 
   chain-finiteness, of which these lemmata are specific examples
*}

lemma adm_trick_1: "(x~=FF) = (x=TT|x=UU)"
apply (rule_tac p = "x" in trE)
apply (simp_all)
done

lemma adm_trick_2: "(x~=TT) = (x=FF|x=UU)"
apply (rule_tac p = "x" in trE)
apply (simp_all)
done

lemmas adm_tricks = adm_trick_1 adm_trick_2

lemma adm_nTT [simp]: "cont(f) ==> adm (%x. (f x)~=TT)"
by (simp add: adm_tricks)

lemma adm_nFF [simp]: "cont(f) ==> adm (%x. (f x)~=FF)"
by (simp add: adm_tricks)

end
