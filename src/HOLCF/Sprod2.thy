(*  Title:      HOLCF/Sprod2.thy
    ID:         $Id$
    Author:     Franz Regensburger
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Class Instance **::(pcpo,pcpo)po
*)

theory Sprod2 = Sprod1:

instance "**"::(pcpo,pcpo)po 
apply (intro_classes)
apply (rule refl_less_sprod)
apply (rule antisym_less_sprod, assumption+)
apply (rule trans_less_sprod, assumption+)
done

(*  Title:      HOLCF/Sprod2.ML
    ID:         $Id$
    Author:     Franz Regensburger
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Class Instance **::(pcpo,pcpo)po
*)

(* for compatibility with old HOLCF-Version *)
lemma inst_sprod_po: "(op <<)=(%x y. Isfst x<<Isfst y&Issnd x<<Issnd y)"
apply (fold less_sprod_def)
apply (rule refl)
done

(* ------------------------------------------------------------------------ *)
(* type sprod is pointed                                                    *)
(* ------------------------------------------------------------------------ *)

lemma minimal_sprod: "Ispair UU UU << p"
apply (simp add: inst_sprod_po minimal)
done

lemmas UU_sprod_def = minimal_sprod [THEN minimal2UU, symmetric, standard]

lemma least_sprod: "? x::'a**'b.!y. x<<y"
apply (rule_tac x = "Ispair UU UU" in exI)
apply (rule minimal_sprod [THEN allI])
done

(* ------------------------------------------------------------------------ *)
(* Ispair is monotone in both arguments                                     *)
(* ------------------------------------------------------------------------ *)

lemma monofun_Ispair1: "monofun(Ispair)"

apply (unfold monofun)
apply (intro strip)
apply (rule less_fun [THEN iffD2])
apply (intro strip)
apply (rule_tac Q = "xa=UU" in excluded_middle [THEN disjE])
apply (rule_tac Q = "x=UU" in excluded_middle [THEN disjE])
apply (frule notUU_I)
apply assumption
apply (simp_all add: Sprod0_ss inst_sprod_po refl_less minimal)
done

lemma monofun_Ispair2: "monofun(Ispair(x))"
apply (unfold monofun)
apply (intro strip)
apply (rule_tac Q = "x=UU" in excluded_middle [THEN disjE])
apply (rule_tac Q = "xa=UU" in excluded_middle [THEN disjE])
apply (frule notUU_I)
apply assumption
apply (simp_all add: Sprod0_ss inst_sprod_po refl_less minimal)
done

lemma monofun_Ispair: "[|x1<<x2; y1<<y2|] ==> Ispair x1 y1 << Ispair x2 y2"
apply (rule trans_less)
apply (rule monofun_Ispair1 [THEN monofunE, THEN spec, THEN spec, THEN mp, THEN less_fun [THEN iffD1, THEN spec]])
prefer 2 apply (rule monofun_Ispair2 [THEN monofunE, THEN spec, THEN spec, THEN mp])
apply assumption
apply assumption
done

(* ------------------------------------------------------------------------ *)
(* Isfst and Issnd are monotone                                             *)
(* ------------------------------------------------------------------------ *)

lemma monofun_Isfst: "monofun(Isfst)"

apply (unfold monofun)
apply (simp add: inst_sprod_po)
done

lemma monofun_Issnd: "monofun(Issnd)"
apply (unfold monofun)
apply (simp add: inst_sprod_po)
done

(* ------------------------------------------------------------------------ *)
(* the type 'a ** 'b is a cpo                                               *)
(* ------------------------------------------------------------------------ *)

lemma lub_sprod: 
"[|chain(S)|] ==> range(S) <<|  
  Ispair (lub(range(%i. Isfst(S i)))) (lub(range(%i. Issnd(S i))))"
apply (rule is_lubI)
apply (rule ub_rangeI)
apply (rule_tac t = "S (i) " in surjective_pairing_Sprod [THEN ssubst])
apply (rule monofun_Ispair)
apply (rule is_ub_thelub)
apply (erule monofun_Isfst [THEN ch2ch_monofun])
apply (rule is_ub_thelub)
apply (erule monofun_Issnd [THEN ch2ch_monofun])
apply (rule_tac t = "u" in surjective_pairing_Sprod [THEN ssubst])
apply (rule monofun_Ispair)
apply (rule is_lub_thelub)
apply (erule monofun_Isfst [THEN ch2ch_monofun])
apply (erule monofun_Isfst [THEN ub2ub_monofun])
apply (rule is_lub_thelub)
apply (erule monofun_Issnd [THEN ch2ch_monofun])
apply (erule monofun_Issnd [THEN ub2ub_monofun])
done

lemmas thelub_sprod = lub_sprod [THEN thelubI, standard]


lemma cpo_sprod: "chain(S::nat=>'a**'b)==>? x. range(S)<<| x"
apply (rule exI)
apply (erule lub_sprod)
done

end


