(*  Title:      HOLCF/sprod3.thy
    ID:         $Id$
    Author:     Franz Regensburger
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Class instance of  ** for class pcpo
*)

theory Sprod3 = Sprod2:

instance "**" :: (pcpo,pcpo)pcpo
apply (intro_classes)
apply (erule cpo_sprod)
apply (rule least_sprod)
done

consts  
  spair		:: "'a -> 'b -> ('a**'b)" (* continuous strict pairing *)
  sfst		:: "('a**'b)->'a"
  ssnd		:: "('a**'b)->'b"
  ssplit	:: "('a->'b->'c)->('a**'b)->'c"

syntax  
  "@stuple"	:: "['a, args] => 'a ** 'b"	("(1'(:_,/ _:'))")

translations
        "(:x, y, z:)"   == "(:x, (:y, z:):)"
        "(:x, y:)"      == "spair$x$y"

defs
spair_def:       "spair  == (LAM x y. Ispair x y)"
sfst_def:        "sfst   == (LAM p. Isfst p)"
ssnd_def:        "ssnd   == (LAM p. Issnd p)"     
ssplit_def:      "ssplit == (LAM f. strictify$(LAM p. f$(sfst$p)$(ssnd$p)))"

(*  Title:      HOLCF/Sprod3
    ID:         $Id$
    Author:     Franz Regensburger
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Class instance of  ** for class pcpo
*)

(* for compatibility with old HOLCF-Version *)
lemma inst_sprod_pcpo: "UU = Ispair UU UU"
apply (simp add: UU_def UU_sprod_def)
done

declare inst_sprod_pcpo [symmetric, simp]

(* ------------------------------------------------------------------------ *)
(* continuity of Ispair, Isfst, Issnd                                       *)
(* ------------------------------------------------------------------------ *)

lemma sprod3_lemma1: 
"[| chain(Y);  x~= UU;  lub(range(Y))~= UU |] ==> 
  Ispair (lub(range Y)) x = 
  Ispair (lub(range(%i. Isfst(Ispair(Y i) x))))  
         (lub(range(%i. Issnd(Ispair(Y i) x))))"
apply (rule_tac f1 = "Ispair" in arg_cong [THEN cong])
apply (rule lub_equal)
apply assumption
apply (rule monofun_Isfst [THEN ch2ch_monofun])
apply (rule ch2ch_fun)
apply (rule monofun_Ispair1 [THEN ch2ch_monofun])
apply assumption
apply (rule allI)
apply (simp (no_asm_simp))
apply (rule sym)
apply (drule chain_UU_I_inverse2)
apply (erule exE)
apply (rule lub_chain_maxelem)
apply (erule Issnd2)
apply (rule allI)
apply (rename_tac "j")
apply (case_tac "Y (j) =UU")
apply auto
done

lemma sprod3_lemma2: 
"[| chain(Y); x ~= UU; lub(range(Y)) = UU |] ==> 
    Ispair (lub(range Y)) x = 
    Ispair (lub(range(%i. Isfst(Ispair(Y i) x)))) 
           (lub(range(%i. Issnd(Ispair(Y i) x))))"
apply (rule_tac s = "UU" and t = "lub (range (Y))" in ssubst)
apply assumption
apply (rule trans)
apply (rule strict_Ispair1)
apply (rule strict_Ispair [symmetric])
apply (rule disjI1)
apply (rule chain_UU_I_inverse)
apply auto
apply (erule chain_UU_I [THEN spec])
apply assumption
done


lemma sprod3_lemma3: 
"[| chain(Y); x = UU |] ==> 
           Ispair (lub(range Y)) x = 
           Ispair (lub(range(%i. Isfst(Ispair (Y i) x)))) 
                  (lub(range(%i. Issnd(Ispair (Y i) x))))"
apply (erule ssubst)
apply (rule trans)
apply (rule strict_Ispair2)
apply (rule strict_Ispair [symmetric])
apply (rule disjI1)
apply (rule chain_UU_I_inverse)
apply (rule allI)
apply (simp add: Sprod0_ss)
done

lemma contlub_Ispair1: "contlub(Ispair)"
apply (rule contlubI)
apply (intro strip)
apply (rule expand_fun_eq [THEN iffD2])
apply (intro strip)
apply (subst lub_fun [THEN thelubI])
apply (erule monofun_Ispair1 [THEN ch2ch_monofun])
apply (rule trans)
apply (rule_tac [2] thelub_sprod [symmetric])
apply (rule_tac [2] ch2ch_fun)
apply (erule_tac [2] monofun_Ispair1 [THEN ch2ch_monofun])
apply (rule_tac Q = "x=UU" in excluded_middle [THEN disjE])
apply (rule_tac Q = "lub (range (Y))=UU" in excluded_middle [THEN disjE])
apply (erule sprod3_lemma1)
apply assumption
apply assumption
apply (erule sprod3_lemma2)
apply assumption
apply assumption
apply (erule sprod3_lemma3)
apply assumption
done

lemma sprod3_lemma4: 
"[| chain(Y); x ~= UU; lub(range(Y)) ~= UU |] ==> 
          Ispair x (lub(range Y)) = 
          Ispair (lub(range(%i. Isfst (Ispair x (Y i))))) 
                 (lub(range(%i. Issnd (Ispair x (Y i)))))"
apply (rule_tac f1 = "Ispair" in arg_cong [THEN cong])
apply (rule sym)
apply (drule chain_UU_I_inverse2)
apply (erule exE)
apply (rule lub_chain_maxelem)
apply (erule Isfst2)
apply (rule allI)
apply (rename_tac "j")
apply (case_tac "Y (j) =UU")
apply auto
done

lemma sprod3_lemma5: 
"[| chain(Y); x ~= UU; lub(range(Y)) = UU |] ==> 
          Ispair x (lub(range Y)) = 
          Ispair (lub(range(%i. Isfst(Ispair x (Y i))))) 
                 (lub(range(%i. Issnd(Ispair x (Y i)))))"
apply (rule_tac s = "UU" and t = "lub (range (Y))" in ssubst)
apply assumption
apply (rule trans)
apply (rule strict_Ispair2)
apply (rule strict_Ispair [symmetric])
apply (rule disjI2)
apply (rule chain_UU_I_inverse)
apply (rule allI)
apply (simp add: Sprod0_ss)
apply (erule chain_UU_I [THEN spec])
apply assumption
done

lemma sprod3_lemma6: 
"[| chain(Y); x = UU |] ==> 
          Ispair x (lub(range Y)) = 
          Ispair (lub(range(%i. Isfst (Ispair x (Y i))))) 
                 (lub(range(%i. Issnd (Ispair x (Y i)))))"
apply (rule_tac s = "UU" and t = "x" in ssubst)
apply assumption
apply (rule trans)
apply (rule strict_Ispair1)
apply (rule strict_Ispair [symmetric])
apply (rule disjI1)
apply (rule chain_UU_I_inverse)
apply (rule allI)
apply (simp add: Sprod0_ss)
done

lemma contlub_Ispair2: "contlub(Ispair(x))"
apply (rule contlubI)
apply (intro strip)
apply (rule trans)
apply (rule_tac [2] thelub_sprod [symmetric])
apply (erule_tac [2] monofun_Ispair2 [THEN ch2ch_monofun])
apply (rule_tac Q = "x=UU" in excluded_middle [THEN disjE])
apply (rule_tac Q = "lub (range (Y))=UU" in excluded_middle [THEN disjE])
apply (erule sprod3_lemma4)
apply assumption
apply assumption
apply (erule sprod3_lemma5)
apply assumption
apply assumption
apply (erule sprod3_lemma6)
apply assumption
done

lemma cont_Ispair1: "cont(Ispair)"
apply (rule monocontlub2cont)
apply (rule monofun_Ispair1)
apply (rule contlub_Ispair1)
done


lemma cont_Ispair2: "cont(Ispair(x))"
apply (rule monocontlub2cont)
apply (rule monofun_Ispair2)
apply (rule contlub_Ispair2)
done

lemma contlub_Isfst: "contlub(Isfst)"
apply (rule contlubI)
apply (intro strip)
apply (subst lub_sprod [THEN thelubI])
apply assumption
apply (rule_tac Q = "lub (range (%i. Issnd (Y (i))))=UU" in excluded_middle [THEN disjE])
apply (simp add: Sprod0_ss)
apply (rule_tac s = "UU" and t = "lub (range (%i. Issnd (Y (i))))" in ssubst)
apply assumption
apply (rule trans)
apply (simp add: Sprod0_ss)
apply (rule sym)
apply (rule chain_UU_I_inverse)
apply (rule allI)
apply (rule strict_Isfst)
apply (rule contrapos_np)
apply (erule_tac [2] defined_IsfstIssnd [THEN conjunct2])
apply (fast dest!: monofun_Issnd [THEN ch2ch_monofun, THEN chain_UU_I, THEN spec])
done

lemma contlub_Issnd: "contlub(Issnd)"
apply (rule contlubI)
apply (intro strip)
apply (subst lub_sprod [THEN thelubI])
apply assumption
apply (rule_tac Q = "lub (range (%i. Isfst (Y (i))))=UU" in excluded_middle [THEN disjE])
apply (simp add: Sprod0_ss)
apply (rule_tac s = "UU" and t = "lub (range (%i. Isfst (Y (i))))" in ssubst)
apply assumption
apply (simp add: Sprod0_ss)
apply (rule sym)
apply (rule chain_UU_I_inverse)
apply (rule allI)
apply (rule strict_Issnd)
apply (rule contrapos_np)
apply (erule_tac [2] defined_IsfstIssnd [THEN conjunct1])
apply (fast dest!: monofun_Isfst [THEN ch2ch_monofun, THEN chain_UU_I, THEN spec])
done

lemma cont_Isfst: "cont(Isfst)"
apply (rule monocontlub2cont)
apply (rule monofun_Isfst)
apply (rule contlub_Isfst)
done

lemma cont_Issnd: "cont(Issnd)"
apply (rule monocontlub2cont)
apply (rule monofun_Issnd)
apply (rule contlub_Issnd)
done

lemma spair_eq: "[|x1=x2;y1=y2|] ==> (:x1,y1:) = (:x2,y2:)"
apply fast
done

(* ------------------------------------------------------------------------ *)
(* convert all lemmas to the continuous versions                            *)
(* ------------------------------------------------------------------------ *)

lemma beta_cfun_sprod: 
        "(LAM x y. Ispair x y)$a$b = Ispair a b"
apply (subst beta_cfun)
apply (simp (no_asm) add: cont_Ispair2 cont_Ispair1 cont2cont_CF1L)
apply (subst beta_cfun)
apply (rule cont_Ispair2)
apply (rule refl)
done

declare beta_cfun_sprod [simp]

lemma inject_spair: 
        "[| aa~=UU ; ba~=UU ; (:a,b:)=(:aa,ba:) |] ==> a=aa & b=ba"
apply (unfold spair_def)
apply (erule inject_Ispair)
apply assumption
apply (erule box_equals)
apply (rule beta_cfun_sprod)
apply (rule beta_cfun_sprod)
done

lemma inst_sprod_pcpo2: "UU = (:UU,UU:)"
apply (unfold spair_def)
apply (rule sym)
apply (rule trans)
apply (rule beta_cfun_sprod)
apply (rule sym)
apply (rule inst_sprod_pcpo)
done

lemma strict_spair: 
        "(a=UU | b=UU) ==> (:a,b:)=UU"
apply (unfold spair_def)
apply (rule trans)
apply (rule beta_cfun_sprod)
apply (rule trans)
apply (rule_tac [2] inst_sprod_pcpo [symmetric])
apply (erule strict_Ispair)
done

lemma strict_spair1: "(:UU,b:) = UU"
apply (unfold spair_def)
apply (subst beta_cfun_sprod)
apply (rule trans)
apply (rule_tac [2] inst_sprod_pcpo [symmetric])
apply (rule strict_Ispair1)
done

lemma strict_spair2: "(:a,UU:) = UU"
apply (unfold spair_def)
apply (subst beta_cfun_sprod)
apply (rule trans)
apply (rule_tac [2] inst_sprod_pcpo [symmetric])
apply (rule strict_Ispair2)
done

declare strict_spair1 [simp] strict_spair2 [simp]

lemma strict_spair_rev: "(:x,y:)~=UU ==> ~x=UU & ~y=UU"
apply (unfold spair_def)
apply (rule strict_Ispair_rev)
apply auto
done

lemma defined_spair_rev: "(:a,b:) = UU ==> (a = UU | b = UU)"
apply (unfold spair_def)
apply (rule defined_Ispair_rev)
apply auto
done

lemma defined_spair: 
        "[|a~=UU; b~=UU|] ==> (:a,b:) ~= UU"
apply (unfold spair_def)
apply (subst beta_cfun_sprod)
apply (subst inst_sprod_pcpo)
apply (erule defined_Ispair)
apply assumption
done

lemma Exh_Sprod2:
        "z=UU | (? a b. z=(:a,b:) & a~=UU & b~=UU)"
apply (unfold spair_def)
apply (rule Exh_Sprod [THEN disjE])
apply (rule disjI1)
apply (subst inst_sprod_pcpo)
apply assumption
apply (rule disjI2)
apply (erule exE)
apply (erule exE)
apply (rule exI)
apply (rule exI)
apply (rule conjI)
apply (subst beta_cfun_sprod)
apply fast
apply fast
done


lemma sprodE:
assumes prem1: "p=UU ==> Q"
assumes prem2: "!!x y. [| p=(:x,y:); x~=UU; y~=UU|] ==> Q"
shows "Q"
apply (rule IsprodE)
apply (rule prem1)
apply (subst inst_sprod_pcpo)
apply assumption
apply (rule prem2)
prefer 2 apply (assumption)
prefer 2 apply (assumption)
apply (unfold spair_def)
apply (subst beta_cfun_sprod)
apply assumption
done


lemma strict_sfst: 
        "p=UU==>sfst$p=UU"
apply (unfold sfst_def)
apply (subst beta_cfun)
apply (rule cont_Isfst)
apply (rule strict_Isfst)
apply (rule inst_sprod_pcpo [THEN subst])
apply assumption
done

lemma strict_sfst1: 
        "sfst$(:UU,y:) = UU"
apply (unfold sfst_def spair_def)
apply (subst beta_cfun_sprod)
apply (subst beta_cfun)
apply (rule cont_Isfst)
apply (rule strict_Isfst1)
done
 
lemma strict_sfst2: 
        "sfst$(:x,UU:) = UU"
apply (unfold sfst_def spair_def)
apply (subst beta_cfun_sprod)
apply (subst beta_cfun)
apply (rule cont_Isfst)
apply (rule strict_Isfst2)
done

lemma strict_ssnd: 
        "p=UU==>ssnd$p=UU"
apply (unfold ssnd_def)
apply (subst beta_cfun)
apply (rule cont_Issnd)
apply (rule strict_Issnd)
apply (rule inst_sprod_pcpo [THEN subst])
apply assumption
done

lemma strict_ssnd1: 
        "ssnd$(:UU,y:) = UU"
apply (unfold ssnd_def spair_def)
apply (subst beta_cfun_sprod)
apply (subst beta_cfun)
apply (rule cont_Issnd)
apply (rule strict_Issnd1)
done

lemma strict_ssnd2: 
        "ssnd$(:x,UU:) = UU"
apply (unfold ssnd_def spair_def)
apply (subst beta_cfun_sprod)
apply (subst beta_cfun)
apply (rule cont_Issnd)
apply (rule strict_Issnd2)
done

lemma sfst2: 
        "y~=UU ==>sfst$(:x,y:)=x"
apply (unfold sfst_def spair_def)
apply (subst beta_cfun_sprod)
apply (subst beta_cfun)
apply (rule cont_Isfst)
apply (erule Isfst2)
done

lemma ssnd2: 
        "x~=UU ==>ssnd$(:x,y:)=y"
apply (unfold ssnd_def spair_def)
apply (subst beta_cfun_sprod)
apply (subst beta_cfun)
apply (rule cont_Issnd)
apply (erule Issnd2)
done


lemma defined_sfstssnd: 
        "p~=UU ==> sfst$p ~=UU & ssnd$p ~=UU"
apply (unfold sfst_def ssnd_def spair_def)
apply (simplesubst beta_cfun)
apply (rule cont_Issnd)
apply (subst beta_cfun)
apply (rule cont_Isfst)
apply (rule defined_IsfstIssnd)
apply (rule inst_sprod_pcpo [THEN subst])
apply assumption
done
 
lemma surjective_pairing_Sprod2: "(:sfst$p , ssnd$p:) = p"
 
apply (unfold sfst_def ssnd_def spair_def)
apply (subst beta_cfun_sprod)
apply (simplesubst beta_cfun)
apply (rule cont_Issnd)
apply (subst beta_cfun)
apply (rule cont_Isfst)
apply (rule surjective_pairing_Sprod [symmetric])
done

lemma lub_sprod2: 
"chain(S) ==> range(S) <<|  
               (: lub(range(%i. sfst$(S i))), lub(range(%i. ssnd$(S i))) :)"
apply (unfold sfst_def ssnd_def spair_def)
apply (subst beta_cfun_sprod)
apply (simplesubst beta_cfun [THEN ext])
apply (rule cont_Issnd)
apply (subst beta_cfun [THEN ext])
apply (rule cont_Isfst)
apply (erule lub_sprod)
done


lemmas thelub_sprod2 = lub_sprod2 [THEN thelubI, standard]
(*
 "chain ?S1 ==>
 lub (range ?S1) =
 (:lub (range (%i. sfst$(?S1 i))), lub (range (%i. ssnd$(?S1 i))):)" : thm
*)

lemma ssplit1: 
        "ssplit$f$UU=UU"

apply (unfold ssplit_def)
apply (subst beta_cfun)
apply (simp (no_asm))
apply (subst strictify1)
apply (rule refl)
done

lemma ssplit2: 
        "[|x~=UU;y~=UU|] ==> ssplit$f$(:x,y:)= f$x$y"
apply (unfold ssplit_def)
apply (subst beta_cfun)
apply (simp (no_asm))
apply (subst strictify2)
apply (rule defined_spair)
apply assumption
apply assumption
apply (subst beta_cfun)
apply (simp (no_asm))
apply (subst sfst2)
apply assumption
apply (subst ssnd2)
apply assumption
apply (rule refl)
done


lemma ssplit3: 
  "ssplit$spair$z=z"

apply (unfold ssplit_def)
apply (subst beta_cfun)
apply (simp (no_asm))
apply (case_tac "z=UU")
apply (erule ssubst)
apply (rule strictify1)
apply (rule trans)
apply (rule strictify2)
apply assumption
apply (subst beta_cfun)
apply (simp (no_asm))
apply (rule surjective_pairing_Sprod2)
done

(* ------------------------------------------------------------------------ *)
(* install simplifier for Sprod                                             *)
(* ------------------------------------------------------------------------ *)

lemmas Sprod_rews = strict_sfst1 strict_sfst2
                strict_ssnd1 strict_ssnd2 sfst2 ssnd2 defined_spair
                ssplit1 ssplit2
declare Sprod_rews [simp]

end
