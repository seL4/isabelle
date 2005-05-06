(*  Title:      HOLCF/Sprod.thy
    ID:         $Id$
    Author:     Franz Regensburger
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Strict product with typedef.
*)

header {* The type of strict products *}

theory Sprod
imports Cfun
begin

subsection {* Definition of strict product type *}

constdefs
  Spair_Rep     :: "['a,'b] => ['a,'b] => bool"
 "Spair_Rep == (%a b. %x y.(~a=UU & ~b=UU --> x=a  & y=b ))"

typedef (Sprod)  ('a, 'b) "**" (infixr 20) = "{f. ? a b. f = Spair_Rep (a::'a) (b::'b)}"
by auto

syntax (xsymbols)
  "**"		:: "[type, type] => type"	 ("(_ \<otimes>/ _)" [21,20] 20)
syntax (HTML output)
  "**"		:: "[type, type] => type"	 ("(_ \<otimes>/ _)" [21,20] 20)

consts
  Ispair        :: "['a,'b] => ('a ** 'b)"
  Isfst         :: "('a ** 'b) => 'a"
  Issnd         :: "('a ** 'b) => 'b"  

defs
   (*defining the abstract constants*)

  Ispair_def:    "Ispair a b == Abs_Sprod(Spair_Rep a b)"

  Isfst_def:     "Isfst(p) == THE z.     (p=Ispair UU UU --> z=UU)
                &(! a b. ~a=UU & ~b=UU & p=Ispair a b   --> z=a)"  

  Issnd_def:     "Issnd(p) == THE z.     (p=Ispair UU UU  --> z=UU)
                &(! a b. ~a=UU & ~b=UU & p=Ispair a b    --> z=b)"  

text {* A non-emptiness result for Sprod *}

lemma SprodI: "(Spair_Rep a b):Sprod"
apply (unfold Sprod_def)
apply (rule CollectI, rule exI, rule exI, rule refl)
done

lemma inj_on_Abs_Sprod: "inj_on Abs_Sprod Sprod"
apply (rule inj_on_inverseI)
apply (erule Abs_Sprod_inverse)
done

text {* Strictness and definedness of @{term Spair_Rep} *}

lemma strict_Spair_Rep: 
 "(a=UU | b=UU) ==> (Spair_Rep a b) = (Spair_Rep UU UU)"
apply (unfold Spair_Rep_def)
apply (rule ext)
apply (rule ext)
apply (rule iffI)
apply fast
apply fast
done

lemma defined_Spair_Rep_rev: 
 "(Spair_Rep a b) = (Spair_Rep UU UU) ==> (a=UU | b=UU)"
apply (unfold Spair_Rep_def)
apply (case_tac "a=UU|b=UU")
apply assumption
apply (fast dest: fun_cong)
done

text {* injectivity of @{term Spair_Rep} and @{term Ispair} *}

lemma inject_Spair_Rep: 
"[|~aa=UU ; ~ba=UU ; Spair_Rep a b = Spair_Rep aa ba |] ==> a=aa & b=ba"

apply (unfold Spair_Rep_def)
apply (drule fun_cong)
apply (drule fun_cong)
apply (erule iffD1 [THEN mp])
apply auto
done

lemma inject_Ispair: 
        "[|~aa=UU ; ~ba=UU ; Ispair a b = Ispair aa ba |] ==> a=aa & b=ba"
apply (unfold Ispair_def)
apply (erule inject_Spair_Rep)
apply assumption
apply (erule inj_on_Abs_Sprod [THEN inj_onD])
apply (rule SprodI)
apply (rule SprodI)
done

text {* strictness and definedness of @{term Ispair} *}

lemma strict_Ispair: 
 "(a=UU | b=UU) ==> Ispair a b = Ispair UU UU"
apply (unfold Ispair_def)
apply (erule strict_Spair_Rep [THEN arg_cong])
done

lemma strict_Ispair1: 
        "Ispair UU b  = Ispair UU UU"
apply (unfold Ispair_def)
apply (rule strict_Spair_Rep [THEN arg_cong])
apply (rule disjI1)
apply (rule refl)
done

lemma strict_Ispair2: 
        "Ispair a UU = Ispair UU UU"
apply (unfold Ispair_def)
apply (rule strict_Spair_Rep [THEN arg_cong])
apply (rule disjI2)
apply (rule refl)
done

lemma strict_Ispair_rev: "~Ispair x y = Ispair UU UU ==> ~x=UU & ~y=UU"
apply (rule de_Morgan_disj [THEN subst])
apply (erule contrapos_nn)
apply (erule strict_Ispair)
done

lemma defined_Ispair_rev: 
        "Ispair a b  = Ispair UU UU ==> (a = UU | b = UU)"
apply (unfold Ispair_def)
apply (rule defined_Spair_Rep_rev)
apply (rule inj_on_Abs_Sprod [THEN inj_onD])
apply assumption
apply (rule SprodI)
apply (rule SprodI)
done

lemma defined_Ispair: "[|a~=UU; b~=UU|] ==> (Ispair a b) ~= (Ispair UU UU)"
apply (rule contrapos_nn)
apply (erule_tac [2] defined_Ispair_rev)
apply (rule de_Morgan_disj [THEN iffD2])
apply (erule conjI)
apply assumption
done

text {* Exhaustion of the strict product @{typ "'a ** 'b"} *}

lemma Exh_Sprod:
        "z=Ispair UU UU | (? a b. z=Ispair a b & a~=UU & b~=UU)"
apply (unfold Ispair_def)
apply (rule Rep_Sprod[unfolded Sprod_def, THEN CollectE])
apply (erule exE)
apply (erule exE)
apply (rule excluded_middle [THEN disjE])
apply (rule disjI2)
apply (rule exI)
apply (rule exI)
apply (rule conjI)
apply (rule Rep_Sprod_inverse [symmetric, THEN trans])
apply (erule arg_cong)
apply (rule de_Morgan_disj [THEN subst])
apply assumption
apply (rule disjI1)
apply (rule Rep_Sprod_inverse [symmetric, THEN trans])
apply (rule_tac f = "Abs_Sprod" in arg_cong)
apply (erule trans)
apply (erule strict_Spair_Rep)
done

text {* general elimination rule for strict product *}

lemma IsprodE:
assumes prem1: "p=Ispair UU UU ==> Q"
assumes prem2: "!!x y. [|p=Ispair x y; x~=UU ; y~=UU|] ==> Q"
shows "Q"
apply (rule Exh_Sprod [THEN disjE])
apply (erule prem1)
apply (erule exE)
apply (erule exE)
apply (erule conjE)
apply (erule conjE)
apply (erule prem2)
apply assumption
apply assumption
done

text {* some results about the selectors @{term Isfst}, @{term Issnd} *}

lemma strict_Isfst: "p=Ispair UU UU ==> Isfst p = UU"
apply (unfold Isfst_def)
apply (rule the_equality)
apply (rule conjI)
apply fast
apply (intro strip)
apply (rule_tac P = "Ispair UU UU = Ispair a b" in notE)
apply (rule not_sym)
apply (rule defined_Ispair)
apply (fast+)
done

lemma strict_Isfst1 [simp]: "Isfst(Ispair UU y) = UU"
apply (subst strict_Ispair1)
apply (rule strict_Isfst)
apply (rule refl)
done

lemma strict_Isfst2 [simp]: "Isfst(Ispair x UU) = UU"
apply (subst strict_Ispair2)
apply (rule strict_Isfst)
apply (rule refl)
done

lemma strict_Issnd: "p=Ispair UU UU ==>Issnd p=UU"
apply (unfold Issnd_def)
apply (rule the_equality)
apply (rule conjI)
apply fast
apply (intro strip)
apply (rule_tac P = "Ispair UU UU = Ispair a b" in notE)
apply (rule not_sym)
apply (rule defined_Ispair)
apply (fast+)
done

lemma strict_Issnd1 [simp]: "Issnd(Ispair UU y) = UU"
apply (subst strict_Ispair1)
apply (rule strict_Issnd)
apply (rule refl)
done

lemma strict_Issnd2 [simp]: "Issnd(Ispair x UU) = UU"
apply (subst strict_Ispair2)
apply (rule strict_Issnd)
apply (rule refl)
done

lemma Isfst: "[|x~=UU ;y~=UU |] ==> Isfst(Ispair x y) = x"
apply (unfold Isfst_def)
apply (rule the_equality)
apply (rule conjI)
apply (intro strip)
apply (rule_tac P = "Ispair x y = Ispair UU UU" in notE)
apply (erule defined_Ispair)
apply assumption
apply assumption
apply (intro strip)
apply (rule inject_Ispair [THEN conjunct1])
prefer 3 apply fast
apply (fast+)
done

lemma Issnd: "[|x~=UU ;y~=UU |] ==> Issnd(Ispair x y) = y"
apply (unfold Issnd_def)
apply (rule the_equality)
apply (rule conjI)
apply (intro strip)
apply (rule_tac P = "Ispair x y = Ispair UU UU" in notE)
apply (erule defined_Ispair)
apply assumption
apply assumption
apply (intro strip)
apply (rule inject_Ispair [THEN conjunct2])
prefer 3 apply fast
apply (fast+)
done

lemma Isfst2: "y~=UU ==>Isfst(Ispair x y)=x"
apply (rule_tac Q = "x=UU" in excluded_middle [THEN disjE])
apply (erule Isfst)
apply assumption
apply (erule ssubst)
apply (rule strict_Isfst1)
done

lemma Issnd2: "~x=UU ==>Issnd(Ispair x y)=y"
apply (rule_tac Q = "y=UU" in excluded_middle [THEN disjE])
apply (erule Issnd)
apply assumption
apply (erule ssubst)
apply (rule strict_Issnd2)
done


text {* instantiate the simplifier *}

lemmas Sprod0_ss = strict_Isfst1 strict_Isfst2 strict_Issnd1 strict_Issnd2
                 Isfst2 Issnd2

declare Isfst2 [simp] Issnd2 [simp]

lemma defined_IsfstIssnd: "p~=Ispair UU UU ==> Isfst p ~= UU & Issnd p ~= UU"
apply (rule_tac p = "p" in IsprodE)
apply simp
apply (erule ssubst)
apply (rule conjI)
apply (simp add: Sprod0_ss)
apply (simp add: Sprod0_ss)
done


text {* Surjective pairing: equivalent to @{thm [source] Exh_Sprod} *}

lemma surjective_pairing_Sprod: "z = Ispair(Isfst z)(Issnd z)"
apply (rule_tac z1 = "z" in Exh_Sprod [THEN disjE])
apply (simp add: Sprod0_ss)
apply (erule exE)
apply (erule exE)
apply (simp add: Sprod0_ss)
done

lemma Sel_injective_Sprod: "[|Isfst x = Isfst y; Issnd x = Issnd y|] ==> x = y"
apply (subgoal_tac "Ispair (Isfst x) (Issnd x) =Ispair (Isfst y) (Issnd y) ")
apply (simp (no_asm_use) add: surjective_pairing_Sprod[symmetric])
apply simp
done

subsection {* Type @{typ "'a ** 'b"} is a partial order *}

instance "**" :: (sq_ord, sq_ord) sq_ord ..

defs (overloaded)
  less_sprod_def: "p1 << p2 == Isfst p1 << Isfst p2 & Issnd p1 << Issnd p2"

lemma refl_less_sprod: "(p::'a ** 'b) << p"
apply (unfold less_sprod_def)
apply (fast intro: refl_less)
done

lemma antisym_less_sprod: 
        "[|(p1::'a ** 'b) << p2;p2 << p1|] ==> p1=p2"
apply (unfold less_sprod_def)
apply (rule Sel_injective_Sprod)
apply (fast intro: antisym_less)
apply (fast intro: antisym_less)
done

lemma trans_less_sprod: 
        "[|(p1::'a ** 'b) << p2;p2 << p3|] ==> p1 << p3"
apply (unfold less_sprod_def)
apply (blast intro: trans_less)
done

instance "**" :: (pcpo, pcpo) po
by intro_classes
  (assumption | rule refl_less_sprod antisym_less_sprod trans_less_sprod)+

text {* for compatibility with old HOLCF-Version *}
lemma inst_sprod_po: "(op <<)=(%x y. Isfst x<<Isfst y&Issnd x<<Issnd y)"
apply (fold less_sprod_def)
apply (rule refl)
done

subsection {* Monotonicity of @{term Ispair}, @{term Isfst}, @{term Issnd} *}

text {* @{term Ispair} is monotone in both arguments *}

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

text {* @{term Isfst} and @{term Issnd} are monotone *}

lemma monofun_Isfst: "monofun(Isfst)"
by (simp add: monofun inst_sprod_po)

lemma monofun_Issnd: "monofun(Issnd)"
by (simp add: monofun inst_sprod_po)

subsection {* Type @{typ "'a ** 'b"} is a cpo *}

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

instance "**" :: (pcpo, pcpo) cpo
by intro_classes (rule cpo_sprod)

subsection {* Type @{typ "'a ** 'b"} is pointed *}

lemma minimal_sprod: "Ispair UU UU << p"
apply (simp add: inst_sprod_po minimal)
done

lemmas UU_sprod_def = minimal_sprod [THEN minimal2UU, symmetric, standard]

lemma least_sprod: "? x::'a**'b.!y. x<<y"
apply (rule_tac x = "Ispair UU UU" in exI)
apply (rule minimal_sprod [THEN allI])
done

instance "**" :: (pcpo, pcpo) pcpo
by intro_classes (rule least_sprod)

text {* for compatibility with old HOLCF-Version *}
lemma inst_sprod_pcpo: "UU = Ispair UU UU"
by (simp add: UU_def UU_sprod_def)

declare inst_sprod_pcpo [symmetric, simp]

subsection {* Continuous versions of constants *}

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

subsection {* Continuity of @{term Ispair}, @{term Isfst}, @{term Issnd} *}

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

text {* convert all lemmas to the continuous versions *}

lemma beta_cfun_sprod [simp]: 
        "(LAM x y. Ispair x y)$a$b = Ispair a b"
apply (subst beta_cfun)
apply (simp (no_asm) add: cont_Ispair2 cont_Ispair1 cont2cont_CF1L)
apply (subst beta_cfun)
apply (rule cont_Ispair2)
apply (rule refl)
done

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

lemma defined_spair [simp]: 
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

lemma strict_sfst: "p=UU==>sfst$p=UU"
apply (unfold sfst_def)
apply (subst beta_cfun)
apply (rule cont_Isfst)
apply (rule strict_Isfst)
apply (rule inst_sprod_pcpo [THEN subst])
apply assumption
done

lemma strict_sfst1 [simp]: "sfst$(:UU,y:) = UU"
apply (unfold sfst_def spair_def)
apply (subst beta_cfun_sprod)
apply (subst beta_cfun)
apply (rule cont_Isfst)
apply (rule strict_Isfst1)
done

lemma strict_sfst2 [simp]: "sfst$(:x,UU:) = UU"
apply (unfold sfst_def spair_def)
apply (subst beta_cfun_sprod)
apply (subst beta_cfun)
apply (rule cont_Isfst)
apply (rule strict_Isfst2)
done

lemma strict_ssnd: "p=UU==>ssnd$p=UU"
apply (unfold ssnd_def)
apply (subst beta_cfun)
apply (rule cont_Issnd)
apply (rule strict_Issnd)
apply (rule inst_sprod_pcpo [THEN subst])
apply assumption
done

lemma strict_ssnd1 [simp]: "ssnd$(:UU,y:) = UU"
apply (unfold ssnd_def spair_def)
apply (subst beta_cfun_sprod)
apply (subst beta_cfun)
apply (rule cont_Issnd)
apply (rule strict_Issnd1)
done

lemma strict_ssnd2 [simp]: "ssnd$(:x,UU:) = UU"
apply (unfold ssnd_def spair_def)
apply (subst beta_cfun_sprod)
apply (subst beta_cfun)
apply (rule cont_Issnd)
apply (rule strict_Issnd2)
done

lemma sfst2 [simp]: "y~=UU ==>sfst$(:x,y:)=x"
apply (unfold sfst_def spair_def)
apply (subst beta_cfun_sprod)
apply (subst beta_cfun)
apply (rule cont_Isfst)
apply (erule Isfst2)
done

lemma ssnd2 [simp]: "x~=UU ==>ssnd$(:x,y:)=y"
apply (unfold ssnd_def spair_def)
apply (subst beta_cfun_sprod)
apply (subst beta_cfun)
apply (rule cont_Issnd)
apply (erule Issnd2)
done


lemma defined_sfstssnd: "p~=UU ==> sfst$p ~=UU & ssnd$p ~=UU"
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

lemma ssplit1 [simp]: "ssplit$f$UU=UU"
by (simp add: ssplit_def)

lemma ssplit2 [simp]: "[|x~=UU;y~=UU|] ==> ssplit$f$(:x,y:)= f$x$y"
by (simp add: ssplit_def)

lemma ssplit3: "ssplit$spair$z=z"
apply (simp add: ssplit_def)
apply (simp add: surjective_pairing_Sprod2)
apply (case_tac "z=UU", simp_all)
done

text {* install simplifier for Sprod *}

lemmas Sprod_rews = strict_sfst1 strict_sfst2
                strict_ssnd1 strict_ssnd2 sfst2 ssnd2 defined_spair
                ssplit1 ssplit2

end
