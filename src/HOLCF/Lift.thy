(*  Title:      HOLCF/Lift.thy
    ID:         $Id$
    Author:     Olaf Mueller
    License:    GPL (GNU GENERAL PUBLIC LICENSE)
*)

header {* Lifting types of class term to flat pcpo's *}

theory Lift = Cprod3:

defaultsort "term"


typedef 'a lift = "UNIV :: 'a option set" ..

constdefs
  Undef :: "'a lift"
  "Undef == Abs_lift None"
  Def :: "'a => 'a lift"
  "Def x == Abs_lift (Some x)"

instance lift :: ("term") sq_ord ..

defs (overloaded)
  less_lift_def: "x << y == (x=y | x=Undef)"

instance lift :: ("term") po
proof
  fix x y z :: "'a lift"
  show "x << x" by (unfold less_lift_def) blast
  { assume "x << y" and "y << x" thus "x = y" by (unfold less_lift_def) blast }
  { assume "x << y" and "y << z" thus "x << z" by (unfold less_lift_def) blast }
qed

lemma inst_lift_po: "(op <<) = (\<lambda>x y. x = y | x = Undef)"
  -- {* For compatibility with old HOLCF-Version. *}
  by (simp only: less_lift_def [symmetric])


subsection {* Type lift is pointed *}

lemma minimal_lift [iff]: "Undef << x"
  by (simp add: inst_lift_po)

lemma UU_lift_def: "(SOME u. \<forall>y. u \<sqsubseteq> y) = Undef"
  apply (rule minimal2UU [symmetric])
  apply (rule minimal_lift)
  done

lemma least_lift: "EX x::'a lift. ALL y. x << y"
  apply (rule_tac x = Undef in exI)
  apply (rule minimal_lift [THEN allI])
  done


subsection {* Type lift is a cpo *}

text {*
  The following lemmas have already been proved in @{text Pcpo.ML} and
  @{text Fix.ML}, but there class @{text pcpo} is assumed, although
  only @{text po} is necessary and a least element. Therefore they are
  redone here for the @{text po} lift with least element @{text
  Undef}.
*}

lemma notUndef_I: "[| x<<y; x ~= Undef |] ==> y ~= Undef"
  -- {* Tailoring @{text notUU_I} of @{text Pcpo.ML} to @{text Undef} *}
  by (blast intro: antisym_less)

lemma chain_mono2_po: "[| EX j.~Y(j)=Undef; chain(Y::nat=>('a)lift) |]
         ==> EX j. ALL i. j<i-->~Y(i)=Undef"
  -- {* Tailoring @{text chain_mono2} of @{text Pcpo.ML} to @{text Undef} *}
  apply safe
  apply (rule exI)
  apply (intro strip)
  apply (rule notUndef_I)
   apply (erule (1) chain_mono)
  apply assumption
  done

lemma flat_imp_chfin_poo: "(ALL Y. chain(Y::nat=>('a)lift)-->(EX n. max_in_chain n Y))"
  -- {* Tailoring @{text flat_imp_chfin} of @{text Fix.ML} to @{text lift} *}
  apply (unfold max_in_chain_def)
  apply (intro strip)
  apply (rule_tac P = "ALL i. Y (i) = Undef" in case_split)
   apply (rule_tac x = 0 in exI)
   apply (intro strip)
   apply (rule trans)
    apply (erule spec)
   apply (rule sym)
   apply (erule spec)
  apply (subgoal_tac "ALL x y. x << (y:: ('a) lift) --> x=Undef | x=y")
   prefer 2 apply (simp add: inst_lift_po)
  apply (rule chain_mono2_po [THEN exE])
    apply fast
   apply assumption
  apply (rule_tac x = "Suc x" in exI)
  apply (intro strip)
  apply (rule disjE)
    prefer 3 apply assumption
   apply (rule mp)
    apply (drule spec)
    apply (erule spec)
   apply (erule le_imp_less_or_eq [THEN disjE])
    apply (erule chain_mono)
    apply auto
  done

theorem cpo_lift: "chain (Y::nat => 'a lift) ==> EX x. range Y <<| x"
  apply (cut_tac flat_imp_chfin_poo)
  apply (blast intro: lub_finch1)
  done

instance lift :: ("term") pcpo
  apply intro_classes
   apply (erule cpo_lift)
  apply (rule least_lift)
  done

lemma inst_lift_pcpo: "UU = Undef"
  -- {* For compatibility with old HOLCF-Version. *}
  by (simp add: UU_def UU_lift_def)


subsection {* Lift as a datatype *}

lemma lift_distinct1: "UU ~= Def x"
  by (simp add: Undef_def Def_def Abs_lift_inject lift_def inst_lift_pcpo)

lemma lift_distinct2: "Def x ~= UU"
  by (simp add: Undef_def Def_def Abs_lift_inject lift_def inst_lift_pcpo)

lemma Def_inject: "(Def x = Def x') = (x = x')"
  by (simp add: Def_def Abs_lift_inject lift_def)

lemma lift_induct: "P UU ==> (!!x. P (Def x)) ==> P y"
  apply (induct y)
  apply (induct_tac y)
   apply (simp_all add: Undef_def Def_def inst_lift_pcpo)
  done

rep_datatype lift
  distinct lift_distinct1 lift_distinct2
  inject Def_inject
  induction lift_induct

lemma Def_not_UU: "Def a ~= UU"
  by simp


subsection {* Further operations *}

consts
 flift1      :: "('a => 'b::pcpo) => ('a lift -> 'b)"
 flift2      :: "('a => 'b)       => ('a lift -> 'b lift)"
 liftpair    ::"'a::term lift * 'b::term lift => ('a * 'b) lift"

defs
 flift1_def:
  "flift1 f == (LAM x. (case x of
                   UU => UU
                 | Def y => (f y)))"
 flift2_def:
  "flift2 f == (LAM x. (case x of
                   UU => UU
                 | Def y => Def (f y)))"
 liftpair_def:
  "liftpair x  == (case (cfst$x) of
                  UU  => UU
                | Def x1 => (case (csnd$x) of
                               UU => UU
                             | Def x2 => Def (x1,x2)))"


declare inst_lift_pcpo [symmetric, simp]


lemma less_lift: "(x::'a lift) << y = (x=y | x=UU)"
  by (simp add: inst_lift_po)


text {* @{text UU} and @{text Def} *}

lemma Lift_exhaust: "x = UU | (EX y. x = Def y)"
  by (induct x) simp_all

lemma Lift_cases: "[| x = UU ==> P; ? a. x = Def a ==> P |] ==> P"
  by (insert Lift_exhaust) blast

lemma not_Undef_is_Def: "(x ~= UU) = (EX y. x = Def y)"
  by (cases x) simp_all

text {*
  For @{term "x ~= UU"} in assumptions @{text def_tac} replaces @{text
  x} by @{text "Def a"} in conclusion. *}

ML {*
  local val not_Undef_is_Def = thm "not_Undef_is_Def"
  in val def_tac = SIMPSET' (fn ss =>
    etac (not_Undef_is_Def RS iffD1 RS exE) THEN' asm_simp_tac ss)
  end;
*}

lemma Undef_eq_UU: "Undef = UU"
  by (rule inst_lift_pcpo [symmetric])

lemma DefE: "Def x = UU ==> R"
  by simp

lemma DefE2: "[| x = Def s; x = UU |] ==> R"
  by simp

lemma Def_inject_less_eq: "Def x << Def y = (x = y)"
  by (simp add: less_lift_def)

lemma Def_less_is_eq [simp]: "Def x << y = (Def x = y)"
  by (simp add: less_lift)


subsection {* Lift is flat *}

instance lift :: ("term") flat
proof
  show "ALL x y::'a lift. x << y --> x = UU | x = y"
    by (simp add: less_lift)
qed

defaultsort pcpo


text {*
  \medskip Two specific lemmas for the combination of LCF and HOL
  terms.
*}

lemma cont_Rep_CFun_app: "[|cont g; cont f|] ==> cont(%x. ((f x)$(g x)) s)"
  apply (rule cont2cont_CF1L)
  apply (tactic "resolve_tac cont_lemmas1 1")+
   apply auto
  done

lemma cont_Rep_CFun_app_app: "[|cont g; cont f|] ==> cont(%x. ((f x)$(g x)) s t)"
  apply (rule cont2cont_CF1L)
  apply (erule cont_Rep_CFun_app)
  apply assumption
  done

text {* Continuity of if-then-else. *}

lemma cont_if: "[| cont f1; cont f2 |] ==> cont (%x. if b then f1 x else f2 x)"
  by (cases b) simp_all


subsection {* Continuity Proofs for flift1, flift2, if *}

text {* Need the instance of @{text flat}. *}

lemma cont_flift1_arg: "cont (lift_case UU f)"
  -- {* @{text flift1} is continuous in its argument itself. *}
  apply (rule flatdom_strict2cont)
  apply simp
  done

lemma cont_flift1_not_arg: "!!f. [| !! a. cont (%y. (f y) a) |] ==>
           cont (%y. lift_case UU (f y))"
  -- {* @{text flift1} is continuous in a variable that occurs only
    in the @{text Def} branch. *}
  apply (rule cont2cont_CF1L_rev)
  apply (intro strip)
  apply (case_tac y)
   apply simp
  apply simp
  done

lemma cont_flift1_arg_and_not_arg: "!!f. [| !! a. cont (%y. (f y) a); cont g|] ==>
    cont (%y. lift_case UU (f y) (g y))"
  -- {* @{text flift1} is continuous in a variable that occurs either
    in the @{text Def} branch or in the argument. *}
  apply (rule_tac tt = g in cont2cont_app)
    apply (rule cont_flift1_not_arg)
    apply auto
  apply (rule cont_flift1_arg)
  done

lemma cont_flift2_arg: "cont (lift_case UU (%y. Def (f y)))"
  -- {* @{text flift2} is continuous in its argument itself. *}
  apply (rule flatdom_strict2cont)
  apply simp
  done

text {*
  \medskip Extension of cont_tac and installation of simplifier.
*}

lemma cont2cont_CF1L_rev2: "(!!y. cont (%x. c1 x y)) ==> cont c1"
  apply (rule cont2cont_CF1L_rev)
  apply simp
  done

lemmas cont_lemmas_ext [simp] =
  cont_flift1_arg cont_flift2_arg
  cont_flift1_arg_and_not_arg cont2cont_CF1L_rev2
  cont_Rep_CFun_app cont_Rep_CFun_app_app cont_if

ML_setup {*
val cont_lemmas2 = cont_lemmas1 @ thms "cont_lemmas_ext";

fun cont_tac  i = resolve_tac cont_lemmas2 i;
fun cont_tacR i = REPEAT (cont_tac i);

local val flift1_def = thm "flift1_def" and flift2_def = thm "flift2_def"
in fun cont_tacRs i =
  simp_tac (simpset() addsimps [flift1_def, flift2_def]) i THEN
  REPEAT (cont_tac i)
end;

simpset_ref() := simpset() addSolver
  (mk_solver "cont_tac" (K (DEPTH_SOLVE_1 o cont_tac)));
*}


subsection {* flift1, flift2 *}

lemma flift1_Def [simp]: "flift1 f$(Def x) = (f x)"
  by (simp add: flift1_def)

lemma flift2_Def [simp]: "flift2 f$(Def x) = Def (f x)"
  by (simp add: flift2_def)

lemma flift1_UU [simp]: "flift1 f$UU = UU"
  by (simp add: flift1_def)

lemma flift2_UU [simp]: "flift2 f$UU = UU"
  by (simp add: flift2_def)

lemma flift2_nUU [simp]: "x~=UU ==> (flift2 f)$x~=UU"
  by (tactic "def_tac 1")

end
