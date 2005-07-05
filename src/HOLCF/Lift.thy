(*  Title:      HOLCF/Lift.thy
    ID:         $Id$
    Author:     Olaf Mueller
*)

header {* Lifting types of class type to flat pcpo's *}

theory Lift
imports Cprod
begin

defaultsort type


typedef 'a lift = "UNIV :: 'a option set" ..

constdefs
  Undef :: "'a lift"
  "Undef == Abs_lift None"
  Def :: "'a => 'a lift"
  "Def x == Abs_lift (Some x)"

instance lift :: (type) sq_ord ..

defs (overloaded)
  less_lift_def: "x << y == (x=y | x=Undef)"

instance lift :: (type) po
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

lemma UU_lift_def: "(THE u. \<forall>y. u \<sqsubseteq> y) = Undef"
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

lemma flat_imp_chfin_poo: "(ALL Y. chain(Y::nat=>('a)lift)-->(EX n. max_in_chain n Y))"
  -- {* Tailoring @{text flat_imp_chfin} of @{text Fix.ML} to @{text lift} *}
  apply (unfold max_in_chain_def)
  apply clarify
  apply (case_tac "ALL i. Y i = Undef")
   apply simp
  apply simp
  apply (erule exE)
  apply (rule_tac x=i in exI)
  apply clarify
  apply (drule chain_mono3, assumption)
  apply (simp add: less_lift_def)
  done

instance lift :: (type) chfin
  apply intro_classes
  apply (rule flat_imp_chfin_poo)
  done

instance lift :: (type) pcpo
  apply intro_classes
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

lemma lift_definedE: "\<lbrakk>x \<noteq> \<bottom>; \<And>a. x = Def a \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  by (cases x) simp_all

text {*
  For @{term "x ~= UU"} in assumptions @{text def_tac} replaces @{text
  x} by @{text "Def a"} in conclusion. *}

ML {*
  local val lift_definedE = thm "lift_definedE"
  in val def_tac = SIMPSET' (fn ss =>
    etac lift_definedE THEN' asm_simp_tac ss)
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

instance lift :: (type) flat
proof
  show "ALL x y::'a lift. x << y --> x = UU | x = y"
    by (simp add: less_lift)
qed

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

subsection {* Further operations *}

constdefs
  flift1 :: "('a \<Rightarrow> 'b::pcpo) \<Rightarrow> ('a lift \<rightarrow> 'b)" (binder "FLIFT " 10)
  "flift1 \<equiv> \<lambda>f. (\<Lambda> x. lift_case \<bottom> f x)"

  flift2 :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a lift \<rightarrow> 'b lift)"
  "flift2 f \<equiv> FLIFT x. Def (f x)"

  liftpair :: "'a lift \<times> 'b lift \<Rightarrow> ('a \<times> 'b) lift"
  "liftpair x \<equiv> csplit\<cdot>(FLIFT x y. Def (x, y))\<cdot>x"

subsection {* Continuity Proofs for flift1, flift2 *}

text {* Need the instance of @{text flat}. *}

lemma cont_lift_case1: "cont (\<lambda>f. lift_case a f x)"
apply (induct x)
apply simp
apply simp
apply (rule cont_id [THEN cont2cont_CF1L])
done

lemma cont_lift_case2: "cont (\<lambda>x. lift_case \<bottom> f x)"
apply (rule flatdom_strict2cont)
apply simp
done

lemma cont_flift1: "cont flift1"
apply (unfold flift1_def)
apply (rule cont2cont_LAM)
apply (rule cont_lift_case2)
apply (rule cont_lift_case1)
done

lemma cont2cont_flift1:
  "\<lbrakk>\<And>y. cont (\<lambda>x. f x y)\<rbrakk> \<Longrightarrow> cont (\<lambda>x. FLIFT y. f x y)"
apply (rule cont_flift1 [THEN cont2cont_app3])
apply (simp add: cont2cont_lambda)
done

lemma flift1_Def [simp]: "flift1 f\<cdot>(Def x) = (f x)"
by (simp add: flift1_def cont_lift_case2)

lemma flift2_Def [simp]: "flift2 f\<cdot>(Def x) = Def (f x)"
by (simp add: flift2_def)

lemma flift1_strict [simp]: "flift1 f\<cdot>\<bottom> = \<bottom>"
by (simp add: flift1_def cont_lift_case2)

lemma flift2_strict [simp]: "flift2 f\<cdot>\<bottom> = \<bottom>"
by (simp add: flift2_def)

lemma flift2_defined [simp]: "x \<noteq> \<bottom> \<Longrightarrow> (flift2 f)\<cdot>x \<noteq> \<bottom>"
by (erule lift_definedE, simp)

text {* old continuity rules *}

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
  apply (rule_tac t=g in cont2cont_app)
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
  \medskip Extension of @{text cont_tac} and installation of simplifier.
*}

lemmas cont_lemmas_ext [simp] =
  cont_flift1_arg cont_flift2_arg
  cont_flift1_arg_and_not_arg cont2cont_lambda
  cont_Rep_CFun_app cont_Rep_CFun_app_app cont_if

ML {*
val cont_lemmas2 = cont_lemmas1 @ thms "cont_lemmas_ext";

fun cont_tac  i = resolve_tac cont_lemmas2 i;
fun cont_tacR i = REPEAT (cont_tac i);

local val flift1_def = thm "flift1_def" and flift2_def = thm "flift2_def"
in fun cont_tacRs i =
  simp_tac (simpset() addsimps [flift1_def, flift2_def]) i THEN
  REPEAT (cont_tac i)
end;
*}

end
