(*  Title:      Reduction.thy
    ID:         $Id$
    Author:     Ole Rasmussen
    Copyright   1995  University of Cambridge
    Logic Image: ZF
*)

theory Reduction = Residuals:

(**** Lambda-terms ****)

consts
  lambda        :: "i"
  unmark        :: "i=>i"
  Apl           :: "[i,i]=>i"

translations
  "Apl(n,m)" == "App(0,n,m)"
  
inductive
  domains       "lambda" <= redexes
  intros
    Lambda_Var:  "               n \<in> nat ==>     Var(n) \<in> lambda"
    Lambda_Fun:  "            u \<in> lambda ==>     Fun(u) \<in> lambda"
    Lambda_App:  "[|u \<in> lambda; v \<in> lambda|] ==> Apl(u,v) \<in> lambda"
  type_intros    redexes.intros bool_typechecks

declare lambda.intros [intro]

primrec
  "unmark(Var(n)) = Var(n)"
  "unmark(Fun(u)) = Fun(unmark(u))"
  "unmark(App(b,f,a)) = Apl(unmark(f), unmark(a))"


declare lambda.intros [simp] 
declare lambda.dom_subset [THEN subsetD, simp, intro]


(* ------------------------------------------------------------------------- *)
(*        unmark lemmas                                                      *)
(* ------------------------------------------------------------------------- *)

lemma unmark_type [intro, simp]:
     "u \<in> redexes ==> unmark(u) \<in> lambda"
by (erule redexes.induct, simp_all)

lemma lambda_unmark: "u \<in> lambda ==> unmark(u) = u"
by (erule lambda.induct, simp_all)


(* ------------------------------------------------------------------------- *)
(*         lift and subst preserve lambda                                    *)
(* ------------------------------------------------------------------------- *)

lemma liftL_type [rule_format]:
     "v \<in> lambda ==> \<forall>k \<in> nat. lift_rec(v,k) \<in> lambda"
by (erule lambda.induct, simp_all add: lift_rec_Var)

lemma substL_type [rule_format, simp]:
     "v \<in> lambda ==>  \<forall>n \<in> nat. \<forall>u \<in> lambda. subst_rec(u,v,n) \<in> lambda"
by (erule lambda.induct, simp_all add: liftL_type subst_Var)


(* ------------------------------------------------------------------------- *)
(*        type-rule for reduction definitions                               *)
(* ------------------------------------------------------------------------- *)

lemmas red_typechecks = substL_type nat_typechecks lambda.intros 
                        bool_typechecks

consts
  Sred1     :: "i"
  Sred      :: "i"
  Spar_red1 :: "i"
  Spar_red  :: "i"
  "-1->"    :: "[i,i]=>o"  (infixl 50)
  "--->"    :: "[i,i]=>o"  (infixl 50)
  "=1=>"    :: "[i,i]=>o"  (infixl 50)
  "===>"    :: "[i,i]=>o"  (infixl 50)

translations
  "a -1-> b" == "<a,b> \<in> Sred1"
  "a ---> b" == "<a,b> \<in> Sred"
  "a =1=> b" == "<a,b> \<in> Spar_red1"
  "a ===> b" == "<a,b> \<in> Spar_red"
  
  
inductive
  domains       "Sred1" <= "lambda*lambda"
  intros
    beta:       "[|m \<in> lambda; n \<in> lambda|] ==> Apl(Fun(m),n) -1-> n/m"
    rfun:       "[|m -1-> n|] ==> Fun(m) -1-> Fun(n)"
    apl_l:      "[|m2 \<in> lambda; m1 -1-> n1|] ==> Apl(m1,m2) -1-> Apl(n1,m2)"
    apl_r:      "[|m1 \<in> lambda; m2 -1-> n2|] ==> Apl(m1,m2) -1-> Apl(m1,n2)"
  type_intros    red_typechecks

declare Sred1.intros [intro, simp]

inductive
  domains       "Sred" <= "lambda*lambda"
  intros
    one_step:   "m-1->n ==> m--->n"
    refl:       "m \<in> lambda==>m --->m"
    trans:      "[|m--->n; n--->p|] ==>m--->p"
  type_intros    Sred1.dom_subset [THEN subsetD] red_typechecks

declare Sred.one_step [intro, simp]
declare Sred.refl     [intro, simp]

inductive
  domains       "Spar_red1" <= "lambda*lambda"
  intros
    beta:       "[|m =1=> m'; n =1=> n'|] ==> Apl(Fun(m),n) =1=> n'/m'"
    rvar:       "n \<in> nat ==> Var(n) =1=> Var(n)"
    rfun:       "m =1=> m' ==> Fun(m) =1=> Fun(m')"
    rapl:       "[|m =1=> m'; n =1=> n'|] ==> Apl(m,n) =1=> Apl(m',n')"
  type_intros    red_typechecks

declare Spar_red1.intros [intro, simp]

inductive
  domains "Spar_red" <= "lambda*lambda"
  intros
    one_step:   "m =1=> n ==> m ===> n"
    trans:      "[|m===>n; n===>p|] ==> m===>p"
  type_intros    Spar_red1.dom_subset [THEN subsetD] red_typechecks

declare Spar_red.one_step [intro, simp]



(* ------------------------------------------------------------------------- *)
(*     Setting up rule lists for reduction                                   *)
(* ------------------------------------------------------------------------- *)

lemmas red1D1 [simp] = Sred1.dom_subset [THEN subsetD, THEN SigmaD1]
lemmas red1D2 [simp] = Sred1.dom_subset [THEN subsetD, THEN SigmaD2]
lemmas redD1 [simp] = Sred.dom_subset [THEN subsetD, THEN SigmaD1]
lemmas redD2 [simp] = Sred.dom_subset [THEN subsetD, THEN SigmaD2]

lemmas par_red1D1 [simp] = Spar_red1.dom_subset [THEN subsetD, THEN SigmaD1]
lemmas par_red1D2 [simp] = Spar_red1.dom_subset [THEN subsetD, THEN SigmaD2]
lemmas par_redD1 [simp] = Spar_red.dom_subset [THEN subsetD, THEN SigmaD1]
lemmas par_redD2 [simp] = Spar_red.dom_subset [THEN subsetD, THEN SigmaD2]

declare bool_typechecks [intro]

inductive_cases  [elim!]: "Fun(t) =1=> Fun(u)"



(* ------------------------------------------------------------------------- *)
(*     Lemmas for reduction                                                  *)
(* ------------------------------------------------------------------------- *)

lemma red_Fun: "m--->n ==> Fun(m) ---> Fun(n)"
apply (erule Sred.induct)
apply (rule_tac [3] Sred.trans, simp_all)
done

lemma red_Apll: "[|n \<in> lambda; m ---> m'|] ==> Apl(m,n)--->Apl(m',n)"
apply (erule Sred.induct)
apply (rule_tac [3] Sred.trans, simp_all)
done

lemma red_Aplr: "[|n \<in> lambda; m ---> m'|] ==> Apl(n,m)--->Apl(n,m')"
apply (erule Sred.induct)
apply (rule_tac [3] Sred.trans, simp_all)
done

lemma red_Apl: "[|m ---> m'; n--->n'|] ==> Apl(m,n)--->Apl(m',n')"
apply (rule_tac n = "Apl (m',n) " in Sred.trans)
apply (simp_all add: red_Apll red_Aplr)
done

lemma red_beta: "[|m \<in> lambda; m':lambda; n \<in> lambda; n':lambda; m ---> m'; n--->n'|] ==>  
               Apl(Fun(m),n)---> n'/m'"
apply (rule_tac n = "Apl (Fun (m'),n') " in Sred.trans)
apply (simp_all add: red_Apl red_Fun)
done


(* ------------------------------------------------------------------------- *)
(*      Lemmas for parallel reduction                                        *)
(* ------------------------------------------------------------------------- *)


lemma refl_par_red1: "m \<in> lambda==> m =1=> m"
by (erule lambda.induct, simp_all)

lemma red1_par_red1: "m-1->n ==> m=1=>n"
by (erule Sred1.induct, simp_all add: refl_par_red1)

lemma red_par_red: "m--->n ==> m===>n"
apply (erule Sred.induct)
apply (rule_tac [3] Spar_red.trans)
apply (simp_all add: refl_par_red1 red1_par_red1)
done

lemma par_red_red: "m===>n ==> m--->n"
apply (erule Spar_red.induct)
apply (erule Spar_red1.induct)
apply (rule_tac [5] Sred.trans)
apply (simp_all add: red_Fun red_beta red_Apl)
done


(* ------------------------------------------------------------------------- *)
(*      Simulation                                                           *)
(* ------------------------------------------------------------------------- *)

lemma simulation: "m=1=>n ==> \<exists>v. m|>v = n & m~v & regular(v)"
by (erule Spar_red1.induct, force+)


(* ------------------------------------------------------------------------- *)
(*           commuting of unmark and subst                                   *)
(* ------------------------------------------------------------------------- *)

lemma unmmark_lift_rec:
     "u \<in> redexes ==> \<forall>k \<in> nat. unmark(lift_rec(u,k)) = lift_rec(unmark(u),k)"
by (erule redexes.induct, simp_all add: lift_rec_Var)

lemma unmmark_subst_rec:
 "v \<in> redexes ==> \<forall>k \<in> nat. \<forall>u \<in> redexes.   
                  unmark(subst_rec(u,v,k)) = subst_rec(unmark(u),unmark(v),k)"
by (erule redexes.induct, simp_all add: unmmark_lift_rec subst_Var)


(* ------------------------------------------------------------------------- *)
(*        Completeness                                                       *)
(* ------------------------------------------------------------------------- *)

lemma completeness_l [rule_format]:
     "u~v ==> regular(v) --> unmark(u) =1=> unmark(u|>v)"
apply (erule Scomp.induct)
apply (auto simp add: unmmark_subst_rec)
done

lemma completeness: "[|u \<in> lambda; u~v; regular(v)|] ==> u =1=> unmark(u|>v)"
by (drule completeness_l, simp_all add: lambda_unmark)

end

