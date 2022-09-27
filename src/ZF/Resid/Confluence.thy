(*  Title:      ZF/Resid/Confluence.thy
    Author:     Ole Rasmussen
    Copyright   1995  University of Cambridge
*)

theory Confluence imports Reduction begin

definition
  confluence    :: "i=>o"  where
    "confluence(R) \<equiv>   
       \<forall>x y. <x,y> \<in> R \<longrightarrow> (\<forall>z.<x,z> \<in> R \<longrightarrow> (\<exists>u.<y,u> \<in> R & <z,u> \<in> R))"

definition
  strip         :: "o"  where
    "strip \<equiv> \<forall>x y. (x =\<Longrightarrow> y) \<longrightarrow> 
                    (\<forall>z.(x =1=> z) \<longrightarrow> (\<exists>u.(y =1=> u) & (z=\<Longrightarrow>u)))" 


(* ------------------------------------------------------------------------- *)
(*        strip lemmas                                                       *)
(* ------------------------------------------------------------------------- *)

lemma strip_lemma_r: 
    "\<lbrakk>confluence(Spar_red1)\<rbrakk>\<Longrightarrow> strip"
apply (unfold confluence_def strip_def)
apply (rule impI [THEN allI, THEN allI])
apply (erule Spar_red.induct, fast)
apply (fast intro: Spar_red.trans)
done


lemma strip_lemma_l: 
    "strip\<Longrightarrow> confluence(Spar_red)"
apply (unfold confluence_def strip_def)
apply (rule impI [THEN allI, THEN allI])
apply (erule Spar_red.induct, blast)
apply clarify
apply (blast intro: Spar_red.trans)
done

(* ------------------------------------------------------------------------- *)
(*      Confluence                                                           *)
(* ------------------------------------------------------------------------- *)


lemma parallel_moves: "confluence(Spar_red1)"
apply (unfold confluence_def, clarify)
apply (frule simulation)
apply (frule_tac n = z in simulation, clarify)
apply (frule_tac v = va in paving)
apply (force intro: completeness)+
done

lemmas confluence_parallel_reduction =
      parallel_moves [THEN strip_lemma_r, THEN strip_lemma_l]

lemma lemma1: "\<lbrakk>confluence(Spar_red)\<rbrakk>\<Longrightarrow> confluence(Sred)"
by (unfold confluence_def, blast intro: par_red_red red_par_red)

lemmas confluence_beta_reduction =
       confluence_parallel_reduction [THEN lemma1]


(**** Conversion ****)

consts
  Sconv1        :: "i"
  Sconv         :: "i"

abbreviation
  Sconv1_rel (infixl \<open><-1->\<close> 50) where
  "a<-1->b \<equiv> <a,b> \<in> Sconv1"

abbreviation
  Sconv_rel (infixl \<open><-\<longrightarrow>\<close> 50) where
  "a<-\<longrightarrow>b \<equiv> <a,b> \<in> Sconv"
  
inductive
  domains       "Sconv1" \<subseteq> "lambda*lambda"
  intros
    red1:        "m -1-> n \<Longrightarrow> m<-1->n"
    expl:        "n -1-> m \<Longrightarrow> m<-1->n"
  type_intros    red1D1 red1D2 lambda.intros bool_typechecks

declare Sconv1.intros [intro]

inductive
  domains       "Sconv" \<subseteq> "lambda*lambda"
  intros
    one_step:    "m<-1->n  \<Longrightarrow> m<-\<longrightarrow>n"
    refl:        "m \<in> lambda \<Longrightarrow> m<-\<longrightarrow>m"
    trans:       "\<lbrakk>m<-\<longrightarrow>n; n<-\<longrightarrow>p\<rbrakk> \<Longrightarrow> m<-\<longrightarrow>p"
  type_intros    Sconv1.dom_subset [THEN subsetD] lambda.intros bool_typechecks

declare Sconv.intros [intro]

lemma conv_sym: "m<-\<longrightarrow>n \<Longrightarrow> n<-\<longrightarrow>m"
apply (erule Sconv.induct)
apply (erule Sconv1.induct, blast+)
done

(* ------------------------------------------------------------------------- *)
(*      Church_Rosser Theorem                                                *)
(* ------------------------------------------------------------------------- *)

lemma Church_Rosser: "m<-\<longrightarrow>n \<Longrightarrow> \<exists>p.(m -\<longrightarrow>p) & (n -\<longrightarrow> p)"
apply (erule Sconv.induct)
apply (erule Sconv1.induct)
apply (blast intro: red1D1 redD2)
apply (blast intro: red1D1 redD2)
apply (blast intro: red1D1 redD2)
apply (cut_tac confluence_beta_reduction)
apply (unfold confluence_def)
apply (blast intro: Sred.trans)
done

end

