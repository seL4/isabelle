(*  Title:      Confluence.thy
    ID:         $Id$
    Author:     Ole Rasmussen
    Copyright   1995  University of Cambridge
    Logic Image: ZF
*)

theory Confluence = Reduction:

constdefs
  confluence    :: "i=>o"
    "confluence(R) ==   
       \<forall>x y. <x,y> \<in> R --> (\<forall>z.<x,z> \<in> R --> (\<exists>u.<y,u> \<in> R & <z,u> \<in> R))"

  strip         :: "o"
    "strip == \<forall>x y. (x ===> y) --> 
                    (\<forall>z.(x =1=> z) --> (\<exists>u.(y =1=> u) & (z===>u)))" 


(* ------------------------------------------------------------------------- *)
(*        strip lemmas                                                       *)
(* ------------------------------------------------------------------------- *)

lemma strip_lemma_r: 
    "[|confluence(Spar_red1)|]==> strip"
apply (unfold confluence_def strip_def)
apply (rule impI [THEN allI, THEN allI])
apply (erule Spar_red.induct)
apply fast
apply (fast intro: Spar_red.trans)
done


lemma strip_lemma_l: 
    "strip==> confluence(Spar_red)"
apply (unfold confluence_def strip_def)
apply (rule impI [THEN allI, THEN allI])
apply (erule Spar_red.induct)
apply blast
apply clarify
apply (blast intro: Spar_red.trans)
done

(* ------------------------------------------------------------------------- *)
(*      Confluence                                                           *)
(* ------------------------------------------------------------------------- *)


lemma parallel_moves: "confluence(Spar_red1)"
apply (unfold confluence_def)
apply clarify
apply (frule simulation)
apply (frule_tac n = "z" in simulation)
apply clarify
apply (frule_tac v = "va" in paving)
apply (force intro: completeness)+
done

lemmas confluence_parallel_reduction =
      parallel_moves [THEN strip_lemma_r, THEN strip_lemma_l, standard]

lemma lemma1: "[|confluence(Spar_red)|]==> confluence(Sred)"
apply (unfold confluence_def, blast intro: par_red_red red_par_red)
done

lemmas confluence_beta_reduction =
       confluence_parallel_reduction [THEN lemma1, standard]


(**** Conversion ****)

consts
  Sconv1        :: "i"
  "<-1->"       :: "[i,i]=>o"   (infixl 50)
  Sconv         :: "i"
  "<--->"       :: "[i,i]=>o"   (infixl 50)

translations
  "a<-1->b"    == "<a,b> \<in> Sconv1"
  "a<--->b"    == "<a,b> \<in> Sconv"
  
inductive
  domains       "Sconv1" <= "lambda*lambda"
  intros
    red1:        "m -1-> n ==> m<-1->n"
    expl:        "n -1-> m ==> m<-1->n"
  type_intros    red1D1 red1D2 lambda.intros bool_typechecks

declare Sconv1.intros [intro]

inductive
  domains       "Sconv" <= "lambda*lambda"
  intros
    one_step:    "m<-1->n  ==> m<--->n"
    refl:        "m \<in> lambda ==> m<--->m"
    trans:       "[|m<--->n; n<--->p|] ==> m<--->p"
  type_intros    Sconv1.dom_subset [THEN subsetD] lambda.intros bool_typechecks

declare Sconv.intros [intro]

lemma conv_sym: "m<--->n ==> n<--->m"
apply (erule Sconv.induct)
apply (erule Sconv1.induct)
apply blast+
done

(* ------------------------------------------------------------------------- *)
(*      Church_Rosser Theorem                                                *)
(* ------------------------------------------------------------------------- *)

lemma Church_Rosser: "m<--->n ==> \<exists>p.(m --->p) & (n ---> p)"
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

