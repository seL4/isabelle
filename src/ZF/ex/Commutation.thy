(*  Title:      HOL/Lambda/Commutation.thy
    ID:         $Id$
    Author:     Tobias Nipkow & Sidi Ould Ehmety
    Copyright   1995  TU Muenchen

Commutation theory for proving the Church Rosser theorem
	ported from Isabelle/HOL  by Sidi Ould Ehmety
*)

theory Commutation = Main:

constdefs
  square  :: "[i, i, i, i] => o"
   "square(r,s,t,u) ==
     (\<forall>a b. <a,b> \<in> r --> (\<forall>c. <a, c> \<in> s --> (\<exists>x. <b,x> \<in> t & <c,x> \<in> u)))"

  commute :: "[i, i] => o"
   "commute(r,s) == square(r,s,s,r)"

  diamond :: "i=>o"
   "diamond(r)   == commute(r, r)"

  strip :: "i=>o"
   "strip(r) == commute(r^*, r)"

  Church_Rosser :: "i => o"
   "Church_Rosser(r) == (\<forall>x y. <x,y> \<in>  (r Un converse(r))^* -->
	 	 	 (\<exists>z. <x,z> \<in> r^* & <y,z> \<in> r^*))"
  confluent :: "i=>o"
   "confluent(r) == diamond(r^*)"


lemma square_sym: "square(r,s,t,u) ==> square(s,r,u,t)"
by (unfold square_def, blast)

lemma square_subset: "[| square(r,s,t,u); t \<subseteq> t' |] ==> square(r,s,t',u)"
by (unfold square_def, blast)


lemma square_rtrancl [rule_format]: 
     "square(r,s,s,t) --> field(s)<=field(t) --> square(r^*,s,s,t^*)"
apply (unfold square_def)
apply clarify
apply (erule rtrancl_induct)
apply (blast intro: rtrancl_refl)
apply (blast intro: rtrancl_into_rtrancl)
done

(* A special case of square_rtrancl_on *)
lemma diamond_strip: 
 "diamond(r) ==> strip(r)"
apply (unfold diamond_def commute_def strip_def)
apply (rule square_rtrancl)
apply simp_all
done

(*** commute ***)

lemma commute_sym: 
    "commute(r,s) ==> commute(s,r)"
by (unfold commute_def, blast intro: square_sym)

lemma commute_rtrancl [rule_format]: 
    "commute(r,s) ==> field(r)=field(s) --> commute(r^*,s^*)"
apply (unfold commute_def)
apply clarify
apply (rule square_rtrancl)
apply (rule square_sym [THEN square_rtrancl, THEN square_sym]) 
apply (simp_all add: rtrancl_field)
done


lemma confluentD: "confluent(r) ==> diamond(r^*)"
by (simp add: confluent_def)

lemma strip_confluent: "strip(r) ==> confluent(r)"
apply (unfold strip_def confluent_def diamond_def)
apply (drule commute_rtrancl)
apply (simp_all add: rtrancl_field)
done

lemma commute_Un: "[| commute(r,t); commute(s,t) |] ==> commute(r Un s, t)"
by (unfold commute_def square_def, blast)

lemma diamond_Un: 
     "[| diamond(r); diamond(s); commute(r, s) |] ==> diamond(r Un s)"
by (unfold diamond_def, blast intro: commute_Un commute_sym) 

lemma diamond_confluent: 
    "diamond(r) ==> confluent(r)"
apply (unfold diamond_def confluent_def)
apply (erule commute_rtrancl)
apply simp
done

lemma confluent_Un: 
 "[| confluent(r); confluent(s); commute(r^*, s^*); 
     relation(r); relation(s) |] ==> confluent(r Un s)"
apply (unfold confluent_def)
apply (rule rtrancl_Un_rtrancl [THEN subst])
apply auto
apply (blast dest: diamond_Un intro: diamond_confluent [THEN confluentD])
done


lemma diamond_to_confluence: 
     "[| diamond(r); s \<subseteq> r; r<= s^* |] ==> confluent(s)"
apply (drule rtrancl_subset [symmetric])
apply assumption
apply (simp_all add: confluent_def)
apply (blast intro: diamond_confluent [THEN confluentD])
done


(*** Church_Rosser ***)

lemma Church_Rosser1: 
     "Church_Rosser(r) ==> confluent(r)"
apply (unfold confluent_def Church_Rosser_def square_def 
              commute_def diamond_def)
apply auto
apply (drule converseI)
apply (simp (no_asm_use) add: rtrancl_converse [symmetric])
apply (drule_tac x = "b" in spec)
apply (drule_tac x1 = "c" in spec [THEN mp])
apply (rule_tac b = "a" in rtrancl_trans)
apply (blast intro: rtrancl_mono [THEN subsetD])+
done


lemma Church_Rosser2: 
     "confluent(r) ==> Church_Rosser(r)"
apply (unfold confluent_def Church_Rosser_def square_def 
              commute_def diamond_def)
apply auto
apply (frule fieldI1)
apply (simp add: rtrancl_field)
apply (erule rtrancl_induct)
apply auto
apply (blast intro: rtrancl_refl)
apply (blast del: rtrancl_refl intro: r_into_rtrancl rtrancl_trans)+
done


lemma Church_Rosser: "Church_Rosser(r) <-> confluent(r)"
by (blast intro: Church_Rosser1 Church_Rosser2)

end          
