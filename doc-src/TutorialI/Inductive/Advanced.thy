(* ID:         $Id$ *)
theory Advanced = Main:

datatype 'f "term" = Apply 'f "'f term list"

consts terms :: "'f set \<Rightarrow> 'f term set"
inductive "terms F"
intros
step[intro]: "\<lbrakk>\<forall>t \<in> set term_list. t \<in> terms F;  f \<in> F\<rbrakk>
              \<Longrightarrow> (Apply f term_list) \<in> terms F"


lemma "F\<subseteq>G \<Longrightarrow> terms F \<subseteq> terms G"
apply clarify
apply (erule terms.induct)
apply blast
done

consts term_type :: "('f \<Rightarrow> 't list * 't) \<Rightarrow> ('f term * 't)set"
inductive "term_type sig"
intros
step[intro]: "\<lbrakk>\<forall>et \<in> set term_type_list. et \<in> term_type sig; 
               sig f = (map snd term_type_list, rtype)\<rbrakk>
              \<Longrightarrow> (Apply f (map fst term_type_list), rtype) \<in> term_type sig"

consts term_type' :: "('f \<Rightarrow> 't list * 't) \<Rightarrow> ('f term * 't)set"
inductive "term_type' sig"
intros
step[intro]: "\<lbrakk>term_type_list \<in> lists(term_type' sig); 
                 sig f = (map snd term_type_list, rtype)\<rbrakk>
              \<Longrightarrow> (Apply f (map fst term_type_list), rtype) \<in> term_type' sig"
monos lists_mono


lemma "term_type sig \<subseteq> term_type' sig"
apply clarify
apply (erule term_type.induct)
apply auto
done

lemma "term_type' sig \<subseteq> term_type sig"
apply clarify
apply (erule term_type'.induct)
apply auto
done

end

