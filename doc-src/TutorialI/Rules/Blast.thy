(* ID:         $Id$ *)
theory Blast = Main:

lemma "((\<exists>x. \<forall>y. p(x)=p(y)) = ((\<exists>x. q(x))=(\<forall>y. p(y))))   =    
       ((\<exists>x. \<forall>y. q(x)=q(y)) = ((\<exists>x. p(x))=(\<forall>y. q(y))))"
apply blast
done

text{*\noindent Until now, we have proved everything using only induction and
simplification.  Substantial proofs require more elaborate types of
inference.*}

lemma "(\<forall>x. honest(x) \<and> industrious(x) \<longrightarrow> healthy(x)) \<and>  
       \<not> (\<exists>x. grocer(x) \<and> healthy(x)) \<and> 
       (\<forall>x. industrious(x) \<and> grocer(x) \<longrightarrow> honest(x)) \<and> 
       (\<forall>x. cyclist(x) \<longrightarrow> industrious(x)) \<and> 
       (\<forall>x. \<not>healthy(x) \<and> cyclist(x) \<longrightarrow> \<not>honest(x))  
       \<longrightarrow> (\<forall>x. grocer(x) \<longrightarrow> \<not>cyclist(x))";
apply blast
done

lemma "(\<Union>i\<in>I. A(i)) \<inter> (\<Union>j\<in>J. B(j)) =
        (\<Union>i\<in>I. \<Union>j\<in>J. A(i) \<inter> B(j))"
apply blast
done

text {*
@{thm[display] mult_is_0}
 \rulename{mult_is_0}}

@{thm[display] finite_Un}
 \rulename{finite_Un}}
*};


lemma [iff]: "(xs@ys = []) = (xs=[] & ys=[])"
  apply (induct_tac xs)
  by (simp_all);

(*ideas for uses of intro, etc.: ex/Primes/is_gcd_unique?*)
end
