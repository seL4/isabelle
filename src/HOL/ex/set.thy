(*  Title:      HOL/ex/set.thy
    ID:         $Id$
    Author:     Tobias Nipkow and Lawrence C Paulson
    Copyright   1991  University of Cambridge

Set Theory examples: Cantor's Theorem, Schroeder-Berstein Theorem, etc.
*)

theory set = Main:

text{*These two are cited in Benzmueller and Kohlhase's system description 
of LEO, CADE-15, 1998 (pages 139-143) as theorems LEO could not prove.*}

lemma "(X = Y Un Z) = (Y<=X & Z<=X & (ALL V. Y<=V & Z<=V --> X<=V))"
by blast

lemma "(X = Y Int Z) = (X<=Y & X<=Z & (ALL V. V<=Y & V<=Z --> V<=X))"
by blast

text{*trivial example of term synthesis: apparently hard for some provers!*}
lemma "a ~= b ==> a:?X & b ~: ?X"
by blast

(** Examples for the Blast_tac paper **)

text{*Union-image, called Un_Union_image on equalities.ML*}
lemma "(UN x:C. f(x) Un g(x)) = Union(f`C)  Un  Union(g`C)"
by blast

text{*Inter-image, called Int_Inter_image on equalities.ML*}
lemma "(INT x:C. f(x) Int g(x)) = Inter(f`C) Int Inter(g`C)"
by blast

text{*Singleton I.  Nice demonstration of blast_tac--and its limitations.
For some unfathomable reason, UNIV_I increases the search space greatly*}
lemma "!!S::'a set set. ALL x:S. ALL y:S. x<=y ==> EX z. S <= {z}"
by (blast del: UNIV_I)

text{*Singleton II.  variant of the benchmark above*}
lemma "ALL x:S. Union(S) <= x ==> EX z. S <= {z}"
by (blast del: UNIV_I)

text{* A unique fixpoint theorem --- fast/best/meson all fail *}

lemma "EX! x. f(g(x))=x ==> EX! y. g(f(y))=y"
apply (erule ex1E, rule ex1I, erule arg_cong)
apply (rule subst, assumption, erule allE, rule arg_cong, erule mp) 
apply (erule arg_cong) 
done



text{* Cantor's Theorem: There is no surjection from a set to its powerset. *}

text{*requires best-first search because it is undirectional*}
lemma cantor1: "~ (EX f:: 'a=>'a set. ALL S. EX x. f(x) = S)"
by best

text{*This form displays the diagonal term*}
lemma "ALL f:: 'a=>'a set. ALL x. f(x) ~= ?S(f)"
by best

text{*This form exploits the set constructs*}
lemma "?S ~: range(f :: 'a=>'a set)"
by (rule notI, erule rangeE, best)  

text{*Or just this!*}
lemma "?S ~: range(f :: 'a=>'a set)"
by best

text{* The Schroeder-Berstein Theorem *}

lemma disj_lemma: "[| -(f`X) = g`(-X);  f(a)=g(b);  a:X |] ==> b:X"
by blast

lemma surj_if_then_else:
     "-(f`X) = g`(-X) ==> surj(%z. if z:X then f(z) else g(z))"
by (simp add: surj_def, blast)

lemma bij_if_then_else: 
     "[| inj_on f X;  inj_on g (-X);  -(f`X) = g`(-X);  
         h = (%z. if z:X then f(z) else g(z)) |]        
      ==> inj(h) & surj(h)"
apply (unfold inj_on_def)
apply (simp add: surj_if_then_else)
apply (blast dest: disj_lemma sym)
done

lemma decomposition: "EX X. X = - (g`(- (f`X)))"
apply (rule exI)
apply (rule lfp_unfold)
apply (rule monoI, blast) 
done

text{*Schroeder-Bernstein Theorem*}
lemma "[| inj (f:: 'a=>'b);  inj (g:: 'b=>'a) |]  
       ==> EX h:: 'a=>'b. inj(h) & surj(h)"
apply (rule decomposition [THEN exE])
apply (rule exI)
apply (rule bij_if_then_else)
   apply (rule_tac [4] refl)
  apply (rule_tac [2] inj_on_inv)
  apply (erule subset_inj_on [OF subset_UNIV]) 
  txt{*tricky variable instantiations!*}
 apply (erule ssubst, subst double_complement)
 apply (rule subsetI, erule imageE, erule ssubst, rule rangeI) 
apply (erule ssubst, subst double_complement, erule inv_image_comp [symmetric])
done


text{*Set variable instantiation examples from 
W. W. Bledsoe and Guohui Feng, SET-VAR.
JAR 11 (3), 1993, pages 293-314.

Isabelle can prove the easy examples without any special mechanisms, but it
can't prove the hard ones.
*}

text{*Example 1, page 295.*}
lemma "(EX A. (ALL x:A. x <= (0::int)))"
by force 

text{*Example 2*}
lemma "D : F --> (EX G. (ALL A:G. EX B:F. A <= B))";
by force 

text{*Example 3*}
lemma "P(a) --> (EX A. (ALL x:A. P(x)) & (EX y. y:A))";
by force 

text{*Example 4*}
lemma "a<b & b<(c::int) --> (EX A. a~:A & b:A & c~: A)"
by force 

text{*Example 5, page 298.*}
lemma "P(f(b)) --> (EX s A. (ALL x:A. P(x)) & f(s):A)";
by force 

text{*Example 6*}
lemma "P(f(b)) --> (EX s A. (ALL x:A. P(x)) & f(s):A)";
by force 

text{*Example 7*}
lemma "EX A. a ~: A"
by force 

text{*Example 8*}
lemma "(ALL u v. u < (0::int) --> u ~= abs v) --> (EX A::int set. (ALL y. abs y ~: A) & -2 : A)"
by force  text{*not blast, which can't simplify -2<0*}

text{*Example 9 omitted (requires the reals)*}

text{*The paper has no Example 10!*}

text{*Example 11: needs a hint*}
lemma "(ALL A. 0:A & (ALL x:A. Suc(x):A) --> n:A) & 
       P(0) & (ALL x. P(x) --> P(Suc(x))) --> P(n)"
apply clarify
apply (drule_tac x="{x. P x}" in spec)
by force  

text{*Example 12*}
lemma "(ALL A. (0,0):A & (ALL x y. (x,y):A --> (Suc(x),Suc(y)):A) --> (n,m):A)
       & P(n) --> P(m)"
by auto 

text{*Example EO1: typo in article, and with the obvious fix it seems
      to require arithmetic reasoning.*}
lemma "(ALL x. (EX u. x=2*u) = (~(EX v. Suc x = 2*v))) --> 
       (EX A. ALL x. (x : A) = (Suc x ~: A))"
apply clarify 
apply (rule_tac x="{x. EX u. x = 2*u}" in exI, auto) 
apply (case_tac v, auto)
apply (drule_tac x="Suc v" and P="%x. ?a(x) ~= ?b(x)" in spec, force) 
done

end
