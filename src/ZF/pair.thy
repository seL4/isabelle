(*  Title:      ZF/pair
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

*)

header{*Ordered Pairs*}

theory pair = upair
files "simpdata.ML":

(** Lemmas for showing that <a,b> uniquely determines a and b **)

lemma singleton_eq_iff [iff]: "{a} = {b} <-> a=b"
by (rule extension [THEN iff_trans], blast)

lemma doubleton_eq_iff: "{a,b} = {c,d} <-> (a=c & b=d) | (a=d & b=c)"
by (rule extension [THEN iff_trans], blast)

lemma Pair_iff [simp]: "<a,b> = <c,d> <-> a=c & b=d"
by (simp add: Pair_def doubleton_eq_iff, blast)

lemmas Pair_inject = Pair_iff [THEN iffD1, THEN conjE, standard, elim!]

lemmas Pair_inject1 = Pair_iff [THEN iffD1, THEN conjunct1, standard]
lemmas Pair_inject2 = Pair_iff [THEN iffD1, THEN conjunct2, standard]

lemma Pair_not_0: "<a,b> ~= 0"
apply (unfold Pair_def)
apply (blast elim: equalityE)
done

lemmas Pair_neq_0 = Pair_not_0 [THEN notE, standard, elim!]

declare sym [THEN Pair_neq_0, elim!]

lemma Pair_neq_fst: "<a,b>=a ==> P"
apply (unfold Pair_def)
apply (rule consI1 [THEN mem_asym, THEN FalseE])
apply (erule subst)
apply (rule consI1)
done

lemma Pair_neq_snd: "<a,b>=b ==> P"
apply (unfold Pair_def)
apply (rule consI1 [THEN consI2, THEN mem_asym, THEN FalseE])
apply (erule subst)
apply (rule consI1 [THEN consI2])
done


subsection{*Sigma: Disjoint Union of a Family of Sets*}

text{*Generalizes Cartesian product*}

lemma Sigma_iff [simp]: "<a,b>: Sigma(A,B) <-> a:A & b:B(a)"
by (simp add: Sigma_def)

lemma SigmaI [TC,intro!]: "[| a:A;  b:B(a) |] ==> <a,b> : Sigma(A,B)"
by simp

lemmas SigmaD1 = Sigma_iff [THEN iffD1, THEN conjunct1, standard]
lemmas SigmaD2 = Sigma_iff [THEN iffD1, THEN conjunct2, standard]

(*The general elimination rule*)
lemma SigmaE [elim!]:
    "[| c: Sigma(A,B);   
        !!x y.[| x:A;  y:B(x);  c=<x,y> |] ==> P  
     |] ==> P"
by (unfold Sigma_def, blast) 

lemma SigmaE2 [elim!]:
    "[| <a,b> : Sigma(A,B);     
        [| a:A;  b:B(a) |] ==> P    
     |] ==> P"
by (unfold Sigma_def, blast) 

lemma Sigma_cong:
    "[| A=A';  !!x. x:A' ==> B(x)=B'(x) |] ==>  
     Sigma(A,B) = Sigma(A',B')"
by (simp add: Sigma_def)

(*Sigma_cong, Pi_cong NOT given to Addcongs: they cause
  flex-flex pairs and the "Check your prover" error.  Most
  Sigmas and Pis are abbreviated as * or -> *)

lemma Sigma_empty1 [simp]: "Sigma(0,B) = 0"
by blast

lemma Sigma_empty2 [simp]: "A*0 = 0"
by blast

lemma Sigma_empty_iff: "A*B=0 <-> A=0 | B=0"
by blast


subsection{*Projections @{term fst} and @{term snd}*}

lemma fst_conv [simp]: "fst(<a,b>) = a"
by (simp add: fst_def)

lemma snd_conv [simp]: "snd(<a,b>) = b"
by (simp add: snd_def)

lemma fst_type [TC]: "p:Sigma(A,B) ==> fst(p) : A"
by auto

lemma snd_type [TC]: "p:Sigma(A,B) ==> snd(p) : B(fst(p))"
by auto

lemma Pair_fst_snd_eq: "a: Sigma(A,B) ==> <fst(a),snd(a)> = a"
by auto


subsection{*The Eliminator, @{term split}*}

(*A META-equality, so that it applies to higher types as well...*)
lemma split [simp]: "split(%x y. c(x,y), <a,b>) == c(a,b)"
by (simp add: split_def)

lemma split_type [TC]:
    "[|  p:Sigma(A,B);    
         !!x y.[| x:A; y:B(x) |] ==> c(x,y):C(<x,y>)  
     |] ==> split(%x y. c(x,y), p) : C(p)"
apply (erule SigmaE, auto) 
done

lemma expand_split: 
  "u: A*B ==>    
        R(split(c,u)) <-> (ALL x:A. ALL y:B. u = <x,y> --> R(c(x,y)))"
apply (simp add: split_def, auto)
done


subsection{*A version of @{term split} for Formulae: Result Type @{typ o}*}

lemma splitI: "R(a,b) ==> split(R, <a,b>)"
by (simp add: split_def)

lemma splitE:
    "[| split(R,z);  z:Sigma(A,B);                       
        !!x y. [| z = <x,y>;  R(x,y) |] ==> P            
     |] ==> P"
apply (simp add: split_def)
apply (erule SigmaE, force) 
done

lemma splitD: "split(R,<a,b>) ==> R(a,b)"
by (simp add: split_def)

text {*
  \bigskip Complex rules for Sigma.
*}

lemma split_paired_Bex_Sigma [simp]:
     "(\<exists>z \<in> Sigma(A,B). P(z)) <-> (\<exists>x \<in> A. \<exists>y \<in> B(x). P(<x,y>))"
by blast

lemma split_paired_Ball_Sigma [simp]:
     "(\<forall>z \<in> Sigma(A,B). P(z)) <-> (\<forall>x \<in> A. \<forall>y \<in> B(x). P(<x,y>))"
by blast

ML
{*
val singleton_eq_iff = thm "singleton_eq_iff";
val doubleton_eq_iff = thm "doubleton_eq_iff";
val Pair_iff = thm "Pair_iff";
val Pair_inject = thm "Pair_inject";
val Pair_inject1 = thm "Pair_inject1";
val Pair_inject2 = thm "Pair_inject2";
val Pair_not_0 = thm "Pair_not_0";
val Pair_neq_0 = thm "Pair_neq_0";
val Pair_neq_fst = thm "Pair_neq_fst";
val Pair_neq_snd = thm "Pair_neq_snd";
val Sigma_iff = thm "Sigma_iff";
val SigmaI = thm "SigmaI";
val SigmaD1 = thm "SigmaD1";
val SigmaD2 = thm "SigmaD2";
val SigmaE = thm "SigmaE";
val SigmaE2 = thm "SigmaE2";
val Sigma_cong = thm "Sigma_cong";
val Sigma_empty1 = thm "Sigma_empty1";
val Sigma_empty2 = thm "Sigma_empty2";
val Sigma_empty_iff = thm "Sigma_empty_iff";
val fst_conv = thm "fst_conv";
val snd_conv = thm "snd_conv";
val fst_type = thm "fst_type";
val snd_type = thm "snd_type";
val Pair_fst_snd_eq = thm "Pair_fst_snd_eq";
val split = thm "split";
val split_type = thm "split_type";
val expand_split = thm "expand_split";
val splitI = thm "splitI";
val splitE = thm "splitE";
val splitD = thm "splitD";
*}

end


