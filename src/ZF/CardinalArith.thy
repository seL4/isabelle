(*  Title:      ZF/CardinalArith.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Cardinal Arithmetic
*)

theory CardinalArith = Cardinal + OrderArith + ArithSimp + Finite:

constdefs

  InfCard       :: "i=>o"
    "InfCard(i) == Card(i) & nat le i"

  cmult         :: "[i,i]=>i"       (infixl "|*|" 70)
    "i |*| j == |i*j|"
  
  cadd          :: "[i,i]=>i"       (infixl "|+|" 65)
    "i |+| j == |i+j|"

  csquare_rel   :: "i=>i"
    "csquare_rel(K) ==   
	  rvimage(K*K,   
		  lam <x,y>:K*K. <x Un y, x, y>, 
		  rmult(K,Memrel(K), K*K, rmult(K,Memrel(K), K,Memrel(K))))"

  (*This def is more complex than Kunen's but it more easily proved to
    be a cardinal*)
  jump_cardinal :: "i=>i"
    "jump_cardinal(K) ==   
         UN X:Pow(K). {z. r: Pow(K*K), well_ord(X,r) & z = ordertype(X,r)}"
  
  (*needed because jump_cardinal(K) might not be the successor of K*)
  csucc         :: "i=>i"
    "csucc(K) == LEAST L. Card(L) & K<L"

syntax (xsymbols)
  "op |+|"     :: "[i,i] => i"          (infixl "\<oplus>" 65)
  "op |*|"     :: "[i,i] => i"          (infixl "\<otimes>" 70)


(*** The following really belong in OrderType ***)

lemma oadd_eq_0_iff: "\<lbrakk>Ord(i); Ord(j)\<rbrakk> \<Longrightarrow> (i ++ j) = 0 <-> i=0 & j=0"
apply (erule trans_induct3 [of j])
apply (simp_all add: oadd_Limit)
apply (simp add: Union_empty_iff Limit_def lt_def, blast)
done

lemma oadd_eq_lt_iff: "\<lbrakk>Ord(i); Ord(j)\<rbrakk> \<Longrightarrow> 0 < (i ++ j) <-> 0<i | 0<j"
by (simp add: Ord_0_lt_iff [symmetric] oadd_eq_0_iff)

lemma oadd_lt_self: "[| Ord(i);  0<j |] ==> i < i++j"
apply (rule lt_trans2) 
apply (erule le_refl) 
apply (simp only: lt_Ord2  oadd_1 [of i, symmetric]) 
apply (blast intro: succ_leI oadd_le_mono)
done

lemma oadd_LimitI: "\<lbrakk>Ord(i); Limit(j)\<rbrakk> \<Longrightarrow> Limit(i ++ j)"
apply (simp add: oadd_Limit)
apply (frule Limit_has_1 [THEN ltD])
apply (rule increasing_LimitI)
 apply (rule Ord_0_lt)
  apply (blast intro: Ord_in_Ord [OF Limit_is_Ord])
 apply (force simp add: Union_empty_iff oadd_eq_0_iff
                        Limit_is_Ord [of j, THEN Ord_in_Ord], auto)
apply (rule_tac x="succ(x)" in bexI)
 apply (simp add: ltI Limit_is_Ord [of j, THEN Ord_in_Ord])
apply (simp add: Limit_def lt_def) 
done

(*** The following really belong in Cardinal ***)

lemma lesspoll_not_refl: "~ (i lesspoll i)"
by (simp add: lesspoll_def) 

lemma lesspoll_irrefl [elim!]: "i lesspoll i ==> P"
by (simp add: lesspoll_def) 

lemma Card_Union [simp,intro,TC]: "(ALL x:A. Card(x)) ==> Card(Union(A))"
apply (rule CardI) 
 apply (simp add: Card_is_Ord) 
apply (clarify dest!: ltD)
apply (drule bspec, assumption) 
apply (frule lt_Card_imp_lesspoll, blast intro: ltI Card_is_Ord) 
apply (drule eqpoll_sym [THEN eqpoll_imp_lepoll])
apply (drule lesspoll_trans1, assumption) 
apply (subgoal_tac "B lepoll \<Union>A")
 apply (drule lesspoll_trans1, assumption, blast) 
apply (blast intro: subset_imp_lepoll) 
done

lemma Card_UN:
     "(!!x. x:A ==> Card(K(x))) ==> Card(UN x:A. K(x))" 
by (blast intro: Card_Union) 

lemma Card_OUN [simp,intro,TC]:
     "(!!x. x:A ==> Card(K(x))) ==> Card(UN x<A. K(x))"
by (simp add: OUnion_def Card_0) 

lemma n_lesspoll_nat: "n \<in> nat ==> n \<prec> nat"
apply (unfold lesspoll_def)
apply (rule conjI)
apply (erule OrdmemD [THEN subset_imp_lepoll], rule Ord_nat)
apply (rule notI)
apply (erule eqpollE)
apply (rule succ_lepoll_natE)
apply (blast intro: nat_succI [THEN OrdmemD, THEN subset_imp_lepoll] 
                    lepoll_trans, assumption) 
done

lemma in_Card_imp_lesspoll: "[| Card(K); b \<in> K |] ==> b \<prec> K"
apply (unfold lesspoll_def)
apply (simp add: Card_iff_initial)
apply (fast intro!: le_imp_lepoll ltI leI)
done

lemma succ_lepoll_imp_not_empty: "succ(x) \<lesssim> y ==> y \<noteq> 0"
by (fast dest!: lepoll_0_is_0)

lemma eqpoll_succ_imp_not_empty: "x \<approx> succ(n) ==> x \<noteq> 0"
by (fast elim!: eqpoll_sym [THEN eqpoll_0_is_0, THEN succ_neq_0])

lemma Finite_Fin_lemma [rule_format]:
     "n \<in> nat ==> \<forall>A. (A\<approx>n & A \<subseteq> X) --> A \<in> Fin(X)"
apply (induct_tac "n")
apply (rule allI)
apply (fast intro!: Fin.emptyI dest!: eqpoll_imp_lepoll [THEN lepoll_0_is_0])
apply (rule allI)
apply (rule impI)
apply (erule conjE)
apply (rule eqpoll_succ_imp_not_empty [THEN not_emptyE], assumption)
apply (frule Diff_sing_eqpoll, assumption)
apply (erule allE)
apply (erule impE, fast)
apply (drule subsetD, assumption)
apply (drule Fin.consI, assumption)
apply (simp add: cons_Diff)
done

lemma Finite_Fin: "[| Finite(A); A \<subseteq> X |] ==> A \<in> Fin(X)"
by (unfold Finite_def, blast intro: Finite_Fin_lemma) 

lemma lesspoll_lemma: 
        "[| ~ A \<prec> B; C \<prec> B |] ==> A - C \<noteq> 0"
apply (unfold lesspoll_def)
apply (fast dest!: Diff_eq_0_iff [THEN iffD1, THEN subset_imp_lepoll]
            intro!: eqpollI elim: notE 
            elim!: eqpollE lepoll_trans)
done

lemma eqpoll_imp_Finite_iff: "A \<approx> B ==> Finite(A) <-> Finite(B)"
apply (unfold Finite_def) 
apply (blast intro: eqpoll_trans eqpoll_sym) 
done

end
