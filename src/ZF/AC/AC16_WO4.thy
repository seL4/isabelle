(*  Title:      ZF/AC/AC16_WO4.thy
    ID:         $Id$
    Author:     Krzysztof Grabczewski

The proof of AC16(n, k) ==> WO4(n-k)

Tidied (using locales) by LCP
*)

theory AC16_WO4 = AC16_lemmas:

(* ********************************************************************** *)
(* The case of finite set                                                 *)
(* ********************************************************************** *)

lemma lemma1:
     "[| Finite(A); 0<m; m \<in> nat |] 
      ==> \<exists>a f. Ord(a) & domain(f) = a &   
                (\<Union>b<a. f`b) = A & (\<forall>b<a. f`b \<lesssim> m)"
apply (unfold Finite_def)
apply (erule bexE)
apply (drule eqpoll_sym [THEN eqpoll_def [THEN def_imp_iff, THEN iffD1]])
apply (erule exE)
apply (rule_tac x = n in exI)
apply (rule_tac x = "\<lambda>i \<in> n. {f`i}" in exI)
apply (simp add: ltD bij_def surj_def)
apply (fast intro!: ltI nat_into_Ord lam_funtype [THEN domain_of_fun] 
               singleton_eqpoll_1 [THEN eqpoll_imp_lepoll, THEN lepoll_trans] 
                    nat_1_lepoll_iff [THEN iffD2]
          elim!: apply_type ltE)
done

(* ********************************************************************** *)
(* The case of infinite set                                               *)
(* ********************************************************************** *)

(* well_ord(x,r) ==> well_ord({{y,z}. y \<in> x}, Something(x,z))  **)
lemmas well_ord_paired = paired_bij [THEN bij_is_inj, THEN well_ord_rvimage]

lemma lepoll_trans1: "[| A \<lesssim> B; ~ A \<lesssim> C |] ==> ~ B \<lesssim> C"
by (blast intro: lepoll_trans)

(* ********************************************************************** *)
(* There exists a well ordered set y such that ...                        *)
(* ********************************************************************** *)

lemmas lepoll_paired = paired_eqpoll [THEN eqpoll_sym, THEN eqpoll_imp_lepoll];

lemma lemma2: "\<exists>y R. well_ord(y,R) & x Int y = 0 & ~y \<lesssim> z & ~Finite(y)"
apply (rule_tac x = "{{a,x}. a \<in> nat Un Hartog (z) }" in exI)
apply (rule well_ord_Un [OF Ord_nat [THEN well_ord_Memrel] 
                         Ord_Hartog [THEN well_ord_Memrel], THEN exE])
apply (blast intro!: Ord_Hartog well_ord_Memrel well_ord_paired
                      lepoll_trans1 [OF _ not_Hartog_lepoll_self]
                      lepoll_trans [OF subset_imp_lepoll lepoll_paired]
       elim!: nat_not_Finite [THEN notE]
       elim: mem_asym 
       dest!: Un_upper1 [THEN subset_imp_lepoll, THEN lepoll_Finite]
              lepoll_paired [THEN lepoll_Finite])
done

lemma infinite_Un: "~Finite(B) ==> ~Finite(A Un B)"
by (blast intro: subset_Finite)

(* ********************************************************************** *)
(* There is a v \<in> s(u) such that k \<lesssim> x Int y (in our case succ(k))    *)
(* The idea of the proof is the following \<in>                               *)
(* Suppose not, i.e. every element of s(u) has exactly k-1 elements of y   *)
(* Thence y is less than or equipollent to {v \<in> Pow(x). v \<approx> n#-k}      *)
(*   We have obtained this result in two steps \<in>                          *)
(*   1. y is less than or equipollent to {v \<in> s(u). a \<subseteq> v}                  *)
(*      where a is certain k-2 element subset of y                        *)
(*   2. {v \<in> s(u). a \<subseteq> v} is less than or equipollent                       *)
(*      to {v \<in> Pow(x). v \<approx> n-k}                                       *)
(* ********************************************************************** *)

(*Proof simplified by LCP*)
lemma succ_not_lepoll_lemma:
     "[| ~(\<exists>x \<in> A. f`x=y); f \<in> inj(A, B); y \<in> B |]   
      ==> (\<lambda>a \<in> succ(A). if(a=A, y, f`a)) \<in> inj(succ(A), B)"
apply (rule_tac d = "%z. if (z=y, A, converse (f) `z) " in lam_injective)
apply (force simp add: inj_is_fun [THEN apply_type])
(*this preliminary simplification prevents looping somehow*)
apply (simp (no_asm_simp))
apply force
done

lemma succ_not_lepoll_imp_eqpoll: "[| ~A \<approx> B; A \<lesssim> B |] ==> succ(A) \<lesssim> B"
apply (unfold lepoll_def eqpoll_def bij_def surj_def)
apply (fast elim!: succ_not_lepoll_lemma inj_is_fun)
done


(* ********************************************************************** *)
(* There is a k-2 element subset of y                                     *)
(* ********************************************************************** *)

lemmas ordertype_eqpoll =
       ordermap_bij [THEN exI [THEN eqpoll_def [THEN def_imp_iff, THEN iffD2]]]

lemma cons_cons_subset:
     "[| a \<subseteq> y; b \<in> y-a; u \<in> x |] ==> cons(b, cons(u, a)) \<in> Pow(x Un y)"
by fast

lemma cons_cons_eqpoll:
     "[| a \<approx> k; a \<subseteq> y; b \<in> y-a; u \<in> x; x Int y = 0 |]    
      ==> cons(b, cons(u, a)) \<approx> succ(succ(k))"
by (fast intro!: cons_eqpoll_succ)

lemma set_eq_cons:
     "[| succ(k) \<approx> A; k \<approx> B; B \<subseteq> A; a \<in> A-B; k \<in> nat |] ==> A = cons(a, B)"
apply (rule equalityI)
prefer 2 apply fast
apply (rule Diff_eq_0_iff [THEN iffD1])
apply (rule equals0I)
apply (drule eqpoll_sym [THEN eqpoll_imp_lepoll])
apply (drule eqpoll_sym [THEN cons_eqpoll_succ], fast)
apply (drule cons_eqpoll_succ, fast)
apply (fast elim!: lepoll_trans [THEN lepoll_trans, THEN succ_lepoll_natE,
         OF eqpoll_sym [THEN eqpoll_imp_lepoll] subset_imp_lepoll])
done

lemma cons_eqE: "[| cons(x,a) = cons(y,a); x \<notin> a |] ==> x = y "
by (fast elim!: equalityE)

lemma eq_imp_Int_eq: "A = B ==> A Int C = B Int C"
by blast

(* ********************************************************************** *)
(* some arithmetic                                                        *)
(* ********************************************************************** *)

lemma eqpoll_sum_imp_Diff_lepoll_lemma [rule_format]:
     "[| k \<in> nat; m \<in> nat |] 
      ==> \<forall>A B. A \<approx> k #+ m & k \<lesssim> B & B \<subseteq> A --> A-B \<lesssim> m"
apply (induct_tac "k")
apply (simp add: add_0)
apply (blast intro: eqpoll_imp_lepoll lepoll_trans
                    Diff_subset [THEN subset_imp_lepoll])
apply (intro allI impI)
apply (rule succ_lepoll_imp_not_empty [THEN not_emptyE], fast)
apply (erule_tac x = "A - {xa}" in allE)
apply (erule_tac x = "B - {xa}" in allE)
apply (erule impE)
apply (simp add: add_succ)
apply (fast intro!: Diff_sing_eqpoll lepoll_Diff_sing) 
apply (subgoal_tac "A - {xa} - (B - {xa}) = A - B", simp)
apply blast 
done

lemma eqpoll_sum_imp_Diff_lepoll:
     "[| A \<approx> succ(k #+ m); B \<subseteq> A; succ(k) \<lesssim> B;  k \<in> nat; m \<in> nat |]   
      ==> A-B \<lesssim> m"
apply (simp only: add_succ [symmetric]) 
apply (blast intro: eqpoll_sum_imp_Diff_lepoll_lemma) 
done

(* ********************************************************************** *)
(* similar properties for \<approx>                                          *)
(* ********************************************************************** *)

lemma eqpoll_sum_imp_Diff_eqpoll_lemma [rule_format]:
     "[| k \<in> nat; m \<in> nat |] 
      ==> \<forall>A B. A \<approx> k #+ m & k \<approx> B & B \<subseteq> A --> A-B \<approx> m"
apply (induct_tac "k")
apply (force dest!: eqpoll_sym [THEN eqpoll_imp_lepoll, THEN lepoll_0_is_0])
apply (intro allI impI)
apply (rule succ_lepoll_imp_not_empty [THEN not_emptyE])
apply (fast elim!: eqpoll_imp_lepoll)
apply (erule_tac x = "A - {xa}" in allE)
apply (erule_tac x = "B - {xa}" in allE)
apply (erule impE)
apply (force intro: eqpoll_sym intro!: Diff_sing_eqpoll)
apply (subgoal_tac "A - {xa} - (B - {xa}) = A - B", simp)
apply blast 
done

lemma eqpoll_sum_imp_Diff_eqpoll:
     "[| A \<approx> succ(k #+ m); B \<subseteq> A; succ(k) \<approx> B; k \<in> nat; m \<in> nat |]   
      ==> A-B \<approx> m"
apply (simp only: add_succ [symmetric]) 
apply (blast intro: eqpoll_sum_imp_Diff_eqpoll_lemma) 
done


(* ********************************************************************** *)
(* LL can be well ordered                                                 *)
(* ********************************************************************** *)

lemma subsets_lepoll_0_eq_unit: "{x \<in> Pow(X). x \<lesssim> 0} = {0}"
by (fast dest!: lepoll_0_is_0 intro!: lepoll_refl)

lemma subsets_lepoll_succ:
     "n \<in> nat ==> {z \<in> Pow(y). z \<lesssim> succ(n)} =   
                  {z \<in> Pow(y). z \<lesssim> n} Un {z \<in> Pow(y). z \<approx> succ(n)}"
by (blast intro: leI le_imp_lepoll nat_into_Ord 
                    lepoll_trans eqpoll_imp_lepoll
          dest!: lepoll_succ_disj)

lemma Int_empty:
     "n \<in> nat ==> {z \<in> Pow(y). z \<lesssim> n} Int {z \<in> Pow(y). z \<approx> succ(n)} = 0"
by (blast intro: eqpoll_sym [THEN eqpoll_imp_lepoll, THEN lepoll_trans] 
                 succ_lepoll_natE)


locale (open) AC16 =
  fixes x and y and k and l and m and t_n and R and MM and LL and GG and s 
  defines k_def:     "k   == succ(l)"
      and MM_def:    "MM  == {v \<in> t_n. succ(k) \<lesssim> v Int y}"
      and LL_def:    "LL  == {v Int y. v \<in> MM}"
      and GG_def:    "GG  == \<lambda>v \<in> LL. (THE w. w \<in> MM & v \<subseteq> w) - v"
      and s_def:     "s(u) == {v \<in> t_n. u \<in> v & k \<lesssim> v Int y}"
  assumes all_ex:    "\<forall>z \<in> {z \<in> Pow(x Un y) . z \<approx> succ(k)}.
	               \<exists>! w. w \<in> t_n & z \<subseteq> w "
    and disjoint[iff]:  "x Int y = 0"
    and "includes":  "t_n \<subseteq> {v \<in> Pow(x Un y). v \<approx> succ(k #+ m)}"
    and WO_R[iff]:      "well_ord(y,R)"
    and lnat[iff]:      "l \<in> nat"
    and mnat[iff]:      "m \<in> nat"
    and mpos[iff]:      "0<m"
    and Infinite[iff]:  "~ Finite(y)"
    and noLepoll:  "~ y \<lesssim> {v \<in> Pow(x). v \<approx> m}"

lemma (in AC16) knat [iff]: "k \<in> nat"
by (simp add: k_def)


(* ********************************************************************** *)
(*   1. y is less than or equipollent to {v \<in> s(u). a \<subseteq> v}                *)
(*      where a is certain k-2 element subset of y                        *)
(* ********************************************************************** *)

lemma (in AC16) Diff_Finite_eqpoll: "[| l \<approx> a; a \<subseteq> y |] ==> y - a \<approx> y"
apply (insert WO_R Infinite lnat)
apply (rule eqpoll_trans) 
apply (rule Diff_lesspoll_eqpoll_Card) 
apply (erule well_ord_cardinal_eqpoll [THEN eqpoll_sym])
apply (blast intro: lesspoll_trans1
            intro!: Card_cardinal  
                    Card_cardinal [THEN Card_is_Ord, THEN nat_le_infinite_Ord,
                                   THEN le_imp_lepoll] 
            dest: well_ord_cardinal_eqpoll 
		   eqpoll_sym  eqpoll_imp_lepoll
                   n_lesspoll_nat [THEN lesspoll_trans2]
                   well_ord_cardinal_eqpoll [THEN eqpoll_sym, 
                          THEN eqpoll_imp_lepoll, THEN lepoll_infinite])+
done


lemma (in AC16) s_subset: "s(u) \<subseteq> t_n"
by (unfold s_def, blast)

lemma (in AC16) sI: 
      "[| w \<in> t_n; cons(b,cons(u,a)) \<subseteq> w; a \<subseteq> y; b \<in> y-a; l \<approx> a |] 
       ==> w \<in> s(u)"
apply (unfold s_def succ_def k_def)
apply (blast intro!: eqpoll_imp_lepoll [THEN cons_lepoll_cong]
             intro: subset_imp_lepoll lepoll_trans)
done

lemma (in AC16) in_s_imp_u_in: "v \<in> s(u) ==> u \<in> v"
by (unfold s_def, blast)


lemma (in AC16) ex1_superset_a:
     "[| l \<approx> a;  a \<subseteq> y;  b \<in> y - a;  u \<in> x |]   
      ==> \<exists>! c. c \<in> s(u) & a \<subseteq> c & b \<in> c"
apply (rule all_ex [simplified k_def, THEN ballE])
 apply (erule ex1E)
 apply (rule_tac a = w in ex1I, blast intro: sI)
 apply (blast dest: s_subset [THEN subsetD] in_s_imp_u_in)
apply (blast del: PowI 
             intro!: cons_cons_subset eqpoll_sym [THEN cons_cons_eqpoll])
done

lemma (in AC16) the_eq_cons:
     "[| \<forall>v \<in> s(u). succ(l) \<approx> v Int y;   
         l \<approx> a;  a \<subseteq> y;  b \<in> y - a;  u \<in> x |]    
      ==> (THE c. c \<in> s(u) & a \<subseteq> c & b \<in> c) Int y = cons(b, a)"
apply (frule ex1_superset_a [THEN theI], assumption+)
apply (rule set_eq_cons)
apply (fast+)
done

lemma (in AC16) y_lepoll_subset_s:
     "[| \<forall>v \<in> s(u). succ(l) \<approx> v Int y;   
         l \<approx> a;  a \<subseteq> y;  u \<in> x |]   
      ==> y \<lesssim> {v \<in> s(u). a \<subseteq> v}"
apply (rule Diff_Finite_eqpoll [THEN eqpoll_sym, THEN eqpoll_imp_lepoll, 
                                THEN lepoll_trans],  fast+)
apply (rule_tac  f3 = "\<lambda>b \<in> y-a. THE c. c \<in> s (u) & a \<subseteq> c & b \<in> c" 
        in exI [THEN lepoll_def [THEN def_imp_iff, THEN iffD2]])
apply (simp add: inj_def)
apply (rule conjI)
apply (rule lam_type)
apply (frule ex1_superset_a [THEN theI], fast+, clarify)
apply (rule cons_eqE [of _ a])
apply (drule_tac A = "THE c. ?P (c) " and C = y in eq_imp_Int_eq)
apply (simp_all add: the_eq_cons)
done


(* ********************************************************************** *)
(* back to the second part                                                *)
(* ********************************************************************** *)


(*relies on the disjointness of x, y*)
lemma (in AC16) x_imp_not_y [dest]: "a \<in> x ==> a \<notin> y"
by (blast dest:  disjoint [THEN equalityD1, THEN subsetD, OF IntI])

lemma (in AC16) w_Int_eq_w_Diff:
     "w \<subseteq> x Un y ==> w Int (x - {u}) = w - cons(u, w Int y)" 
by blast

lemma (in AC16) w_Int_eqpoll_m:
     "[| w \<in> {v \<in> s(u). a \<subseteq> v};   
         l \<approx> a;  u \<in> x;   
         \<forall>v \<in> s(u). succ(l) \<approx> v Int y |] 
      ==> w Int (x - {u}) \<approx> m"
apply (erule CollectE)
apply (subst w_Int_eq_w_Diff)
apply (fast dest!: s_subset [THEN subsetD] 
                   "includes" [simplified k_def, THEN subsetD])
apply (blast dest: s_subset [THEN subsetD] 
                   "includes" [simplified k_def, THEN subsetD] 
             dest: eqpoll_sym [THEN cons_eqpoll_succ, THEN eqpoll_sym] 
                   in_s_imp_u_in
            intro!: eqpoll_sum_imp_Diff_eqpoll)
done


(* ********************************************************************** *)
(*   2. {v \<in> s(u). a \<subseteq> v} is less than or equipollent                       *)
(*      to {v \<in> Pow(x). v \<approx> n-k}                                       *)
(* ********************************************************************** *)

lemma (in AC16) eqpoll_m_not_empty: "a \<approx> m ==> a \<noteq> 0"
apply (insert mpos)
apply (fast elim!: zero_lt_natE dest!: eqpoll_succ_imp_not_empty)
done

lemma (in AC16) cons_cons_in:
     "[| z \<in> xa Int (x - {u}); l \<approx> a; a \<subseteq> y; u \<in> x |]   
      ==> \<exists>! w. w \<in> t_n & cons(z, cons(u, a)) \<subseteq> w"
apply (rule all_ex [THEN bspec])
apply (unfold k_def)
apply (fast intro!: cons_eqpoll_succ elim: eqpoll_sym)
done

lemma (in AC16) subset_s_lepoll_w:
     "[| \<forall>v \<in> s(u). succ(l) \<approx> v Int y; a \<subseteq> y; l \<approx> a; u \<in> x |]   
      ==> {v \<in> s(u). a \<subseteq> v} \<lesssim> {v \<in> Pow(x). v \<approx> m}"
apply (rule_tac f3 = "\<lambda>w \<in> {v \<in> s (u) . a \<subseteq> v}. w Int (x - {u})" 
       in exI [THEN lepoll_def [THEN def_imp_iff, THEN iffD2]])
apply (simp add: inj_def)
apply (intro conjI lam_type CollectI)
  apply fast
 apply (blast intro: w_Int_eqpoll_m) 
apply (intro ballI impI)
(** LEVEL 8 **)
apply (rule w_Int_eqpoll_m [THEN eqpoll_m_not_empty, THEN not_emptyE])
apply (blast, assumption+)
apply (drule equalityD1 [THEN subsetD], assumption)
apply (frule cons_cons_in, assumption+)
apply (blast dest: ex1_two_eq intro: s_subset [THEN subsetD] in_s_imp_u_in)+
done


(* ********************************************************************** *)
(* well_ord_subsets_lepoll_n                                              *)
(* ********************************************************************** *)

lemma (in AC16) well_ord_subsets_eqpoll_n:
     "n \<in> nat ==> \<exists>S. well_ord({z \<in> Pow(y) . z \<approx> succ(n)}, S)"
apply (rule WO_R [THEN well_ord_infinite_subsets_eqpoll_X,
                  THEN eqpoll_def [THEN def_imp_iff, THEN iffD1], THEN exE])
apply (fast intro: bij_is_inj [THEN well_ord_rvimage])+
done

lemma (in AC16) well_ord_subsets_lepoll_n:
     "n \<in> nat ==> \<exists>R. well_ord({z \<in> Pow(y). z \<lesssim> n}, R)"
apply (induct_tac "n")
apply (force intro!: well_ord_unit simp add: subsets_lepoll_0_eq_unit)
apply (erule exE)
apply (rule well_ord_subsets_eqpoll_n [THEN exE], assumption)
apply (simp add: subsets_lepoll_succ)
apply (drule well_ord_radd, assumption)
apply (erule Int_empty [THEN disj_Un_eqpoll_sum,
                  THEN eqpoll_def [THEN def_imp_iff, THEN iffD1], THEN exE])
apply (fast elim!: bij_is_inj [THEN well_ord_rvimage])
done


lemma (in AC16) LL_subset: "LL \<subseteq> {z \<in> Pow(y). z \<lesssim> succ(k #+ m)}"
apply (unfold LL_def MM_def)
apply (insert "includes")
apply (blast intro: subset_imp_lepoll eqpoll_imp_lepoll lepoll_trans)
done

lemma (in AC16) well_ord_LL: "\<exists>S. well_ord(LL,S)"
apply (rule well_ord_subsets_lepoll_n [THEN exE, of "succ(k#+m)"])
apply simp 
apply (blast intro: well_ord_subset [OF _ LL_subset])
done

(* ********************************************************************** *)
(* every element of LL is a contained in exactly one element of MM        *)
(* ********************************************************************** *)

lemma (in AC16) unique_superset_in_MM:
     "v \<in> LL ==> \<exists>! w. w \<in> MM & v \<subseteq> w"
apply (unfold MM_def LL_def, safe, fast)
apply (rule lepoll_imp_eqpoll_subset [THEN exE], assumption)
apply (rule_tac x = x in all_ex [THEN ballE]) 
apply (blast intro: eqpoll_sym)+
done


(* ********************************************************************** *)
(* The function GG satisfies the conditions of WO4                        *)
(* ********************************************************************** *)

(* ********************************************************************** *)
(* The union of appropriate values is the whole x                         *)
(* ********************************************************************** *)

lemma (in AC16) Int_in_LL: "w \<in> MM ==> w Int y \<in> LL"
by (unfold LL_def, fast)

lemma (in AC16) in_LL_eq_Int: 
     "v \<in> LL ==> v = (THE x. x \<in> MM & v \<subseteq> x) Int y"
apply (unfold LL_def, clarify)
apply (subst unique_superset_in_MM [THEN the_equality2])
apply (auto simp add: Int_in_LL)
done

lemma (in AC16) unique_superset1: "a \<in> LL \<Longrightarrow> (THE x. x \<in> MM \<and> a \<subseteq> x) \<in> MM"
by (erule unique_superset_in_MM [THEN theI, THEN conjunct1]) 

lemma (in AC16) the_in_MM_subset:
     "v \<in> LL ==> (THE x. x \<in> MM & v \<subseteq> x) \<subseteq> x Un y"
apply (drule unique_superset1)
apply (unfold MM_def)
apply (fast dest!: unique_superset1 "includes" [THEN subsetD])
done

lemma (in AC16) GG_subset: "v \<in> LL ==> GG ` v \<subseteq> x"
apply (unfold GG_def)
apply (frule the_in_MM_subset)
apply (frule in_LL_eq_Int)
apply (force elim: equalityE)
done

lemma (in AC16) nat_lepoll_ordertype: "nat \<lesssim> ordertype(y, R)"
apply (rule nat_le_infinite_Ord [THEN le_imp_lepoll]) 
 apply (rule Ord_ordertype [OF WO_R]) 
apply (rule ordertype_eqpoll [THEN eqpoll_imp_lepoll, THEN lepoll_infinite]) 
 apply (rule WO_R) 
apply (rule Infinite) 
done

lemma (in AC16) ex_subset_eqpoll_n: "n \<in> nat ==> \<exists>z. z \<subseteq> y & n \<approx> z"
apply (erule nat_lepoll_imp_ex_eqpoll_n)
apply (rule lepoll_trans [OF nat_lepoll_ordertype]) 
apply (rule ordertype_eqpoll [THEN eqpoll_sym, THEN eqpoll_imp_lepoll]) 
apply (rule WO_R) 
done


lemma (in AC16) exists_proper_in_s: "u \<in> x ==> \<exists>v \<in> s(u). succ(k) \<lesssim> v Int y"
apply (rule ccontr)
apply (subgoal_tac "\<forall>v \<in> s (u) . k \<approx> v Int y")
prefer 2 apply (simp add: s_def, blast intro: succ_not_lepoll_imp_eqpoll)
apply (unfold k_def)
apply (insert all_ex "includes" lnat)
apply (rule ex_subset_eqpoll_n [THEN exE], assumption)
apply (rule noLepoll [THEN notE])
apply (blast intro: lepoll_trans [OF y_lepoll_subset_s subset_s_lepoll_w])
done

lemma (in AC16) exists_in_MM: "u \<in> x ==> \<exists>w \<in> MM. u \<in> w"
apply (erule exists_proper_in_s [THEN bexE])
apply (unfold MM_def s_def, fast)
done

lemma (in AC16) exists_in_LL: "u \<in> x ==> \<exists>w \<in> LL. u \<in> GG`w"
apply (rule exists_in_MM [THEN bexE], assumption)
apply (rule bexI)
apply (erule_tac [2] Int_in_LL)
apply (unfold GG_def)
apply (simp add: Int_in_LL)
apply (subst unique_superset_in_MM [THEN the_equality2])
apply (fast elim!: Int_in_LL)+
done

lemma (in AC16) OUN_eq_x: "well_ord(LL,S) ==>       
      (\<Union>b<ordertype(LL,S). GG ` (converse(ordermap(LL,S)) ` b)) = x"
apply (rule equalityI)
apply (rule subsetI)
apply (erule OUN_E)
apply (rule GG_subset [THEN subsetD])
prefer 2 apply assumption
apply (blast intro: ltD  ordermap_bij [THEN bij_converse_bij, THEN bij_is_fun,
                                       THEN apply_type])
apply (rule subsetI)
apply (erule exists_in_LL [THEN bexE])
apply (force intro: ltI [OF _ Ord_ordertype]
                    ordermap_type [THEN apply_type]
             simp add: ordermap_bij [THEN bij_is_inj, THEN left_inverse])
done

(* ********************************************************************** *)
(* Every element of the family is less than or equipollent to n-k (m)     *)
(* ********************************************************************** *)

lemma (in AC16) in_MM_eqpoll_n: "w \<in> MM ==> w \<approx> succ(k #+ m)"
apply (unfold MM_def)
apply (fast dest: "includes" [THEN subsetD])
done

lemma (in AC16) in_LL_eqpoll_n: "w \<in> LL ==> succ(k) \<lesssim> w"
by (unfold LL_def MM_def, fast)

lemma (in AC16) in_LL: "w \<in> LL ==> w \<subseteq> (THE x. x \<in> MM \<and> w \<subseteq> x)"
by (erule subset_trans [OF in_LL_eq_Int [THEN equalityD1] Int_lower1])

lemma (in AC16) all_in_lepoll_m: 
      "well_ord(LL,S) ==>       
       \<forall>b<ordertype(LL,S). GG ` (converse(ordermap(LL,S)) ` b) \<lesssim> m"
apply (unfold GG_def)
apply (rule oallI)
apply (simp add: ltD ordermap_bij [THEN bij_converse_bij, THEN bij_is_fun, THEN apply_type])
apply (insert "includes")
apply (rule eqpoll_sum_imp_Diff_lepoll)
apply (blast del: subsetI
	     dest!: ltD 
	     intro!: eqpoll_sum_imp_Diff_lepoll in_LL_eqpoll_n
	     intro: in_LL   unique_superset1 [THEN in_MM_eqpoll_n] 
                    ordermap_bij [THEN bij_converse_bij, THEN bij_is_fun, 
                                  THEN apply_type])+
done

lemma (in AC16) conclusion:
     "\<exists>a f. Ord(a) & domain(f) = a & (\<Union>b<a. f ` b) = x & (\<forall>b<a. f ` b \<lesssim> m)"
apply (rule well_ord_LL [THEN exE])
apply (rename_tac S)
apply (rule_tac x = "ordertype (LL,S)" in exI)
apply (rule_tac x = "\<lambda>b \<in> ordertype(LL,S). 
                      GG ` (converse (ordermap (LL,S)) ` b)"  in exI)
apply (simp add: ltD)
apply (blast intro: lam_funtype [THEN domain_of_fun] 
                    Ord_ordertype  OUN_eq_x  all_in_lepoll_m [THEN ospec])
done


(* ********************************************************************** *)
(* The main theorem AC16(n, k) ==> WO4(n-k)                               *)
(* ********************************************************************** *)

theorem AC16_WO4: 
     "[| AC16(k #+ m, k); 0 < k; 0 < m; k \<in> nat; m \<in> nat |] ==> WO4(m)"
apply (unfold AC16_def WO4_def)
apply (rule allI)
apply (case_tac "Finite (A)")
apply (rule lemma1, assumption+)
apply (cut_tac lemma2)
apply (elim exE conjE)
apply (erule_tac x = "A Un y" in allE)
apply (frule infinite_Un, drule mp, assumption)
apply (erule zero_lt_natE, assumption, clarify)
apply (blast intro: AC16.conclusion) 
done

end
