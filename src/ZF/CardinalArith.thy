(*  Title:      ZF/CardinalArith.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Cardinal arithmetic -- WITHOUT the Axiom of Choice

Note: Could omit proving the algebraic laws for cardinal addition and
multiplication.  On finite cardinals these operations coincide with
addition and multiplication of natural numbers; on infinite cardinals they
coincide with union (maximum).  Either way we get most laws for free.
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


(*** The following really belong early in the development ***)

lemma relation_converse_converse [simp]:
     "relation(r) ==> converse(converse(r)) = r"
by (simp add: relation_def, blast) 

lemma relation_restrict [simp]:  "relation(restrict(r,A))"
by (simp add: restrict_def relation_def, blast) 

(*** The following really belong in Order ***)

lemma subset_ord_iso_Memrel:
     "[| f: ord_iso(A,Memrel(B),C,r); A<=B |] ==> f: ord_iso(A,Memrel(A),C,r)"
apply (frule ord_iso_is_bij [THEN bij_is_fun, THEN fun_is_rel]) 
apply (frule ord_iso_trans [OF id_ord_iso_Memrel], assumption) 
apply (simp add: right_comp_id) 
done

lemma restrict_ord_iso:
     "[| f \<in> ord_iso(i, Memrel(i), Order.pred(A,a,r), r);  a \<in> A; j < i; 
       trans[A](r) |]
      ==> restrict(f,j) \<in> ord_iso(j, Memrel(j), Order.pred(A,f`j,r), r)"
apply (frule ltD) 
apply (frule ord_iso_is_bij [THEN bij_is_fun, THEN apply_type], assumption) 
apply (frule ord_iso_restrict_pred, assumption) 
apply (simp add: pred_iff trans_pred_pred_eq lt_pred_Memrel)
apply (blast intro!: subset_ord_iso_Memrel le_imp_subset [OF leI]) 
done

lemma restrict_ord_iso2:
     "[| f \<in> ord_iso(Order.pred(A,a,r), r, i, Memrel(i));  a \<in> A; 
       j < i; trans[A](r) |]
      ==> converse(restrict(converse(f), j)) 
          \<in> ord_iso(Order.pred(A, converse(f)`j, r), r, j, Memrel(j))"
by (blast intro: restrict_ord_iso ord_iso_sym ltI)

(*** The following really belong in OrderType ***)

lemma oadd_eq_0_iff: "[| Ord(i); Ord(j) |] ==> (i ++ j) = 0 <-> i=0 & j=0"
apply (erule trans_induct3 [of j])
apply (simp_all add: oadd_Limit)
apply (simp add: Union_empty_iff Limit_def lt_def, blast)
done

lemma oadd_eq_lt_iff: "[| Ord(i); Ord(j) |] ==> 0 < (i ++ j) <-> 0<i | 0<j"
by (simp add: Ord_0_lt_iff [symmetric] oadd_eq_0_iff)

lemma oadd_lt_self: "[| Ord(i);  0<j |] ==> i < i++j"
apply (rule lt_trans2) 
apply (erule le_refl) 
apply (simp only: lt_Ord2  oadd_1 [of i, symmetric]) 
apply (blast intro: succ_leI oadd_le_mono)
done

lemma oadd_LimitI: "[| Ord(i); Limit(j) |] ==> Limit(i ++ j)"
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
apply (subgoal_tac "B \<lesssim> \<Union>A")
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


(*** Cardinal addition ***)

(** Cardinal addition is commutative **)

lemma sum_commute_eqpoll: "A+B \<approx> B+A"
apply (unfold eqpoll_def)
apply (rule exI)
apply (rule_tac c = "case(Inr,Inl)" and d = "case(Inr,Inl)" in lam_bijective)
apply auto
done

lemma cadd_commute: "i |+| j = j |+| i"
apply (unfold cadd_def)
apply (rule sum_commute_eqpoll [THEN cardinal_cong])
done

(** Cardinal addition is associative **)

lemma sum_assoc_eqpoll: "(A+B)+C \<approx> A+(B+C)"
apply (unfold eqpoll_def)
apply (rule exI)
apply (rule sum_assoc_bij)
done

(*Unconditional version requires AC*)
lemma well_ord_cadd_assoc: 
    "[| well_ord(i,ri); well_ord(j,rj); well_ord(k,rk) |]
     ==> (i |+| j) |+| k = i |+| (j |+| k)"
apply (unfold cadd_def)
apply (rule cardinal_cong)
apply (rule eqpoll_trans)
 apply (rule sum_eqpoll_cong [OF well_ord_cardinal_eqpoll eqpoll_refl])
 apply (blast intro: well_ord_radd elim:) 
apply (rule sum_assoc_eqpoll [THEN eqpoll_trans])
apply (rule eqpoll_sym)
apply (rule sum_eqpoll_cong [OF eqpoll_refl well_ord_cardinal_eqpoll])
apply (blast intro: well_ord_radd elim:) 
done

(** 0 is the identity for addition **)

lemma sum_0_eqpoll: "0+A \<approx> A"
apply (unfold eqpoll_def)
apply (rule exI)
apply (rule bij_0_sum)
done

lemma cadd_0 [simp]: "Card(K) ==> 0 |+| K = K"
apply (unfold cadd_def)
apply (simp add: sum_0_eqpoll [THEN cardinal_cong] Card_cardinal_eq)
done

(** Addition by another cardinal **)

lemma sum_lepoll_self: "A \<lesssim> A+B"
apply (unfold lepoll_def inj_def)
apply (rule_tac x = "lam x:A. Inl (x) " in exI)
apply (simp (no_asm_simp))
done

(*Could probably weaken the premises to well_ord(K,r), or removing using AC*)

lemma cadd_le_self: 
    "[| Card(K);  Ord(L) |] ==> K le (K |+| L)"
apply (unfold cadd_def)
apply (rule le_trans [OF Card_cardinal_le well_ord_lepoll_imp_Card_le])
apply assumption; 
apply (rule_tac [2] sum_lepoll_self)
apply (blast intro: well_ord_radd well_ord_Memrel Card_is_Ord)
done

(** Monotonicity of addition **)

lemma sum_lepoll_mono: 
     "[| A \<lesssim> C;  B \<lesssim> D |] ==> A + B  \<lesssim>  C + D"
apply (unfold lepoll_def)
apply (elim exE);
apply (rule_tac x = "lam z:A+B. case (%w. Inl(f`w), %y. Inr(fa`y), z)" in exI)
apply (rule_tac d = "case (%w. Inl(converse(f) `w), %y. Inr(converse(fa) `y))"
       in lam_injective)
apply (typecheck add: inj_is_fun)
apply auto
done

lemma cadd_le_mono:
    "[| K' le K;  L' le L |] ==> (K' |+| L') le (K |+| L)"
apply (unfold cadd_def)
apply (safe dest!: le_subset_iff [THEN iffD1])
apply (rule well_ord_lepoll_imp_Card_le)
apply (blast intro: well_ord_radd well_ord_Memrel)
apply (blast intro: sum_lepoll_mono subset_imp_lepoll)
done

(** Addition of finite cardinals is "ordinary" addition **)

(*????????????????upair.ML*)
lemma eq_imp_not_mem: "a=A ==> a ~: A"
apply (blast intro: elim: mem_irrefl); 
done

lemma sum_succ_eqpoll: "succ(A)+B \<approx> succ(A+B)"
apply (unfold eqpoll_def)
apply (rule exI)
apply (rule_tac c = "%z. if z=Inl (A) then A+B else z" 
            and d = "%z. if z=A+B then Inl (A) else z" in lam_bijective)
   apply (simp_all)
apply (blast dest: sym [THEN eq_imp_not_mem] elim: mem_irrefl)+
done

(*Pulling the  succ(...)  outside the |...| requires m, n: nat  *)
(*Unconditional version requires AC*)
lemma cadd_succ_lemma:
    "[| Ord(m);  Ord(n) |] ==> succ(m) |+| n = |succ(m |+| n)|"
apply (unfold cadd_def)
apply (rule sum_succ_eqpoll [THEN cardinal_cong, THEN trans])
apply (rule succ_eqpoll_cong [THEN cardinal_cong])
apply (rule well_ord_cardinal_eqpoll [THEN eqpoll_sym])
apply (blast intro: well_ord_radd well_ord_Memrel)
done

lemma nat_cadd_eq_add: "[| m: nat;  n: nat |] ==> m |+| n = m#+n"
apply (induct_tac "m")
apply (simp add: nat_into_Card [THEN cadd_0])
apply (simp add: cadd_succ_lemma nat_into_Card [THEN Card_cardinal_eq])
done


(*** Cardinal multiplication ***)

(** Cardinal multiplication is commutative **)

(*Easier to prove the two directions separately*)
lemma prod_commute_eqpoll: "A*B \<approx> B*A"
apply (unfold eqpoll_def)
apply (rule exI)
apply (rule_tac c = "%<x,y>.<y,x>" and d = "%<x,y>.<y,x>" in lam_bijective)
apply (auto ); 
done

lemma cmult_commute: "i |*| j = j |*| i"
apply (unfold cmult_def)
apply (rule prod_commute_eqpoll [THEN cardinal_cong])
done

(** Cardinal multiplication is associative **)

lemma prod_assoc_eqpoll: "(A*B)*C \<approx> A*(B*C)"
apply (unfold eqpoll_def)
apply (rule exI)
apply (rule prod_assoc_bij)
done

(*Unconditional version requires AC*)
lemma well_ord_cmult_assoc:
    "[| well_ord(i,ri); well_ord(j,rj); well_ord(k,rk) |]
     ==> (i |*| j) |*| k = i |*| (j |*| k)"
apply (unfold cmult_def)
apply (rule cardinal_cong)
apply (rule eqpoll_trans); 
 apply (rule prod_eqpoll_cong [OF well_ord_cardinal_eqpoll eqpoll_refl])
 apply (blast intro: well_ord_rmult)
apply (rule prod_assoc_eqpoll [THEN eqpoll_trans])
apply (rule eqpoll_sym); 
apply (rule prod_eqpoll_cong [OF eqpoll_refl well_ord_cardinal_eqpoll])
apply (blast intro: well_ord_rmult)
done

(** Cardinal multiplication distributes over addition **)

lemma sum_prod_distrib_eqpoll: "(A+B)*C \<approx> (A*C)+(B*C)"
apply (unfold eqpoll_def)
apply (rule exI)
apply (rule sum_prod_distrib_bij)
done

lemma well_ord_cadd_cmult_distrib:
    "[| well_ord(i,ri); well_ord(j,rj); well_ord(k,rk) |]
     ==> (i |+| j) |*| k = (i |*| k) |+| (j |*| k)"
apply (unfold cadd_def cmult_def)
apply (rule cardinal_cong)
apply (rule eqpoll_trans); 
 apply (rule prod_eqpoll_cong [OF well_ord_cardinal_eqpoll eqpoll_refl])
apply (blast intro: well_ord_radd)
apply (rule sum_prod_distrib_eqpoll [THEN eqpoll_trans])
apply (rule eqpoll_sym); 
apply (rule sum_eqpoll_cong [OF well_ord_cardinal_eqpoll 
                                well_ord_cardinal_eqpoll])
apply (blast intro: well_ord_rmult)+
done

(** Multiplication by 0 yields 0 **)

lemma prod_0_eqpoll: "0*A \<approx> 0"
apply (unfold eqpoll_def)
apply (rule exI)
apply (rule lam_bijective)
apply safe
done

lemma cmult_0 [simp]: "0 |*| i = 0"
apply (simp add: cmult_def prod_0_eqpoll [THEN cardinal_cong])
done

(** 1 is the identity for multiplication **)

lemma prod_singleton_eqpoll: "{x}*A \<approx> A"
apply (unfold eqpoll_def)
apply (rule exI)
apply (rule singleton_prod_bij [THEN bij_converse_bij])
done

lemma cmult_1 [simp]: "Card(K) ==> 1 |*| K = K"
apply (unfold cmult_def succ_def)
apply (simp add: prod_singleton_eqpoll [THEN cardinal_cong] Card_cardinal_eq)
done

(*** Some inequalities for multiplication ***)

lemma prod_square_lepoll: "A \<lesssim> A*A"
apply (unfold lepoll_def inj_def)
apply (rule_tac x = "lam x:A. <x,x>" in exI)
apply (simp (no_asm))
done

(*Could probably weaken the premise to well_ord(K,r), or remove using AC*)
lemma cmult_square_le: "Card(K) ==> K le K |*| K"
apply (unfold cmult_def)
apply (rule le_trans)
apply (rule_tac [2] well_ord_lepoll_imp_Card_le)
apply (rule_tac [3] prod_square_lepoll)
apply (simp (no_asm_simp) add: le_refl Card_is_Ord Card_cardinal_eq)
apply (blast intro: well_ord_rmult well_ord_Memrel Card_is_Ord);
done

(** Multiplication by a non-zero cardinal **)

lemma prod_lepoll_self: "b: B ==> A \<lesssim> A*B"
apply (unfold lepoll_def inj_def)
apply (rule_tac x = "lam x:A. <x,b>" in exI)
apply (simp (no_asm_simp))
done

(*Could probably weaken the premises to well_ord(K,r), or removing using AC*)
lemma cmult_le_self:
    "[| Card(K);  Ord(L);  0<L |] ==> K le (K |*| L)"
apply (unfold cmult_def)
apply (rule le_trans [OF Card_cardinal_le well_ord_lepoll_imp_Card_le])
  apply assumption; 
 apply (blast intro: well_ord_rmult well_ord_Memrel Card_is_Ord)
apply (blast intro: prod_lepoll_self ltD)
done

(** Monotonicity of multiplication **)

lemma prod_lepoll_mono:
     "[| A \<lesssim> C;  B \<lesssim> D |] ==> A * B  \<lesssim>  C * D"
apply (unfold lepoll_def)
apply (elim exE);
apply (rule_tac x = "lam <w,y>:A*B. <f`w, fa`y>" in exI)
apply (rule_tac d = "%<w,y>. <converse (f) `w, converse (fa) `y>" 
       in lam_injective)
apply (typecheck add: inj_is_fun)
apply auto
done

lemma cmult_le_mono:
    "[| K' le K;  L' le L |] ==> (K' |*| L') le (K |*| L)"
apply (unfold cmult_def)
apply (safe dest!: le_subset_iff [THEN iffD1])
apply (rule well_ord_lepoll_imp_Card_le)
 apply (blast intro: well_ord_rmult well_ord_Memrel)
apply (blast intro: prod_lepoll_mono subset_imp_lepoll)
done

(*** Multiplication of finite cardinals is "ordinary" multiplication ***)

lemma prod_succ_eqpoll: "succ(A)*B \<approx> B + A*B"
apply (unfold eqpoll_def)
apply (rule exI);
apply (rule_tac c = "%<x,y>. if x=A then Inl (y) else Inr (<x,y>)"
            and d = "case (%y. <A,y>, %z. z)" in lam_bijective)
apply safe
apply (simp_all add: succI2 if_type mem_imp_not_eq)
done

(*Unconditional version requires AC*)
lemma cmult_succ_lemma:
    "[| Ord(m);  Ord(n) |] ==> succ(m) |*| n = n |+| (m |*| n)"
apply (unfold cmult_def cadd_def)
apply (rule prod_succ_eqpoll [THEN cardinal_cong, THEN trans])
apply (rule cardinal_cong [symmetric])
apply (rule sum_eqpoll_cong [OF eqpoll_refl well_ord_cardinal_eqpoll])
apply (blast intro: well_ord_rmult well_ord_Memrel)
done

lemma nat_cmult_eq_mult: "[| m: nat;  n: nat |] ==> m |*| n = m#*n"
apply (induct_tac "m")
apply (simp (no_asm_simp))
apply (simp (no_asm_simp) add: cmult_succ_lemma nat_cadd_eq_add)
done

lemma cmult_2: "Card(n) ==> 2 |*| n = n |+| n"
apply (simp add: cmult_succ_lemma Card_is_Ord cadd_commute [of _ 0])
done

lemma sum_lepoll_prod: "2 \<lesssim> C ==> B+B \<lesssim> C*B"
apply (rule lepoll_trans); 
apply (rule sum_eq_2_times [THEN equalityD1, THEN subset_imp_lepoll]) 
apply (erule prod_lepoll_mono) 
apply (rule lepoll_refl); 
done

lemma lepoll_imp_sum_lepoll_prod: "[| A \<lesssim> B; 2 \<lesssim> A |] ==> A+B \<lesssim> A*B"
apply (blast intro: sum_lepoll_mono sum_lepoll_prod lepoll_trans lepoll_refl)
done


(*** Infinite Cardinals are Limit Ordinals ***)

(*This proof is modelled upon one assuming nat<=A, with injection
  lam z:cons(u,A). if z=u then 0 else if z : nat then succ(z) else z
  and inverse %y. if y:nat then nat_case(u, %z. z, y) else y.  \
  If f: inj(nat,A) then range(f) behaves like the natural numbers.*)
lemma nat_cons_lepoll: "nat \<lesssim> A ==> cons(u,A) \<lesssim> A"
apply (unfold lepoll_def)
apply (erule exE)
apply (rule_tac x = 
          "lam z:cons (u,A).
             if z=u then f`0 
             else if z: range (f) then f`succ (converse (f) `z) else z" 
       in exI)
apply (rule_tac d =
          "%y. if y: range(f) then nat_case (u, %z. f`z, converse(f) `y) 
                              else y" 
       in lam_injective)
apply (fast intro!: if_type apply_type intro: inj_is_fun inj_converse_fun)
apply (simp add: inj_is_fun [THEN apply_rangeI]
                 inj_converse_fun [THEN apply_rangeI]
                 inj_converse_fun [THEN apply_funtype])
done

lemma nat_cons_eqpoll: "nat \<lesssim> A ==> cons(u,A) \<approx> A"
apply (erule nat_cons_lepoll [THEN eqpollI])
apply (rule subset_consI [THEN subset_imp_lepoll])
done

(*Specialized version required below*)
lemma nat_succ_eqpoll: "nat <= A ==> succ(A) \<approx> A"
apply (unfold succ_def)
apply (erule subset_imp_lepoll [THEN nat_cons_eqpoll])
done

lemma InfCard_nat: "InfCard(nat)"
apply (unfold InfCard_def)
apply (blast intro: Card_nat le_refl Card_is_Ord)
done

lemma InfCard_is_Card: "InfCard(K) ==> Card(K)"
apply (unfold InfCard_def)
apply (erule conjunct1)
done

lemma InfCard_Un:
    "[| InfCard(K);  Card(L) |] ==> InfCard(K Un L)"
apply (unfold InfCard_def)
apply (simp add: Card_Un Un_upper1_le [THEN [2] le_trans]  Card_is_Ord)
done

(*Kunen's Lemma 10.11*)
lemma InfCard_is_Limit: "InfCard(K) ==> Limit(K)"
apply (unfold InfCard_def)
apply (erule conjE)
apply (frule Card_is_Ord)
apply (rule ltI [THEN non_succ_LimitI])
apply (erule le_imp_subset [THEN subsetD])
apply (safe dest!: Limit_nat [THEN Limit_le_succD])
apply (unfold Card_def)
apply (drule trans)
apply (erule le_imp_subset [THEN nat_succ_eqpoll, THEN cardinal_cong])
apply (erule Ord_cardinal_le [THEN lt_trans2, THEN lt_irrefl])
apply (rule le_eqI) 
apply assumption; 
apply (rule Ord_cardinal)
done


(*** An infinite cardinal equals its square (Kunen, Thm 10.12, page 29) ***)

(*A general fact about ordermap*)
lemma ordermap_eqpoll_pred:
    "[| well_ord(A,r);  x:A |] ==> ordermap(A,r)`x \<approx> pred(A,x,r)"
apply (unfold eqpoll_def)
apply (rule exI)
apply (simp (no_asm_simp) add: ordermap_eq_image well_ord_is_wf)
apply (erule ordermap_bij [THEN bij_is_inj, THEN restrict_bij, THEN bij_converse_bij])
apply (rule pred_subset)
done

(** Establishing the well-ordering **)

lemma csquare_lam_inj:
     "Ord(K) ==> (lam <x,y>:K*K. <x Un y, x, y>) : inj(K*K, K*K*K)"
apply (unfold inj_def)
apply (force intro: lam_type Un_least_lt [THEN ltD] ltI)
done

lemma well_ord_csquare: "Ord(K) ==> well_ord(K*K, csquare_rel(K))"
apply (unfold csquare_rel_def)
apply (rule csquare_lam_inj [THEN well_ord_rvimage])
apply assumption; 
apply (blast intro: well_ord_rmult well_ord_Memrel)
done

(** Characterising initial segments of the well-ordering **)

lemma csquareD:
 "[| <<x,y>, <z,z>> : csquare_rel(K);  x<K;  y<K;  z<K |] ==> x le z & y le z"
apply (unfold csquare_rel_def)
apply (erule rev_mp)
apply (elim ltE)
apply (simp (no_asm_simp) add: rvimage_iff Un_absorb Un_least_mem_iff ltD)
apply (safe elim!: mem_irrefl intro!: Un_upper1_le Un_upper2_le)
apply (simp_all (no_asm_simp) add: lt_def succI2)
done

lemma pred_csquare_subset: 
    "z<K ==> pred(K*K, <z,z>, csquare_rel(K)) <= succ(z)*succ(z)"
apply (unfold Order.pred_def)
apply (safe del: SigmaI succCI)
apply (erule csquareD [THEN conjE])
apply (unfold lt_def)
apply (auto ); 
done

lemma csquare_ltI:
 "[| x<z;  y<z;  z<K |] ==>  <<x,y>, <z,z>> : csquare_rel(K)"
apply (unfold csquare_rel_def)
apply (subgoal_tac "x<K & y<K")
 prefer 2 apply (blast intro: lt_trans) 
apply (elim ltE)
apply (simp (no_asm_simp) add: rvimage_iff Un_absorb Un_least_mem_iff ltD)
done

(*Part of the traditional proof.  UNUSED since it's harder to prove & apply *)
lemma csquare_or_eqI:
 "[| x le z;  y le z;  z<K |] ==> <<x,y>, <z,z>> : csquare_rel(K) | x=z & y=z"
apply (unfold csquare_rel_def)
apply (subgoal_tac "x<K & y<K")
 prefer 2 apply (blast intro: lt_trans1) 
apply (elim ltE)
apply (simp (no_asm_simp) add: rvimage_iff Un_absorb Un_least_mem_iff ltD)
apply (elim succE)
apply (simp_all (no_asm_simp) add: subset_Un_iff [THEN iff_sym] subset_Un_iff2 [THEN iff_sym] OrdmemD)
done

(** The cardinality of initial segments **)

lemma ordermap_z_lt:
      "[| Limit(K);  x<K;  y<K;  z=succ(x Un y) |] ==>
          ordermap(K*K, csquare_rel(K)) ` <x,y> <
          ordermap(K*K, csquare_rel(K)) ` <z,z>"
apply (subgoal_tac "z<K & well_ord (K*K, csquare_rel (K))")
prefer 2 apply (blast intro!: Un_least_lt Limit_has_succ
                              Limit_is_Ord [THEN well_ord_csquare])
apply (clarify ); 
apply (rule csquare_ltI [THEN ordermap_mono, THEN ltI])
apply (erule_tac [4] well_ord_is_wf)
apply (blast intro!: Un_upper1_le Un_upper2_le Ord_ordermap elim!: ltE)+
done

(*Kunen: "each <x,y>: K*K has no more than z*z predecessors..." (page 29) *)
lemma ordermap_csquare_le:
  "[| Limit(K);  x<K;  y<K;  z=succ(x Un y) |] ==>
        | ordermap(K*K, csquare_rel(K)) ` <x,y> | le  |succ(z)| |*| |succ(z)|"
apply (unfold cmult_def)
apply (rule well_ord_rmult [THEN well_ord_lepoll_imp_Card_le])
apply (rule Ord_cardinal [THEN well_ord_Memrel])+
apply (subgoal_tac "z<K")
 prefer 2 apply (blast intro!: Un_least_lt Limit_has_succ)
apply (rule ordermap_z_lt [THEN leI, THEN le_imp_lepoll, THEN lepoll_trans])
apply assumption +
apply (rule ordermap_eqpoll_pred [THEN eqpoll_imp_lepoll, THEN lepoll_trans])
apply (erule Limit_is_Ord [THEN well_ord_csquare])
apply (blast intro: ltD)
apply (rule pred_csquare_subset [THEN subset_imp_lepoll, THEN lepoll_trans],
            assumption)
apply (elim ltE)
apply (rule prod_eqpoll_cong [THEN eqpoll_sym, THEN eqpoll_imp_lepoll])
apply (erule Ord_succ [THEN Ord_cardinal_eqpoll])+
done

(*Kunen: "... so the order type <= K" *)
lemma ordertype_csquare_le:
     "[| InfCard(K);  ALL y:K. InfCard(y) --> y |*| y = y |] 
      ==> ordertype(K*K, csquare_rel(K)) le K"
apply (frule InfCard_is_Card [THEN Card_is_Ord])
apply (rule all_lt_imp_le)
apply assumption
apply (erule well_ord_csquare [THEN Ord_ordertype])
apply (rule Card_lt_imp_lt)
apply (erule_tac [3] InfCard_is_Card)
apply (erule_tac [2] ltE)
apply (simp add: ordertype_unfold)
apply (safe elim!: ltE)
apply (subgoal_tac "Ord (xa) & Ord (ya)")
 prefer 2 apply (blast intro: Ord_in_Ord)
apply (clarify );
(*??WHAT A MESS!*)  
apply (rule InfCard_is_Limit [THEN ordermap_csquare_le, THEN lt_trans1],
       (assumption | rule refl | erule ltI)+) 
apply (rule_tac i = "xa Un ya" and j = "nat" in Ord_linear2,
       simp_all add: Ord_Un Ord_nat)
prefer 2 (*case nat le (xa Un ya) *)
 apply (simp add: le_imp_subset [THEN nat_succ_eqpoll, THEN cardinal_cong] 
                  le_succ_iff InfCard_def Card_cardinal Un_least_lt Ord_Un
                ltI nat_le_cardinal Ord_cardinal_le [THEN lt_trans1, THEN ltD])
(*the finite case: xa Un ya < nat *)
apply (rule_tac j = "nat" in lt_trans2)
 apply (simp add: lt_def nat_cmult_eq_mult nat_succI mult_type
                  nat_into_Card [THEN Card_cardinal_eq]  Ord_nat)
apply (simp add: InfCard_def)
done

(*Main result: Kunen's Theorem 10.12*)
lemma InfCard_csquare_eq: "InfCard(K) ==> K |*| K = K"
apply (frule InfCard_is_Card [THEN Card_is_Ord])
apply (erule rev_mp)
apply (erule_tac i=K in trans_induct) 
apply (rule impI)
apply (rule le_anti_sym)
apply (erule_tac [2] InfCard_is_Card [THEN cmult_square_le])
apply (rule ordertype_csquare_le [THEN [2] le_trans])
prefer 2 apply (assumption)
prefer 2 apply (assumption)
apply (simp (no_asm_simp) add: cmult_def Ord_cardinal_le well_ord_csquare [THEN ordermap_bij, THEN bij_imp_eqpoll, THEN cardinal_cong] well_ord_csquare [THEN Ord_ordertype])
done

(*Corollary for arbitrary well-ordered sets (all sets, assuming AC)*)
lemma well_ord_InfCard_square_eq:
     "[| well_ord(A,r);  InfCard(|A|) |] ==> A*A \<approx> A"
apply (rule prod_eqpoll_cong [THEN eqpoll_trans])
apply (erule well_ord_cardinal_eqpoll [THEN eqpoll_sym])+
apply (rule well_ord_cardinal_eqE)
apply (blast intro: Ord_cardinal well_ord_rmult well_ord_Memrel)
apply assumption; 
apply (simp (no_asm_simp) add: cmult_def [symmetric] InfCard_csquare_eq)
done

(** Toward's Kunen's Corollary 10.13 (1) **)

lemma InfCard_le_cmult_eq: "[| InfCard(K);  L le K;  0<L |] ==> K |*| L = K"
apply (rule le_anti_sym)
 prefer 2
 apply (erule ltE, blast intro: cmult_le_self InfCard_is_Card)
apply (frule InfCard_is_Card [THEN Card_is_Ord, THEN le_refl])
apply (rule cmult_le_mono [THEN le_trans], assumption+)
apply (simp add: InfCard_csquare_eq)
done

(*Corollary 10.13 (1), for cardinal multiplication*)
lemma InfCard_cmult_eq: "[| InfCard(K);  InfCard(L) |] ==> K |*| L = K Un L"
apply (rule_tac i = "K" and j = "L" in Ord_linear_le)
apply (typecheck add: InfCard_is_Card Card_is_Ord)
apply (rule cmult_commute [THEN ssubst])
apply (rule Un_commute [THEN ssubst])
apply (simp_all (no_asm_simp) add: InfCard_is_Limit [THEN Limit_has_0] InfCard_le_cmult_eq subset_Un_iff2 [THEN iffD1] le_imp_subset)
done

lemma InfCard_cdouble_eq: "InfCard(K) ==> K |+| K = K"
apply (simp (no_asm_simp) add: cmult_2 [symmetric] InfCard_is_Card cmult_commute)
apply (simp (no_asm_simp) add: InfCard_le_cmult_eq InfCard_is_Limit Limit_has_0 Limit_has_succ)
done

(*Corollary 10.13 (1), for cardinal addition*)
lemma InfCard_le_cadd_eq: "[| InfCard(K);  L le K |] ==> K |+| L = K"
apply (rule le_anti_sym)
 prefer 2
 apply (erule ltE, blast intro: cadd_le_self InfCard_is_Card)
apply (frule InfCard_is_Card [THEN Card_is_Ord, THEN le_refl])
apply (rule cadd_le_mono [THEN le_trans], assumption+)
apply (simp add: InfCard_cdouble_eq)
done

lemma InfCard_cadd_eq: "[| InfCard(K);  InfCard(L) |] ==> K |+| L = K Un L"
apply (rule_tac i = "K" and j = "L" in Ord_linear_le)
apply (typecheck add: InfCard_is_Card Card_is_Ord)
apply (rule cadd_commute [THEN ssubst])
apply (rule Un_commute [THEN ssubst])
apply (simp_all (no_asm_simp) add: InfCard_le_cadd_eq subset_Un_iff2 [THEN iffD1] le_imp_subset)
done

(*The other part, Corollary 10.13 (2), refers to the cardinality of the set
  of all n-tuples of elements of K.  A better version for the Isabelle theory
  might be  InfCard(K) ==> |list(K)| = K.
*)

(*** For every cardinal number there exists a greater one
     [Kunen's Theorem 10.16, which would be trivial using AC] ***)

lemma Ord_jump_cardinal: "Ord(jump_cardinal(K))"
apply (unfold jump_cardinal_def)
apply (rule Ord_is_Transset [THEN [2] OrdI])
 prefer 2 apply (blast intro!: Ord_ordertype)
apply (unfold Transset_def)
apply (safe del: subsetI)
apply (simp add: ordertype_pred_unfold)
apply safe
apply (rule UN_I)
apply (rule_tac [2] ReplaceI)
   prefer 4 apply (blast intro: well_ord_subset elim!: predE)+
done

(*Allows selective unfolding.  Less work than deriving intro/elim rules*)
lemma jump_cardinal_iff:
     "i : jump_cardinal(K) <->
      (EX r X. r <= K*K & X <= K & well_ord(X,r) & i = ordertype(X,r))"
apply (unfold jump_cardinal_def)
apply (blast del: subsetI) 
done

(*The easy part of Theorem 10.16: jump_cardinal(K) exceeds K*)
lemma K_lt_jump_cardinal: "Ord(K) ==> K < jump_cardinal(K)"
apply (rule Ord_jump_cardinal [THEN [2] ltI])
apply (rule jump_cardinal_iff [THEN iffD2])
apply (rule_tac x="Memrel(K)" in exI)
apply (rule_tac x=K in exI)  
apply (simp add: ordertype_Memrel well_ord_Memrel)
apply (simp add: Memrel_def subset_iff)
done

(*The proof by contradiction: the bijection f yields a wellordering of X
  whose ordertype is jump_cardinal(K).  *)
lemma Card_jump_cardinal_lemma:
     "[| well_ord(X,r);  r <= K * K;  X <= K;
         f : bij(ordertype(X,r), jump_cardinal(K)) |]
      ==> jump_cardinal(K) : jump_cardinal(K)"
apply (subgoal_tac "f O ordermap (X,r) : bij (X, jump_cardinal (K))")
 prefer 2 apply (blast intro: comp_bij ordermap_bij)
apply (rule jump_cardinal_iff [THEN iffD2])
apply (intro exI conjI)
apply (rule subset_trans [OF rvimage_type Sigma_mono])
apply assumption+
apply (erule bij_is_inj [THEN well_ord_rvimage])
apply (rule Ord_jump_cardinal [THEN well_ord_Memrel])
apply (simp add: well_ord_Memrel [THEN [2] bij_ordertype_vimage]
                 ordertype_Memrel Ord_jump_cardinal)
done

(*The hard part of Theorem 10.16: jump_cardinal(K) is itself a cardinal*)
lemma Card_jump_cardinal: "Card(jump_cardinal(K))"
apply (rule Ord_jump_cardinal [THEN CardI])
apply (unfold eqpoll_def)
apply (safe dest!: ltD jump_cardinal_iff [THEN iffD1])
apply (blast intro: Card_jump_cardinal_lemma [THEN mem_irrefl])
done

(*** Basic properties of successor cardinals ***)

lemma csucc_basic: "Ord(K) ==> Card(csucc(K)) & K < csucc(K)"
apply (unfold csucc_def)
apply (rule LeastI)
apply (blast intro: Card_jump_cardinal K_lt_jump_cardinal Ord_jump_cardinal)+
done

lemmas Card_csucc = csucc_basic [THEN conjunct1, standard]

lemmas lt_csucc = csucc_basic [THEN conjunct2, standard]

lemma Ord_0_lt_csucc: "Ord(K) ==> 0 < csucc(K)"
apply (blast intro: Ord_0_le lt_csucc lt_trans1)
done

lemma csucc_le: "[| Card(L);  K<L |] ==> csucc(K) le L"
apply (unfold csucc_def)
apply (rule Least_le)
apply (blast intro: Card_is_Ord)+
done

lemma lt_csucc_iff: "[| Ord(i); Card(K) |] ==> i < csucc(K) <-> |i| le K"
apply (rule iffI)
apply (rule_tac [2] Card_lt_imp_lt)
apply (erule_tac [2] lt_trans1)
apply (simp_all add: lt_csucc Card_csucc Card_is_Ord)
apply (rule notI [THEN not_lt_imp_le])
apply (rule Card_cardinal [THEN csucc_le, THEN lt_trans1, THEN lt_irrefl])
apply assumption
apply (rule Ord_cardinal_le [THEN lt_trans1])
apply (simp_all add: Ord_cardinal Card_is_Ord) 
done

lemma Card_lt_csucc_iff:
     "[| Card(K'); Card(K) |] ==> K' < csucc(K) <-> K' le K"
by (simp (no_asm_simp) add: lt_csucc_iff Card_cardinal_eq Card_is_Ord)

lemma InfCard_csucc: "InfCard(K) ==> InfCard(csucc(K))"
by (simp add: InfCard_def Card_csucc Card_is_Ord 
              lt_csucc [THEN leI, THEN [2] le_trans])


(*** Finite sets ***)

lemma Fin_lemma [rule_format]: "n: nat ==> ALL A. A \<approx> n --> A : Fin(A)"
apply (induct_tac "n")
apply (simp (no_asm) add: eqpoll_0_iff)
apply clarify
apply (subgoal_tac "EX u. u:A")
apply (erule exE)
apply (rule Diff_sing_eqpoll [THEN revcut_rl])
prefer 2 apply (assumption)
apply assumption
apply (rule_tac b = "A" in cons_Diff [THEN subst])
apply assumption
apply (rule Fin.consI)
apply blast
apply (blast intro: subset_consI [THEN Fin_mono, THEN subsetD])
(*Now for the lemma assumed above*)
apply (unfold eqpoll_def)
apply (blast intro: bij_converse_bij [THEN bij_is_fun, THEN apply_type])
done

lemma Finite_into_Fin: "Finite(A) ==> A : Fin(A)"
apply (unfold Finite_def)
apply (blast intro: Fin_lemma)
done

lemma Fin_into_Finite: "A : Fin(U) ==> Finite(A)"
apply (fast intro!: Finite_0 Finite_cons elim: Fin_induct)
done

lemma Finite_Fin_iff: "Finite(A) <-> A : Fin(A)"
apply (blast intro: Finite_into_Fin Fin_into_Finite)
done

lemma Finite_Un: "[| Finite(A); Finite(B) |] ==> Finite(A Un B)"
by (blast intro!: Fin_into_Finite Fin_UnI 
          dest!: Finite_into_Fin
          intro: Un_upper1 [THEN Fin_mono, THEN subsetD] 
                 Un_upper2 [THEN Fin_mono, THEN subsetD])

lemma Finite_Union: "[| ALL y:X. Finite(y);  Finite(X) |] ==> Finite(Union(X))"
apply (simp add: Finite_Fin_iff)
apply (rule Fin_UnionI)
apply (erule Fin_induct)
apply (simp (no_asm))
apply (blast intro: Fin.consI Fin_mono [THEN [2] rev_subsetD])
done

(* Induction principle for Finite(A), by Sidi Ehmety *)
lemma Finite_induct:
"[| Finite(A); P(0);
    !! x B.   [| Finite(B); x ~: B; P(B) |] ==> P(cons(x, B)) |]
 ==> P(A)"
apply (erule Finite_into_Fin [THEN Fin_induct]) 
apply (blast intro: Fin_into_Finite)+
done


(** Removing elements from a finite set decreases its cardinality **)

lemma Fin_imp_not_cons_lepoll: "A: Fin(U) ==> x~:A --> ~ cons(x,A) \<lesssim> A"
apply (erule Fin_induct)
apply (simp (no_asm) add: lepoll_0_iff)
apply (subgoal_tac "cons (x,cons (xa,y)) = cons (xa,cons (x,y))")
apply (simp (no_asm_simp))
apply (blast dest!: cons_lepoll_consD)
apply blast
done

lemma Finite_imp_cardinal_cons: "[| Finite(A);  a~:A |] ==> |cons(a,A)| = succ(|A|)"
apply (unfold cardinal_def)
apply (rule Least_equality)
apply (fold cardinal_def)
apply (simp (no_asm) add: succ_def)
apply (blast intro: cons_eqpoll_cong well_ord_cardinal_eqpoll
             elim!: mem_irrefl  dest!: Finite_imp_well_ord)
apply (blast intro: Card_cardinal Card_is_Ord)
apply (rule notI)
apply (rule Finite_into_Fin [THEN Fin_imp_not_cons_lepoll, THEN mp, THEN notE])
apply assumption
apply assumption
apply (erule eqpoll_sym [THEN eqpoll_imp_lepoll, THEN lepoll_trans])
apply (erule le_imp_lepoll [THEN lepoll_trans])
apply (blast intro: well_ord_cardinal_eqpoll [THEN eqpoll_imp_lepoll]
             dest!: Finite_imp_well_ord)
done


lemma Finite_imp_succ_cardinal_Diff: "[| Finite(A);  a:A |] ==> succ(|A-{a}|) = |A|"
apply (rule_tac b = "A" in cons_Diff [THEN subst])
apply assumption
apply (simp (no_asm_simp) add: Finite_imp_cardinal_cons Diff_subset [THEN subset_Finite])
apply (simp (no_asm_simp) add: cons_Diff)
done

lemma Finite_imp_cardinal_Diff: "[| Finite(A);  a:A |] ==> |A-{a}| < |A|"
apply (rule succ_leE)
apply (simp (no_asm_simp) add: Finite_imp_succ_cardinal_Diff)
done


(** Theorems by Krzysztof Grabczewski, proofs by lcp **)

lemmas nat_implies_well_ord = nat_into_Ord [THEN well_ord_Memrel, standard]

lemma nat_sum_eqpoll_sum: "[| m:nat; n:nat |] ==> m + n \<approx> m #+ n"
apply (rule eqpoll_trans)
apply (rule well_ord_radd [THEN well_ord_cardinal_eqpoll, THEN eqpoll_sym])
apply (erule nat_implies_well_ord)+
apply (simp (no_asm_simp) add: nat_cadd_eq_add [symmetric] cadd_def eqpoll_refl)
done


(*** Theorems by Sidi Ehmety ***)

(*The contrapositive says ~Finite(A) ==> ~Finite(A-{a}) *)
lemma Diff_sing_Finite: "Finite(A - {a}) ==> Finite(A)"
apply (unfold Finite_def)
apply (case_tac "a:A")
apply (subgoal_tac [2] "A-{a}=A")
apply auto
apply (rule_tac x = "succ (n) " in bexI)
apply (subgoal_tac "cons (a, A - {a}) = A & cons (n, n) = succ (n) ")
apply (drule_tac a = "a" and b = "n" in cons_eqpoll_cong)
apply (auto dest: mem_irrefl)
done

(*And the contrapositive of this says
   [| ~Finite(A); Finite(B) |] ==> ~Finite(A-B) *)
lemma Diff_Finite [rule_format (no_asm)]: "Finite(B) ==> Finite(A-B) --> Finite(A)"
apply (erule Finite_induct)
apply auto
apply (case_tac "x:A")
 apply (subgoal_tac [2] "A-cons (x, B) = A - B")
apply (subgoal_tac "A - cons (x, B) = (A - B) - {x}")
apply (rotate_tac -1)
apply simp
apply (drule Diff_sing_Finite)
apply auto
done

lemma Ord_subset_natD [rule_format (no_asm)]: "Ord(i) ==> i <= nat --> i : nat | i=nat"
apply (erule trans_induct3)
apply auto
apply (blast dest!: nat_le_Limit [THEN le_imp_subset])
done

lemma Ord_nat_subset_into_Card: "[| Ord(i); i <= nat |] ==> Card(i)"
apply (blast dest: Ord_subset_natD intro: Card_nat nat_into_Card)
done

lemma Finite_cardinal_in_nat [simp]: "Finite(A) ==> |A| : nat"
apply (erule Finite_induct)
apply (auto simp add: cardinal_0 Finite_imp_cardinal_cons)
done

lemma Finite_Diff_sing_eq_diff_1: "[| Finite(A); x:A |] ==> |A-{x}| = |A| #- 1"
apply (rule succ_inject)
apply (rule_tac b = "|A|" in trans)
apply (simp (no_asm_simp) add: Finite_imp_succ_cardinal_Diff)
apply (subgoal_tac "1 \<lesssim> A")
prefer 2 apply (blast intro: not_0_is_lepoll_1)
apply (frule Finite_imp_well_ord)
apply clarify
apply (rotate_tac -1)
apply (drule well_ord_lepoll_imp_Card_le)
apply (auto simp add: cardinal_1)
apply (rule trans)
apply (rule_tac [2] diff_succ)
apply (auto simp add: Finite_cardinal_in_nat)
done

lemma cardinal_lt_imp_Diff_not_0 [rule_format (no_asm)]: "Finite(B) ==> ALL A. |B|<|A| --> A - B ~= 0"
apply (erule Finite_induct)
apply auto
apply (simp_all add: Finite_imp_cardinal_cons)
apply (case_tac "Finite (A) ")
apply (subgoal_tac [2] "Finite (cons (x, B))")
apply (drule_tac [2] B = "cons (x, B) " in Diff_Finite)
apply (auto simp add: Finite_0 Finite_cons)
apply (subgoal_tac "|B|<|A|")
prefer 2 apply (blast intro: lt_trans Ord_cardinal)
apply (case_tac "x:A")
apply (subgoal_tac [2] "A - cons (x, B) = A - B")
apply auto
apply (subgoal_tac "|A| le |cons (x, B) |")
prefer 2
 apply (blast dest: Finite_cons [THEN Finite_imp_well_ord] 
              intro: well_ord_lepoll_imp_Card_le subset_imp_lepoll)
apply (auto simp add: Finite_imp_cardinal_cons)
apply (auto dest!: Finite_cardinal_in_nat simp add: le_iff)
apply (blast intro: lt_trans)
done


ML{*
val InfCard_def = thm "InfCard_def"
val cmult_def = thm "cmult_def"
val cadd_def = thm "cadd_def"
val jump_cardinal_def = thm "jump_cardinal_def"
val csucc_def = thm "csucc_def"

val sum_commute_eqpoll = thm "sum_commute_eqpoll";
val cadd_commute = thm "cadd_commute";
val sum_assoc_eqpoll = thm "sum_assoc_eqpoll";
val well_ord_cadd_assoc = thm "well_ord_cadd_assoc";
val sum_0_eqpoll = thm "sum_0_eqpoll";
val cadd_0 = thm "cadd_0";
val sum_lepoll_self = thm "sum_lepoll_self";
val cadd_le_self = thm "cadd_le_self";
val sum_lepoll_mono = thm "sum_lepoll_mono";
val cadd_le_mono = thm "cadd_le_mono";
val eq_imp_not_mem = thm "eq_imp_not_mem";
val sum_succ_eqpoll = thm "sum_succ_eqpoll";
val nat_cadd_eq_add = thm "nat_cadd_eq_add";
val prod_commute_eqpoll = thm "prod_commute_eqpoll";
val cmult_commute = thm "cmult_commute";
val prod_assoc_eqpoll = thm "prod_assoc_eqpoll";
val well_ord_cmult_assoc = thm "well_ord_cmult_assoc";
val sum_prod_distrib_eqpoll = thm "sum_prod_distrib_eqpoll";
val well_ord_cadd_cmult_distrib = thm "well_ord_cadd_cmult_distrib";
val prod_0_eqpoll = thm "prod_0_eqpoll";
val cmult_0 = thm "cmult_0";
val prod_singleton_eqpoll = thm "prod_singleton_eqpoll";
val cmult_1 = thm "cmult_1";
val prod_lepoll_self = thm "prod_lepoll_self";
val cmult_le_self = thm "cmult_le_self";
val prod_lepoll_mono = thm "prod_lepoll_mono";
val cmult_le_mono = thm "cmult_le_mono";
val prod_succ_eqpoll = thm "prod_succ_eqpoll";
val nat_cmult_eq_mult = thm "nat_cmult_eq_mult";
val cmult_2 = thm "cmult_2";
val sum_lepoll_prod = thm "sum_lepoll_prod";
val lepoll_imp_sum_lepoll_prod = thm "lepoll_imp_sum_lepoll_prod";
val nat_cons_lepoll = thm "nat_cons_lepoll";
val nat_cons_eqpoll = thm "nat_cons_eqpoll";
val nat_succ_eqpoll = thm "nat_succ_eqpoll";
val InfCard_nat = thm "InfCard_nat";
val InfCard_is_Card = thm "InfCard_is_Card";
val InfCard_Un = thm "InfCard_Un";
val InfCard_is_Limit = thm "InfCard_is_Limit";
val ordermap_eqpoll_pred = thm "ordermap_eqpoll_pred";
val ordermap_z_lt = thm "ordermap_z_lt";
val InfCard_le_cmult_eq = thm "InfCard_le_cmult_eq";
val InfCard_cmult_eq = thm "InfCard_cmult_eq";
val InfCard_cdouble_eq = thm "InfCard_cdouble_eq";
val InfCard_le_cadd_eq = thm "InfCard_le_cadd_eq";
val InfCard_cadd_eq = thm "InfCard_cadd_eq";
val Ord_jump_cardinal = thm "Ord_jump_cardinal";
val jump_cardinal_iff = thm "jump_cardinal_iff";
val K_lt_jump_cardinal = thm "K_lt_jump_cardinal";
val Card_jump_cardinal = thm "Card_jump_cardinal";
val csucc_basic = thm "csucc_basic";
val Card_csucc = thm "Card_csucc";
val lt_csucc = thm "lt_csucc";
val Ord_0_lt_csucc = thm "Ord_0_lt_csucc";
val csucc_le = thm "csucc_le";
val lt_csucc_iff = thm "lt_csucc_iff";
val Card_lt_csucc_iff = thm "Card_lt_csucc_iff";
val InfCard_csucc = thm "InfCard_csucc";
val Finite_into_Fin = thm "Finite_into_Fin";
val Fin_into_Finite = thm "Fin_into_Finite";
val Finite_Fin_iff = thm "Finite_Fin_iff";
val Finite_Un = thm "Finite_Un";
val Finite_Union = thm "Finite_Union";
val Finite_induct = thm "Finite_induct";
val Fin_imp_not_cons_lepoll = thm "Fin_imp_not_cons_lepoll";
val Finite_imp_cardinal_cons = thm "Finite_imp_cardinal_cons";
val Finite_imp_succ_cardinal_Diff = thm "Finite_imp_succ_cardinal_Diff";
val Finite_imp_cardinal_Diff = thm "Finite_imp_cardinal_Diff";
val nat_implies_well_ord = thm "nat_implies_well_ord";
val nat_sum_eqpoll_sum = thm "nat_sum_eqpoll_sum";
val Diff_sing_Finite = thm "Diff_sing_Finite";
val Diff_Finite = thm "Diff_Finite";
val Ord_subset_natD = thm "Ord_subset_natD";
val Ord_nat_subset_into_Card = thm "Ord_nat_subset_into_Card";
val Finite_cardinal_in_nat = thm "Finite_cardinal_in_nat";
val Finite_Diff_sing_eq_diff_1 = thm "Finite_Diff_sing_eq_diff_1";
val cardinal_lt_imp_Diff_not_0 = thm "cardinal_lt_imp_Diff_not_0";
*}

end
