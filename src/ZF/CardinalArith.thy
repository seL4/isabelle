(*  Title:      ZF/CardinalArith.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge
*)

header{*Cardinal Arithmetic Without the Axiom of Choice*}

theory CardinalArith imports Cardinal OrderArith ArithSimp Finite begin

definition
  InfCard       :: "i=>o"  where
    "InfCard(i) == Card(i) & nat \<le> i"

definition
  cmult         :: "[i,i]=>i"       (infixl "|*|" 70)  where
    "i |*| j == |i*j|"

definition
  cadd          :: "[i,i]=>i"       (infixl "|+|" 65)  where
    "i |+| j == |i+j|"

definition
  csquare_rel   :: "i=>i"  where
    "csquare_rel(K) ==
          rvimage(K*K,
                  lam <x,y>:K*K. <x \<union> y, x, y>,
                  rmult(K,Memrel(K), K*K, rmult(K,Memrel(K), K,Memrel(K))))"

definition
  jump_cardinal :: "i=>i"  where
    --{*This def is more complex than Kunen's but it more easily proved to
        be a cardinal*}
    "jump_cardinal(K) ==
         \<Union>X\<in>Pow(K). {z. r \<in> Pow(K*K), well_ord(X,r) & z = ordertype(X,r)}"

definition
  csucc         :: "i=>i"  where
    --{*needed because @{term "jump_cardinal(K)"} might not be the successor
        of @{term K}*}
    "csucc(K) == LEAST L. Card(L) & K<L"

notation (xsymbols)
  cadd  (infixl "\<oplus>" 65) and
  cmult  (infixl "\<otimes>" 70)

notation (HTML)
  cadd  (infixl "\<oplus>" 65) and
  cmult  (infixl "\<otimes>" 70)


lemma Card_Union [simp,intro,TC]:
  assumes A: "\<And>x. x\<in>A \<Longrightarrow> Card(x)" shows "Card(\<Union>(A))"
proof (rule CardI)
  show "Ord(\<Union>A)" using A
    by (simp add: Card_is_Ord)
next
  fix j
  assume j: "j < \<Union>A"
  hence "\<exists>c\<in>A. j < c & Card(c)" using A
    by (auto simp add: lt_def intro: Card_is_Ord)
  then obtain c where c: "c\<in>A" "j < c" "Card(c)"
    by blast
  hence jls: "j \<prec> c"
    by (simp add: lt_Card_imp_lesspoll)
  { assume eqp: "j \<approx> \<Union>A"
    have  "c \<lesssim> \<Union>A" using c
      by (blast intro: subset_imp_lepoll)
    also have "... \<approx> j"  by (rule eqpoll_sym [OF eqp])
    also have "... \<prec> c"  by (rule jls)
    finally have "c \<prec> c" .
    hence False
      by auto
  } thus "\<not> j \<approx> \<Union>A" by blast
qed

lemma Card_UN: "(!!x. x \<in> A ==> Card(K(x))) ==> Card(\<Union>x\<in>A. K(x))"
  by blast

lemma Card_OUN [simp,intro,TC]:
     "(!!x. x \<in> A ==> Card(K(x))) ==> Card(\<Union>x<A. K(x))"
  by (auto simp add: OUnion_def Card_0)

lemma in_Card_imp_lesspoll: "[| Card(K); b \<in> K |] ==> b \<prec> K"
apply (unfold lesspoll_def)
apply (simp add: Card_iff_initial)
apply (fast intro!: le_imp_lepoll ltI leI)
done


subsection{*Cardinal addition*}

text{*Note: Could omit proving the algebraic laws for cardinal addition and
multiplication.  On finite cardinals these operations coincide with
addition and multiplication of natural numbers; on infinite cardinals they
coincide with union (maximum).  Either way we get most laws for free.*}

subsubsection{*Cardinal addition is commutative*}

lemma sum_commute_eqpoll: "A+B \<approx> B+A"
proof (unfold eqpoll_def, rule exI)
  show "(\<lambda>z\<in>A+B. case(Inr,Inl,z)) \<in> bij(A+B, B+A)"
    by (auto intro: lam_bijective [where d = "case(Inr,Inl)"])
qed

lemma cadd_commute: "i \<oplus> j = j \<oplus> i"
apply (unfold cadd_def)
apply (rule sum_commute_eqpoll [THEN cardinal_cong])
done

subsubsection{*Cardinal addition is associative*}

lemma sum_assoc_eqpoll: "(A+B)+C \<approx> A+(B+C)"
apply (unfold eqpoll_def)
apply (rule exI)
apply (rule sum_assoc_bij)
done

text{*Unconditional version requires AC*}
lemma well_ord_cadd_assoc:
  assumes i: "well_ord(i,ri)" and j: "well_ord(j,rj)" and k: "well_ord(k,rk)"
  shows "(i \<oplus> j) \<oplus> k = i \<oplus> (j \<oplus> k)"
proof (unfold cadd_def, rule cardinal_cong)
  have "|i + j| + k \<approx> (i + j) + k"
    by (blast intro: sum_eqpoll_cong well_ord_cardinal_eqpoll eqpoll_refl well_ord_radd i j)
  also have "...  \<approx> i + (j + k)"
    by (rule sum_assoc_eqpoll)
  also have "...  \<approx> i + |j + k|"
    by (blast intro: sum_eqpoll_cong well_ord_cardinal_eqpoll eqpoll_refl well_ord_radd j k eqpoll_sym)
  finally show "|i + j| + k \<approx> i + |j + k|" .
qed


subsubsection{*0 is the identity for addition*}

lemma sum_0_eqpoll: "0+A \<approx> A"
apply (unfold eqpoll_def)
apply (rule exI)
apply (rule bij_0_sum)
done

lemma cadd_0 [simp]: "Card(K) ==> 0 \<oplus> K = K"
apply (unfold cadd_def)
apply (simp add: sum_0_eqpoll [THEN cardinal_cong] Card_cardinal_eq)
done

subsubsection{*Addition by another cardinal*}

lemma sum_lepoll_self: "A \<lesssim> A+B"
proof (unfold lepoll_def, rule exI)
  show "(\<lambda>x\<in>A. Inl (x)) \<in> inj(A, A + B)"
    by (simp add: inj_def)
qed

(*Could probably weaken the premises to well_ord(K,r), or removing using AC*)

lemma cadd_le_self:
  assumes K: "Card(K)" and L: "Ord(L)" shows "K \<le> (K \<oplus> L)"
proof (unfold cadd_def)
  have "K \<le> |K|"
    by (rule Card_cardinal_le [OF K])
  moreover have "|K| \<le> |K + L|" using K L
    by (blast intro: well_ord_lepoll_imp_Card_le sum_lepoll_self
                     well_ord_radd well_ord_Memrel Card_is_Ord)
  ultimately show "K \<le> |K + L|"
    by (blast intro: le_trans)
qed

subsubsection{*Monotonicity of addition*}

lemma sum_lepoll_mono:
     "[| A \<lesssim> C;  B \<lesssim> D |] ==> A + B \<lesssim> C + D"
apply (unfold lepoll_def)
apply (elim exE)
apply (rule_tac x = "\<lambda>z\<in>A+B. case (%w. Inl(f`w), %y. Inr(fa`y), z)" in exI)
apply (rule_tac d = "case (%w. Inl(converse(f) `w), %y. Inr(converse(fa) ` y))"
       in lam_injective)
apply (typecheck add: inj_is_fun, auto)
done

lemma cadd_le_mono:
    "[| K' \<le> K;  L' \<le> L |] ==> (K' \<oplus> L') \<le> (K \<oplus> L)"
apply (unfold cadd_def)
apply (safe dest!: le_subset_iff [THEN iffD1])
apply (rule well_ord_lepoll_imp_Card_le)
apply (blast intro: well_ord_radd well_ord_Memrel)
apply (blast intro: sum_lepoll_mono subset_imp_lepoll)
done

subsubsection{*Addition of finite cardinals is "ordinary" addition*}

lemma sum_succ_eqpoll: "succ(A)+B \<approx> succ(A+B)"
apply (unfold eqpoll_def)
apply (rule exI)
apply (rule_tac c = "%z. if z=Inl (A) then A+B else z"
            and d = "%z. if z=A+B then Inl (A) else z" in lam_bijective)
   apply simp_all
apply (blast dest: sym [THEN eq_imp_not_mem] elim: mem_irrefl)+
done

(*Pulling the  succ(...)  outside the |...| requires m, n \<in> nat  *)
(*Unconditional version requires AC*)
lemma cadd_succ_lemma:
  assumes "Ord(m)" "Ord(n)" shows "succ(m) \<oplus> n = |succ(m \<oplus> n)|"
proof (unfold cadd_def)
  have [intro]: "m + n \<approx> |m + n|" using assms
    by (blast intro: eqpoll_sym well_ord_cardinal_eqpoll well_ord_radd well_ord_Memrel)

  have "|succ(m) + n| = |succ(m + n)|"
    by (rule sum_succ_eqpoll [THEN cardinal_cong])
  also have "... = |succ(|m + n|)|"
    by (blast intro: succ_eqpoll_cong cardinal_cong)
  finally show "|succ(m) + n| = |succ(|m + n|)|" .
qed

lemma nat_cadd_eq_add:
  assumes m: "m \<in> nat" and [simp]: "n \<in> nat" shows"m \<oplus> n = m #+ n"
using m
proof (induct m)
  case 0 thus ?case by (simp add: nat_into_Card cadd_0)
next
  case (succ m) thus ?case by (simp add: cadd_succ_lemma nat_into_Card Card_cardinal_eq)
qed


subsection{*Cardinal multiplication*}

subsubsection{*Cardinal multiplication is commutative*}

lemma prod_commute_eqpoll: "A*B \<approx> B*A"
apply (unfold eqpoll_def)
apply (rule exI)
apply (rule_tac c = "%<x,y>.<y,x>" and d = "%<x,y>.<y,x>" in lam_bijective,
       auto)
done

lemma cmult_commute: "i \<otimes> j = j \<otimes> i"
apply (unfold cmult_def)
apply (rule prod_commute_eqpoll [THEN cardinal_cong])
done

subsubsection{*Cardinal multiplication is associative*}

lemma prod_assoc_eqpoll: "(A*B)*C \<approx> A*(B*C)"
apply (unfold eqpoll_def)
apply (rule exI)
apply (rule prod_assoc_bij)
done

text{*Unconditional version requires AC*}
lemma well_ord_cmult_assoc:
  assumes i: "well_ord(i,ri)" and j: "well_ord(j,rj)" and k: "well_ord(k,rk)"
  shows "(i \<otimes> j) \<otimes> k = i \<otimes> (j \<otimes> k)"
proof (unfold cmult_def, rule cardinal_cong)
  have "|i * j| * k \<approx> (i * j) * k"
    by (blast intro: prod_eqpoll_cong well_ord_cardinal_eqpoll eqpoll_refl well_ord_rmult i j)
  also have "...  \<approx> i * (j * k)"
    by (rule prod_assoc_eqpoll)
  also have "...  \<approx> i * |j * k|"
    by (blast intro: prod_eqpoll_cong well_ord_cardinal_eqpoll eqpoll_refl well_ord_rmult j k eqpoll_sym)
  finally show "|i * j| * k \<approx> i * |j * k|" .
qed

subsubsection{*Cardinal multiplication distributes over addition*}

lemma sum_prod_distrib_eqpoll: "(A+B)*C \<approx> (A*C)+(B*C)"
apply (unfold eqpoll_def)
apply (rule exI)
apply (rule sum_prod_distrib_bij)
done

lemma well_ord_cadd_cmult_distrib:
  assumes i: "well_ord(i,ri)" and j: "well_ord(j,rj)" and k: "well_ord(k,rk)"
  shows "(i \<oplus> j) \<otimes> k = (i \<otimes> k) \<oplus> (j \<otimes> k)"
proof (unfold cadd_def cmult_def, rule cardinal_cong)
  have "|i + j| * k \<approx> (i + j) * k"
    by (blast intro: prod_eqpoll_cong well_ord_cardinal_eqpoll eqpoll_refl well_ord_radd i j)
  also have "...  \<approx> i * k + j * k"
    by (rule sum_prod_distrib_eqpoll)
  also have "...  \<approx> |i * k| + |j * k|"
    by (blast intro: sum_eqpoll_cong well_ord_cardinal_eqpoll well_ord_rmult i j k eqpoll_sym)
  finally show "|i + j| * k \<approx> |i * k| + |j * k|" .
qed

subsubsection{*Multiplication by 0 yields 0*}

lemma prod_0_eqpoll: "0*A \<approx> 0"
apply (unfold eqpoll_def)
apply (rule exI)
apply (rule lam_bijective, safe)
done

lemma cmult_0 [simp]: "0 \<otimes> i = 0"
by (simp add: cmult_def prod_0_eqpoll [THEN cardinal_cong])

subsubsection{*1 is the identity for multiplication*}

lemma prod_singleton_eqpoll: "{x}*A \<approx> A"
apply (unfold eqpoll_def)
apply (rule exI)
apply (rule singleton_prod_bij [THEN bij_converse_bij])
done

lemma cmult_1 [simp]: "Card(K) ==> 1 \<otimes> K = K"
apply (unfold cmult_def succ_def)
apply (simp add: prod_singleton_eqpoll [THEN cardinal_cong] Card_cardinal_eq)
done

subsection{*Some inequalities for multiplication*}

lemma prod_square_lepoll: "A \<lesssim> A*A"
apply (unfold lepoll_def inj_def)
apply (rule_tac x = "\<lambda>x\<in>A. <x,x>" in exI, simp)
done

(*Could probably weaken the premise to well_ord(K,r), or remove using AC*)
lemma cmult_square_le: "Card(K) ==> K \<le> K \<otimes> K"
apply (unfold cmult_def)
apply (rule le_trans)
apply (rule_tac [2] well_ord_lepoll_imp_Card_le)
apply (rule_tac [3] prod_square_lepoll)
apply (simp add: le_refl Card_is_Ord Card_cardinal_eq)
apply (blast intro: well_ord_rmult well_ord_Memrel Card_is_Ord)
done

subsubsection{*Multiplication by a non-zero cardinal*}

lemma prod_lepoll_self: "b \<in> B ==> A \<lesssim> A*B"
apply (unfold lepoll_def inj_def)
apply (rule_tac x = "\<lambda>x\<in>A. <x,b>" in exI, simp)
done

(*Could probably weaken the premises to well_ord(K,r), or removing using AC*)
lemma cmult_le_self:
    "[| Card(K);  Ord(L);  0<L |] ==> K \<le> (K \<otimes> L)"
apply (unfold cmult_def)
apply (rule le_trans [OF Card_cardinal_le well_ord_lepoll_imp_Card_le])
  apply assumption
 apply (blast intro: well_ord_rmult well_ord_Memrel Card_is_Ord)
apply (blast intro: prod_lepoll_self ltD)
done

subsubsection{*Monotonicity of multiplication*}

lemma prod_lepoll_mono:
     "[| A \<lesssim> C;  B \<lesssim> D |] ==> A * B  \<lesssim>  C * D"
apply (unfold lepoll_def)
apply (elim exE)
apply (rule_tac x = "lam <w,y>:A*B. <f`w, fa`y>" in exI)
apply (rule_tac d = "%<w,y>. <converse (f) `w, converse (fa) `y>"
       in lam_injective)
apply (typecheck add: inj_is_fun, auto)
done

lemma cmult_le_mono:
    "[| K' \<le> K;  L' \<le> L |] ==> (K' \<otimes> L') \<le> (K \<otimes> L)"
apply (unfold cmult_def)
apply (safe dest!: le_subset_iff [THEN iffD1])
apply (rule well_ord_lepoll_imp_Card_le)
 apply (blast intro: well_ord_rmult well_ord_Memrel)
apply (blast intro: prod_lepoll_mono subset_imp_lepoll)
done

subsection{*Multiplication of finite cardinals is "ordinary" multiplication*}

lemma prod_succ_eqpoll: "succ(A)*B \<approx> B + A*B"
apply (unfold eqpoll_def)
apply (rule exI)
apply (rule_tac c = "%<x,y>. if x=A then Inl (y) else Inr (<x,y>)"
            and d = "case (%y. <A,y>, %z. z)" in lam_bijective)
apply safe
apply (simp_all add: succI2 if_type mem_imp_not_eq)
done

(*Unconditional version requires AC*)
lemma cmult_succ_lemma:
    "[| Ord(m);  Ord(n) |] ==> succ(m) \<otimes> n = n \<oplus> (m \<otimes> n)"
apply (unfold cmult_def cadd_def)
apply (rule prod_succ_eqpoll [THEN cardinal_cong, THEN trans])
apply (rule cardinal_cong [symmetric])
apply (rule sum_eqpoll_cong [OF eqpoll_refl well_ord_cardinal_eqpoll])
apply (blast intro: well_ord_rmult well_ord_Memrel)
done

lemma nat_cmult_eq_mult: "[| m \<in> nat;  n \<in> nat |] ==> m \<otimes> n = m#*n"
apply (induct_tac m)
apply (simp_all add: cmult_succ_lemma nat_cadd_eq_add)
done

lemma cmult_2: "Card(n) ==> 2 \<otimes> n = n \<oplus> n"
by (simp add: cmult_succ_lemma Card_is_Ord cadd_commute [of _ 0])

lemma sum_lepoll_prod:
  assumes C: "2 \<lesssim> C" shows "B+B \<lesssim> C*B"
proof -
  have "B+B \<lesssim> 2*B"
    by (simp add: sum_eq_2_times)
  also have "... \<lesssim> C*B"
    by (blast intro: prod_lepoll_mono lepoll_refl C)
  finally show "B+B \<lesssim> C*B" .
qed

lemma lepoll_imp_sum_lepoll_prod: "[| A \<lesssim> B; 2 \<lesssim> A |] ==> A+B \<lesssim> A*B"
by (blast intro: sum_lepoll_mono sum_lepoll_prod lepoll_trans lepoll_refl)


subsection{*Infinite Cardinals are Limit Ordinals*}

(*This proof is modelled upon one assuming nat<=A, with injection
  \<lambda>z\<in>cons(u,A). if z=u then 0 else if z \<in> nat then succ(z) else z
  and inverse %y. if y \<in> nat then nat_case(u, %z. z, y) else y.  \
  If f \<in> inj(nat,A) then range(f) behaves like the natural numbers.*)
lemma nat_cons_lepoll: "nat \<lesssim> A ==> cons(u,A) \<lesssim> A"
apply (unfold lepoll_def)
apply (erule exE)
apply (rule_tac x =
          "\<lambda>z\<in>cons (u,A).
             if z=u then f`0
             else if z \<in> range (f) then f`succ (converse (f) `z) else z"
       in exI)
apply (rule_tac d =
          "%y. if y \<in> range(f) then nat_case (u, %z. f`z, converse(f) `y)
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
lemma nat_succ_eqpoll: "nat \<subseteq> A ==> succ(A) \<approx> A"
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
    "[| InfCard(K);  Card(L) |] ==> InfCard(K \<union> L)"
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
apply (rule le_eqI, assumption)
apply (rule Ord_cardinal)
done


(*** An infinite cardinal equals its square (Kunen, Thm 10.12, page 29) ***)

(*A general fact about ordermap*)
lemma ordermap_eqpoll_pred:
    "[| well_ord(A,r);  x \<in> A |] ==> ordermap(A,r)`x \<approx> Order.pred(A,x,r)"
apply (unfold eqpoll_def)
apply (rule exI)
apply (simp add: ordermap_eq_image well_ord_is_wf)
apply (erule ordermap_bij [THEN bij_is_inj, THEN restrict_bij,
                           THEN bij_converse_bij])
apply (rule pred_subset)
done

subsubsection{*Establishing the well-ordering*}

lemma well_ord_csquare:
  assumes K: "Ord(K)" shows "well_ord(K*K, csquare_rel(K))"
proof (unfold csquare_rel_def, rule well_ord_rvimage)
  show "(\<lambda>\<langle>x,y\<rangle>\<in>K \<times> K. \<langle>x \<union> y, x, y\<rangle>) \<in> inj(K \<times> K, K \<times> K \<times> K)" using K
    by (force simp add: inj_def intro: lam_type Un_least_lt [THEN ltD] ltI)
next
  show "well_ord(K \<times> K \<times> K, rmult(K, Memrel(K), K \<times> K, rmult(K, Memrel(K), K, Memrel(K))))"
    using K by (blast intro: well_ord_rmult well_ord_Memrel)
qed

subsubsection{*Characterising initial segments of the well-ordering*}

lemma csquareD:
 "[| <<x,y>, <z,z>> \<in> csquare_rel(K);  x<K;  y<K;  z<K |] ==> x \<le> z & y \<le> z"
apply (unfold csquare_rel_def)
apply (erule rev_mp)
apply (elim ltE)
apply (simp add: rvimage_iff Un_absorb Un_least_mem_iff ltD)
apply (safe elim!: mem_irrefl intro!: Un_upper1_le Un_upper2_le)
apply (simp_all add: lt_def succI2)
done

lemma pred_csquare_subset:
    "z<K ==> Order.pred(K*K, <z,z>, csquare_rel(K)) \<subseteq> succ(z)*succ(z)"
apply (unfold Order.pred_def)
apply (safe del: SigmaI dest!: csquareD)
apply (unfold lt_def, auto)
done

lemma csquare_ltI:
 "[| x<z;  y<z;  z<K |] ==>  <<x,y>, <z,z>> \<in> csquare_rel(K)"
apply (unfold csquare_rel_def)
apply (subgoal_tac "x<K & y<K")
 prefer 2 apply (blast intro: lt_trans)
apply (elim ltE)
apply (simp add: rvimage_iff Un_absorb Un_least_mem_iff ltD)
done

(*Part of the traditional proof.  UNUSED since it's harder to prove & apply *)
lemma csquare_or_eqI:
 "[| x \<le> z;  y \<le> z;  z<K |] ==> <<x,y>, <z,z>> \<in> csquare_rel(K) | x=z & y=z"
apply (unfold csquare_rel_def)
apply (subgoal_tac "x<K & y<K")
 prefer 2 apply (blast intro: lt_trans1)
apply (elim ltE)
apply (simp add: rvimage_iff Un_absorb Un_least_mem_iff ltD)
apply (elim succE)
apply (simp_all add: subset_Un_iff [THEN iff_sym]
                     subset_Un_iff2 [THEN iff_sym] OrdmemD)
done

subsubsection{*The cardinality of initial segments*}

lemma ordermap_z_lt:
      "[| Limit(K);  x<K;  y<K;  z=succ(x \<union> y) |] ==>
          ordermap(K*K, csquare_rel(K)) ` <x,y> <
          ordermap(K*K, csquare_rel(K)) ` <z,z>"
apply (subgoal_tac "z<K & well_ord (K*K, csquare_rel (K))")
prefer 2 apply (blast intro!: Un_least_lt Limit_has_succ
                              Limit_is_Ord [THEN well_ord_csquare], clarify)
apply (rule csquare_ltI [THEN ordermap_mono, THEN ltI])
apply (erule_tac [4] well_ord_is_wf)
apply (blast intro!: Un_upper1_le Un_upper2_le Ord_ordermap elim!: ltE)+
done

text{*Kunen: "each @{term"\<langle>x,y\<rangle> \<in> K \<times> K"} has no more than @{term"z \<times> z"} predecessors..." (page 29) *}
lemma ordermap_csquare_le:
  assumes K: "Limit(K)" and x: "x<K" and y: " y<K"
  defines "z \<equiv> succ(x \<union> y)"
  shows "|ordermap(K \<times> K, csquare_rel(K)) ` \<langle>x,y\<rangle>| \<le> |succ(z)| \<otimes> |succ(z)|"
proof (unfold cmult_def, rule well_ord_lepoll_imp_Card_le)
  show "well_ord(|succ(z)| \<times> |succ(z)|,
                 rmult(|succ(z)|, Memrel(|succ(z)|), |succ(z)|, Memrel(|succ(z)|)))"
    by (blast intro: Ord_cardinal well_ord_Memrel well_ord_rmult)
next
  have zK: "z<K" using x y K z_def
    by (blast intro: Un_least_lt Limit_has_succ)
  hence oz: "Ord(z)" by (elim ltE)
  have "ordermap(K \<times> K, csquare_rel(K)) ` \<langle>x,y\<rangle> \<lesssim> ordermap(K \<times> K, csquare_rel(K)) ` \<langle>z,z\<rangle>"
    using z_def
    by (blast intro: ordermap_z_lt leI le_imp_lepoll K x y)
  also have "... \<approx>  Order.pred(K \<times> K, \<langle>z,z\<rangle>, csquare_rel(K))"
    proof (rule ordermap_eqpoll_pred)
      show "well_ord(K \<times> K, csquare_rel(K))" using K
        by (rule Limit_is_Ord [THEN well_ord_csquare])
    next
      show "\<langle>z, z\<rangle> \<in> K \<times> K" using zK
        by (blast intro: ltD)
    qed
  also have "...  \<lesssim> succ(z) \<times> succ(z)" using zK
    by (rule pred_csquare_subset [THEN subset_imp_lepoll])
  also have "... \<approx> |succ(z)| \<times> |succ(z)|" using oz
    by (blast intro: prod_eqpoll_cong Ord_succ Ord_cardinal_eqpoll eqpoll_sym)
  finally show "ordermap(K \<times> K, csquare_rel(K)) ` \<langle>x,y\<rangle> \<lesssim> |succ(z)| \<times> |succ(z)|" .
qed

text{*Kunen: "... so the order type is @{text"\<le>"} K" *}
lemma ordertype_csquare_le:
  assumes IK: "InfCard(K)" and eq: "\<And>y. y\<in>K \<Longrightarrow> InfCard(y) \<Longrightarrow> y \<otimes> y = y"
  shows "ordertype(K*K, csquare_rel(K)) \<le> K"
proof -
  have  CK: "Card(K)" using IK by (rule InfCard_is_Card)
  hence OK: "Ord(K)"  by (rule Card_is_Ord)
  moreover have "Ord(ordertype(K \<times> K, csquare_rel(K)))" using OK
    by (rule well_ord_csquare [THEN Ord_ordertype])
  ultimately show ?thesis
  proof (rule all_lt_imp_le)
    fix i
    assume i: "i < ordertype(K \<times> K, csquare_rel(K))"
    hence Oi: "Ord(i)" by (elim ltE)
    obtain x y where x: "x \<in> K" and y: "y \<in> K"
                 and ieq: "i = ordermap(K \<times> K, csquare_rel(K)) ` \<langle>x,y\<rangle>"
      using i by (auto simp add: ordertype_unfold elim: ltE)
    hence xy: "Ord(x)" "Ord(y)" "x < K" "y < K" using OK
      by (blast intro: Ord_in_Ord ltI)+
    hence ou: "Ord(x \<union> y)"
      by (simp add: Ord_Un)
    show "i < K"
      proof (rule Card_lt_imp_lt [OF _ Oi CK])
        have "|i| \<le> |succ(succ(x \<union> y))| \<otimes> |succ(succ(x \<union> y))|" using IK xy
          by (auto simp add: ieq intro: InfCard_is_Limit [THEN ordermap_csquare_le])
        moreover have "|succ(succ(x \<union> y))| \<otimes> |succ(succ(x \<union> y))| < K"
          proof (cases rule: Ord_linear2 [OF ou Ord_nat])
            assume "x \<union> y < nat"
            hence "|succ(succ(x \<union> y))| \<otimes> |succ(succ(x \<union> y))| \<in> nat"
              by (simp add: lt_def nat_cmult_eq_mult nat_succI mult_type
                         nat_into_Card [THEN Card_cardinal_eq]  Ord_nat)
            also have "... \<subseteq> K" using IK
              by (simp add: InfCard_def le_imp_subset)
            finally show "|succ(succ(x \<union> y))| \<otimes> |succ(succ(x \<union> y))| < K"
              by (simp add: ltI OK)
          next
            assume natxy: "nat \<le> x \<union> y"
            hence seq: "|succ(succ(x \<union> y))| = |x \<union> y|" using xy
              by (simp add: le_imp_subset nat_succ_eqpoll [THEN cardinal_cong] le_succ_iff)
            also have "... < K" using xy
              by (simp add: Un_least_lt Ord_cardinal_le [THEN lt_trans1])
            finally have "|succ(succ(x \<union> y))| < K" .
            moreover have "InfCard(|succ(succ(x \<union> y))|)" using xy natxy
              by (simp add: seq InfCard_def Card_cardinal nat_le_cardinal)
            ultimately show ?thesis  by (simp add: eq ltD)
          qed
        ultimately show "|i| < K" by (blast intro: lt_trans1)
    qed
  qed
qed

(*Main result: Kunen's Theorem 10.12*)
lemma InfCard_csquare_eq:
  assumes IK: "InfCard(K)" shows "InfCard(K) ==> K \<otimes> K = K"
proof -
  have  OK: "Ord(K)" using IK by (simp add: Card_is_Ord InfCard_is_Card)
  show "InfCard(K) ==> K \<otimes> K = K" using OK
  proof (induct rule: trans_induct)
    case (step i)
    show "i \<otimes> i = i"
    proof (rule le_anti_sym)
      have "|i \<times> i| = |ordertype(i \<times> i, csquare_rel(i))|"
        by (rule cardinal_cong,
          simp add: step.hyps well_ord_csquare [THEN ordermap_bij, THEN bij_imp_eqpoll])
      hence "i \<otimes> i \<le> ordertype(i \<times> i, csquare_rel(i))"
        by (simp add: step.hyps cmult_def Ord_cardinal_le well_ord_csquare [THEN Ord_ordertype])
      moreover
      have "ordertype(i \<times> i, csquare_rel(i)) \<le> i" using step
        by (simp add: ordertype_csquare_le)
      ultimately show "i \<otimes> i \<le> i" by (rule le_trans)
    next
      show "i \<le> i \<otimes> i" using step
        by (blast intro: cmult_square_le InfCard_is_Card)
    qed
  qed
qed

(*Corollary for arbitrary well-ordered sets (all sets, assuming AC)*)
lemma well_ord_InfCard_square_eq:
  assumes r: "well_ord(A,r)" and I: "InfCard(|A|)" shows "A \<times> A \<approx> A"
proof -
  have "A \<times> A \<approx> |A| \<times> |A|"
    by (blast intro: prod_eqpoll_cong well_ord_cardinal_eqpoll eqpoll_sym r)
  also have "... \<approx> A"
    proof (rule well_ord_cardinal_eqE [OF _ r])
      show "well_ord(|A| \<times> |A|, rmult(|A|, Memrel(|A|), |A|, Memrel(|A|)))"
        by (blast intro: Ord_cardinal well_ord_rmult well_ord_Memrel r)
    next
      show "||A| \<times> |A|| = |A|" using InfCard_csquare_eq I
        by (simp add: cmult_def)
    qed
  finally show ?thesis .
qed

lemma InfCard_square_eqpoll: "InfCard(K) ==> K \<times> K \<approx> K"
apply (rule well_ord_InfCard_square_eq)
 apply (erule InfCard_is_Card [THEN Card_is_Ord, THEN well_ord_Memrel])
apply (simp add: InfCard_is_Card [THEN Card_cardinal_eq])
done

lemma Inf_Card_is_InfCard: "[| ~Finite(i); Card(i) |] ==> InfCard(i)"
by (simp add: InfCard_def Card_is_Ord [THEN nat_le_infinite_Ord])

subsubsection{*Toward's Kunen's Corollary 10.13 (1)*}

lemma InfCard_le_cmult_eq: "[| InfCard(K);  L \<le> K;  0<L |] ==> K \<otimes> L = K"
apply (rule le_anti_sym)
 prefer 2
 apply (erule ltE, blast intro: cmult_le_self InfCard_is_Card)
apply (frule InfCard_is_Card [THEN Card_is_Ord, THEN le_refl])
apply (rule cmult_le_mono [THEN le_trans], assumption+)
apply (simp add: InfCard_csquare_eq)
done

(*Corollary 10.13 (1), for cardinal multiplication*)
lemma InfCard_cmult_eq: "[| InfCard(K);  InfCard(L) |] ==> K \<otimes> L = K \<union> L"
apply (rule_tac i = K and j = L in Ord_linear_le)
apply (typecheck add: InfCard_is_Card Card_is_Ord)
apply (rule cmult_commute [THEN ssubst])
apply (rule Un_commute [THEN ssubst])
apply (simp_all add: InfCard_is_Limit [THEN Limit_has_0] InfCard_le_cmult_eq
                     subset_Un_iff2 [THEN iffD1] le_imp_subset)
done

lemma InfCard_cdouble_eq: "InfCard(K) ==> K \<oplus> K = K"
apply (simp add: cmult_2 [symmetric] InfCard_is_Card cmult_commute)
apply (simp add: InfCard_le_cmult_eq InfCard_is_Limit Limit_has_0 Limit_has_succ)
done

(*Corollary 10.13 (1), for cardinal addition*)
lemma InfCard_le_cadd_eq: "[| InfCard(K);  L \<le> K |] ==> K \<oplus> L = K"
apply (rule le_anti_sym)
 prefer 2
 apply (erule ltE, blast intro: cadd_le_self InfCard_is_Card)
apply (frule InfCard_is_Card [THEN Card_is_Ord, THEN le_refl])
apply (rule cadd_le_mono [THEN le_trans], assumption+)
apply (simp add: InfCard_cdouble_eq)
done

lemma InfCard_cadd_eq: "[| InfCard(K);  InfCard(L) |] ==> K \<oplus> L = K \<union> L"
apply (rule_tac i = K and j = L in Ord_linear_le)
apply (typecheck add: InfCard_is_Card Card_is_Ord)
apply (rule cadd_commute [THEN ssubst])
apply (rule Un_commute [THEN ssubst])
apply (simp_all add: InfCard_le_cadd_eq subset_Un_iff2 [THEN iffD1] le_imp_subset)
done

(*The other part, Corollary 10.13 (2), refers to the cardinality of the set
  of all n-tuples of elements of K.  A better version for the Isabelle theory
  might be  InfCard(K) ==> |list(K)| = K.
*)

subsection{*For Every Cardinal Number There Exists A Greater One*}

text{*This result is Kunen's Theorem 10.16, which would be trivial using AC*}

lemma Ord_jump_cardinal: "Ord(jump_cardinal(K))"
apply (unfold jump_cardinal_def)
apply (rule Ord_is_Transset [THEN [2] OrdI])
 prefer 2 apply (blast intro!: Ord_ordertype)
apply (unfold Transset_def)
apply (safe del: subsetI)
apply (simp add: ordertype_pred_unfold, safe)
apply (rule UN_I)
apply (rule_tac [2] ReplaceI)
   prefer 4 apply (blast intro: well_ord_subset elim!: predE)+
done

(*Allows selective unfolding.  Less work than deriving intro/elim rules*)
lemma jump_cardinal_iff:
     "i \<in> jump_cardinal(K) \<longleftrightarrow>
      (\<exists>r X. r \<subseteq> K*K & X \<subseteq> K & well_ord(X,r) & i = ordertype(X,r))"
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
     "[| well_ord(X,r);  r \<subseteq> K * K;  X \<subseteq> K;
         f \<in> bij(ordertype(X,r), jump_cardinal(K)) |]
      ==> jump_cardinal(K) \<in> jump_cardinal(K)"
apply (subgoal_tac "f O ordermap (X,r) \<in> bij (X, jump_cardinal (K))")
 prefer 2 apply (blast intro: comp_bij ordermap_bij)
apply (rule jump_cardinal_iff [THEN iffD2])
apply (intro exI conjI)
apply (rule subset_trans [OF rvimage_type Sigma_mono], assumption+)
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

subsection{*Basic Properties of Successor Cardinals*}

lemma csucc_basic: "Ord(K) ==> Card(csucc(K)) & K < csucc(K)"
apply (unfold csucc_def)
apply (rule LeastI)
apply (blast intro: Card_jump_cardinal K_lt_jump_cardinal Ord_jump_cardinal)+
done

lemmas Card_csucc = csucc_basic [THEN conjunct1]

lemmas lt_csucc = csucc_basic [THEN conjunct2]

lemma Ord_0_lt_csucc: "Ord(K) ==> 0 < csucc(K)"
by (blast intro: Ord_0_le lt_csucc lt_trans1)

lemma csucc_le: "[| Card(L);  K<L |] ==> csucc(K) \<le> L"
apply (unfold csucc_def)
apply (rule Least_le)
apply (blast intro: Card_is_Ord)+
done

lemma lt_csucc_iff: "[| Ord(i); Card(K) |] ==> i < csucc(K) \<longleftrightarrow> |i| \<le> K"
apply (rule iffI)
apply (rule_tac [2] Card_lt_imp_lt)
apply (erule_tac [2] lt_trans1)
apply (simp_all add: lt_csucc Card_csucc Card_is_Ord)
apply (rule notI [THEN not_lt_imp_le])
apply (rule Card_cardinal [THEN csucc_le, THEN lt_trans1, THEN lt_irrefl], assumption)
apply (rule Ord_cardinal_le [THEN lt_trans1])
apply (simp_all add: Ord_cardinal Card_is_Ord)
done

lemma Card_lt_csucc_iff:
     "[| Card(K'); Card(K) |] ==> K' < csucc(K) \<longleftrightarrow> K' \<le> K"
by (simp add: lt_csucc_iff Card_cardinal_eq Card_is_Ord)

lemma InfCard_csucc: "InfCard(K) ==> InfCard(csucc(K))"
by (simp add: InfCard_def Card_csucc Card_is_Ord
              lt_csucc [THEN leI, THEN [2] le_trans])


subsubsection{*Removing elements from a finite set decreases its cardinality*}

lemma Finite_imp_cardinal_cons [simp]:
  assumes FA: "Finite(A)" and a: "a\<notin>A" shows "|cons(a,A)| = succ(|A|)"
proof -
  { fix X
    have "Finite(X) ==> a \<notin> X \<Longrightarrow> cons(a,X) \<lesssim> X \<Longrightarrow> False"
      proof (induct X rule: Finite_induct)
        case 0 thus False  by (simp add: lepoll_0_iff)
      next
        case (cons x Y)
        hence "cons(x, cons(a, Y)) \<lesssim> cons(x, Y)" by (simp add: cons_commute)
        hence "cons(a, Y) \<lesssim> Y" using cons        by (blast dest: cons_lepoll_consD)
        thus False using cons by auto
      qed
  }
  hence [simp]: "~ cons(a,A) \<lesssim> A" using a FA by auto
  have [simp]: "|A| \<approx> A" using Finite_imp_well_ord [OF FA]
    by (blast intro: well_ord_cardinal_eqpoll)
  have "(\<mu> i. i \<approx> cons(a, A)) = succ(|A|)"
    proof (rule Least_equality [OF _ _ notI])
      show "succ(|A|) \<approx> cons(a, A)"
        by (simp add: succ_def cons_eqpoll_cong mem_not_refl a)
    next
      show "Ord(succ(|A|))" by simp
    next
      fix i
      assume i: "i \<le> |A|" "i \<approx> cons(a, A)"
      have "cons(a, A) \<approx> i" by (rule eqpoll_sym) (rule i)
      also have "... \<lesssim> |A|" by (rule le_imp_lepoll) (rule i)
      also have "... \<approx> A"   by simp
      finally have "cons(a, A) \<lesssim> A" .
      thus False by simp
    qed
  thus ?thesis by (simp add: cardinal_def)
qed

lemma Finite_imp_succ_cardinal_Diff:
     "[| Finite(A);  a \<in> A |] ==> succ(|A-{a}|) = |A|"
apply (rule_tac b = A in cons_Diff [THEN subst], assumption)
apply (simp add: Finite_imp_cardinal_cons Diff_subset [THEN subset_Finite])
apply (simp add: cons_Diff)
done

lemma Finite_imp_cardinal_Diff: "[| Finite(A);  a \<in> A |] ==> |A-{a}| < |A|"
apply (rule succ_leE)
apply (simp add: Finite_imp_succ_cardinal_Diff)
done

lemma Finite_cardinal_in_nat [simp]: "Finite(A) ==> |A| \<in> nat"
proof (induct rule: Finite_induct)
  case 0 thus ?case by (simp add: cardinal_0)
next
  case (cons x A) thus ?case by (simp add: Finite_imp_cardinal_cons)
qed

lemma card_Un_Int:
     "[|Finite(A); Finite(B)|] ==> |A| #+ |B| = |A \<union> B| #+ |A \<inter> B|"
apply (erule Finite_induct, simp)
apply (simp add: Finite_Int cons_absorb Un_cons Int_cons_left)
done

lemma card_Un_disjoint:
     "[|Finite(A); Finite(B); A \<inter> B = 0|] ==> |A \<union> B| = |A| #+ |B|"
by (simp add: Finite_Un card_Un_Int)

lemma card_partition:
  assumes FC: "Finite(C)"
  shows
     "Finite (\<Union> C) \<Longrightarrow>
        (\<forall>c\<in>C. |c| = k) \<Longrightarrow>
        (\<forall>c1 \<in> C. \<forall>c2 \<in> C. c1 \<noteq> c2 \<longrightarrow> c1 \<inter> c2 = 0) \<Longrightarrow>
        k #* |C| = |\<Union> C|"
using FC
proof (induct rule: Finite_induct)
  case 0 thus ?case by simp
next
  case (cons x B)
  hence "x \<inter> \<Union>B = 0" by auto
  thus ?case using cons
    by (auto simp add: card_Un_disjoint)
qed


subsubsection{*Theorems by Krzysztof Grabczewski, proofs by lcp*}

lemmas nat_implies_well_ord = nat_into_Ord [THEN well_ord_Memrel]

lemma nat_sum_eqpoll_sum:
  assumes m: "m \<in> nat" and n: "n \<in> nat" shows "m + n \<approx> m #+ n"
proof -
  have "m + n \<approx> |m+n|" using m n
    by (blast intro: nat_implies_well_ord well_ord_radd well_ord_cardinal_eqpoll eqpoll_sym)
  also have "... = m #+ n" using m n
    by (simp add: nat_cadd_eq_add [symmetric] cadd_def)
  finally show ?thesis .
qed

lemma Ord_subset_natD [rule_format]: "Ord(i) ==> i \<subseteq> nat \<Longrightarrow> i \<in> nat | i=nat"
proof (induct i rule: trans_induct3)
  case 0 thus ?case by auto
next
  case (succ i) thus ?case by auto
next
  case (limit l) thus ?case
    by (blast dest: nat_le_Limit le_imp_subset)
qed

lemma Ord_nat_subset_into_Card: "[| Ord(i); i \<subseteq> nat |] ==> Card(i)"
by (blast dest: Ord_subset_natD intro: Card_nat nat_into_Card)

end
