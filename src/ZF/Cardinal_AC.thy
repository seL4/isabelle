(*  Title:      ZF/Cardinal_AC.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

These results help justify infinite-branching datatypes
*)

header{*Cardinal Arithmetic Using AC*}

theory Cardinal_AC imports CardinalArith Zorn begin

subsection{*Strengthened Forms of Existing Theorems on Cardinals*}

lemma cardinal_eqpoll: "|A| \<approx> A"
apply (rule AC_well_ord [THEN exE])
apply (erule well_ord_cardinal_eqpoll)
done

text{*The theorem @{term "||A|| = |A|"} *}
lemmas cardinal_idem = cardinal_eqpoll [THEN cardinal_cong, simp]

lemma cardinal_eqE: "|X| = |Y| ==> X \<approx> Y"
apply (rule AC_well_ord [THEN exE])
apply (rule AC_well_ord [THEN exE])
apply (rule well_ord_cardinal_eqE, assumption+)
done

lemma cardinal_eqpoll_iff: "|X| = |Y| \<longleftrightarrow> X \<approx> Y"
by (blast intro: cardinal_cong cardinal_eqE)

lemma cardinal_disjoint_Un:
     "[| |A|=|B|;  |C|=|D|;  A \<inter> C = 0;  B \<inter> D = 0 |]
      ==> |A \<union> C| = |B \<union> D|"
by (simp add: cardinal_eqpoll_iff eqpoll_disjoint_Un)

lemma lepoll_imp_Card_le: "A \<lesssim> B ==> |A| \<le> |B|"
apply (rule AC_well_ord [THEN exE])
apply (erule well_ord_lepoll_imp_Card_le, assumption)
done

lemma cadd_assoc: "(i \<oplus> j) \<oplus> k = i \<oplus> (j \<oplus> k)"
apply (rule AC_well_ord [THEN exE])
apply (rule AC_well_ord [THEN exE])
apply (rule AC_well_ord [THEN exE])
apply (rule well_ord_cadd_assoc, assumption+)
done

lemma cmult_assoc: "(i \<otimes> j) \<otimes> k = i \<otimes> (j \<otimes> k)"
apply (rule AC_well_ord [THEN exE])
apply (rule AC_well_ord [THEN exE])
apply (rule AC_well_ord [THEN exE])
apply (rule well_ord_cmult_assoc, assumption+)
done

lemma cadd_cmult_distrib: "(i \<oplus> j) \<otimes> k = (i \<otimes> k) \<oplus> (j \<otimes> k)"
apply (rule AC_well_ord [THEN exE])
apply (rule AC_well_ord [THEN exE])
apply (rule AC_well_ord [THEN exE])
apply (rule well_ord_cadd_cmult_distrib, assumption+)
done

lemma InfCard_square_eq: "InfCard(|A|) ==> A*A \<approx> A"
apply (rule AC_well_ord [THEN exE])
apply (erule well_ord_InfCard_square_eq, assumption)
done


subsection {*The relationship between cardinality and le-pollence*}

lemma Card_le_imp_lepoll:
  assumes "|A| \<le> |B|" shows "A \<lesssim> B"
proof -
  have "A \<approx> |A|" 
    by (rule cardinal_eqpoll [THEN eqpoll_sym])
  also have "... \<lesssim> |B|"
    by (rule le_imp_subset [THEN subset_imp_lepoll]) (rule assms)
  also have "... \<approx> B" 
    by (rule cardinal_eqpoll)
  finally show ?thesis .
qed

lemma le_Card_iff: "Card(K) ==> |A| \<le> K \<longleftrightarrow> A \<lesssim> K"
apply (erule Card_cardinal_eq [THEN subst], rule iffI,
       erule Card_le_imp_lepoll)
apply (erule lepoll_imp_Card_le)
done

lemma cardinal_0_iff_0 [simp]: "|A| = 0 \<longleftrightarrow> A = 0"
apply auto
apply (drule cardinal_0 [THEN ssubst])
apply (blast intro: eqpoll_0_iff [THEN iffD1] cardinal_eqpoll_iff [THEN iffD1])
done

lemma cardinal_lt_iff_lesspoll:
  assumes i: "Ord(i)" shows "i < |A| \<longleftrightarrow> i \<prec> A"
proof
  assume "i < |A|"
  hence  "i \<prec> |A|" 
    by (blast intro: lt_Card_imp_lesspoll Card_cardinal) 
  also have "...  \<approx> A" 
    by (rule cardinal_eqpoll)
  finally show "i \<prec> A" .
next
  assume "i \<prec> A"
  also have "...  \<approx> |A|" 
    by (blast intro: cardinal_eqpoll eqpoll_sym) 
  finally have "i \<prec> |A|" .
  thus  "i < |A|" using i
    by (force intro: cardinal_lt_imp_lt lesspoll_cardinal_lt)
qed

lemma cardinal_le_imp_lepoll: " i \<le> |A| ==> i \<lesssim> A"
  by (blast intro: lt_Ord Card_le_imp_lepoll Ord_cardinal_le le_trans)


subsection{*Other Applications of AC*}

lemma surj_implies_inj:
  assumes f: "f \<in> surj(X,Y)" shows "\<exists>g. g \<in> inj(Y,X)"
proof -
  from f AC_Pi [of Y "%y. f-``{y}"]
  obtain z where z: "z \<in> (\<Pi> y\<in>Y. f -`` {y})"  
    by (auto simp add: surj_def) (fast dest: apply_Pair)
  show ?thesis
    proof
      show "z \<in> inj(Y, X)" using z surj_is_fun [OF f]
        by (blast dest: apply_type Pi_memberD
                  intro: apply_equality Pi_type f_imp_injective)
    qed
qed

text{*Kunen's Lemma 10.20*}
lemma surj_implies_cardinal_le: 
  assumes f: "f \<in> surj(X,Y)" shows "|Y| \<le> |X|"
proof (rule lepoll_imp_Card_le)
  from f [THEN surj_implies_inj] obtain g where "g \<in> inj(Y,X)" ..
  thus "Y \<lesssim> X"
    by (auto simp add: lepoll_def)
qed

text{*Kunen's Lemma 10.21*}
lemma cardinal_UN_le:
  assumes K: "InfCard(K)" 
  shows "(!!i. i\<in>K ==> |X(i)| \<le> K) ==> |\<Union>i\<in>K. X(i)| \<le> K"
proof (simp add: K InfCard_is_Card le_Card_iff)
  have [intro]: "Ord(K)" by (blast intro: InfCard_is_Card Card_is_Ord K) 
  assume "!!i. i\<in>K ==> X(i) \<lesssim> K"
  hence "!!i. i\<in>K ==> \<exists>f. f \<in> inj(X(i), K)" by (simp add: lepoll_def) 
  with AC_Pi obtain f where f: "f \<in> (\<Pi> i\<in>K. inj(X(i), K))"
    by force 
  { fix z
    assume z: "z \<in> (\<Union>i\<in>K. X(i))"
    then obtain i where i: "i \<in> K" "Ord(i)" "z \<in> X(i)"
      by (blast intro: Ord_in_Ord [of K]) 
    hence "(LEAST i. z \<in> X(i)) \<le> i" by (fast intro: Least_le) 
    hence "(LEAST i. z \<in> X(i)) < K" by (best intro: lt_trans1 ltI i) 
    hence "(LEAST i. z \<in> X(i)) \<in> K" and "z \<in> X(LEAST i. z \<in> X(i))"  
      by (auto intro: LeastI ltD i) 
  } note mems = this
  have "(\<Union>i\<in>K. X(i)) \<lesssim> K \<times> K" 
    proof (unfold lepoll_def)
      show "\<exists>f. f \<in> inj(\<Union>RepFun(K, X), K \<times> K)"
        apply (rule exI) 
        apply (rule_tac c = "%z. \<langle>LEAST i. z \<in> X(i), f ` (LEAST i. z \<in> X(i)) ` z\<rangle>"
                    and d = "%\<langle>i,j\<rangle>. converse (f`i) ` j" in lam_injective) 
        apply (force intro: f inj_is_fun mems apply_type Perm.left_inverse)+
        done
    qed
  also have "... \<approx> K" 
    by (simp add: K InfCard_square_eq InfCard_is_Card Card_cardinal_eq)
  finally show "(\<Union>i\<in>K. X(i)) \<lesssim> K" .
qed

text{*The same again, using @{term csucc}*}
lemma cardinal_UN_lt_csucc:
     "[| InfCard(K);  \<And>i. i\<in>K \<Longrightarrow> |X(i)| < csucc(K) |]
      ==> |\<Union>i\<in>K. X(i)| < csucc(K)"
by (simp add: Card_lt_csucc_iff cardinal_UN_le InfCard_is_Card Card_cardinal)

text{*The same again, for a union of ordinals.  In use, j(i) is a bit like rank(i),
  the least ordinal j such that i:Vfrom(A,j). *}
lemma cardinal_UN_Ord_lt_csucc:
     "[| InfCard(K);  \<And>i. i\<in>K \<Longrightarrow> j(i) < csucc(K) |]
      ==> (\<Union>i\<in>K. j(i)) < csucc(K)"
apply (rule cardinal_UN_lt_csucc [THEN Card_lt_imp_lt], assumption)
apply (blast intro: Ord_cardinal_le [THEN lt_trans1] elim: ltE)
apply (blast intro!: Ord_UN elim: ltE)
apply (erule InfCard_is_Card [THEN Card_is_Ord, THEN Card_csucc])
done


subsection{*The Main Result for Infinite-Branching Datatypes*}

text{*As above, but the index set need not be a cardinal. Work
backwards along the injection from @{term W} into @{term K}, given
that @{term"W\<noteq>0"}.*}

lemma inj_UN_subset:
  assumes f: "f \<in> inj(A,B)" and a: "a \<in> A"
  shows "(\<Union>x\<in>A. C(x)) \<subseteq> (\<Union>y\<in>B. C(if y \<in> range(f) then converse(f)`y else a))"
proof (rule UN_least)
  fix x
  assume x: "x \<in> A"
  hence fx: "f ` x \<in> B" by (blast intro: f inj_is_fun [THEN apply_type])
  have "C(x) \<subseteq> C(if f ` x \<in> range(f) then converse(f) ` (f ` x) else a)" 
    using f x by (simp add: inj_is_fun [THEN apply_rangeI])
  also have "... \<subseteq> (\<Union>y\<in>B. C(if y \<in> range(f) then converse(f) ` y else a))"
    by (rule UN_upper [OF fx]) 
  finally show "C(x) \<subseteq> (\<Union>y\<in>B. C(if y \<in> range(f) then converse(f)`y else a))" .
qed

theorem le_UN_Ord_lt_csucc:
  assumes IK: "InfCard(K)" and WK: "|W| \<le> K" and j: "\<And>w. w\<in>W \<Longrightarrow> j(w) < csucc(K)"
  shows "(\<Union>w\<in>W. j(w)) < csucc(K)"
proof -
  have CK: "Card(K)" 
    by (simp add: InfCard_is_Card IK)
  then obtain f where f: "f \<in> inj(W, K)" using WK
    by(auto simp add: le_Card_iff lepoll_def)
  have OU: "Ord(\<Union>w\<in>W. j(w))" using j
    by (blast elim: ltE)
  note lt_subset_trans [OF _ _ OU, trans]
  show ?thesis
    proof (cases "W=0")
      case True  --{*solve the easy 0 case*}
      thus ?thesis by (simp add: CK Card_is_Ord Card_csucc Ord_0_lt_csucc)
    next
      case False
        then obtain x where x: "x \<in> W" by blast
        have "(\<Union>x\<in>W. j(x)) \<subseteq> (\<Union>k\<in>K. j(if k \<in> range(f) then converse(f) ` k else x))"
          by (rule inj_UN_subset [OF f x]) 
        also have "... < csucc(K)" using IK
          proof (rule cardinal_UN_Ord_lt_csucc)
            fix k
            assume "k \<in> K"
            thus "j(if k \<in> range(f) then converse(f) ` k else x) < csucc(K)" using f x j
              by (simp add: inj_converse_fun [THEN apply_type])
          qed
        finally show ?thesis .
    qed
qed

end
