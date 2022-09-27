(*  Title:      ZF/Epsilon.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge
*)

section\<open>Epsilon Induction and Recursion\<close>

theory Epsilon imports Nat begin

definition
  eclose    :: "i=>i"  where
    "eclose(A) \<equiv> \<Union>n\<in>nat. nat_rec(n, A, %m r. \<Union>(r))"

definition
  transrec  :: "[i, [i,i]=>i] =>i"  where
    "transrec(a,H) \<equiv> wfrec(Memrel(eclose({a})), a, H)"

definition
  rank      :: "i=>i"  where
    "rank(a) \<equiv> transrec(a, %x f. \<Union>y\<in>x. succ(f`y))"

definition
  transrec2 :: "[i, i, [i,i]=>i] =>i"  where
    "transrec2(k, a, b) \<equiv>
       transrec(k,
                %i r. if(i=0, a,
                        if(\<exists>j. i=succ(j),
                           b(THE j. i=succ(j), r`(THE j. i=succ(j))),
                           \<Union>j<i. r`j)))"

definition
  recursor  :: "[i, [i,i]=>i, i]=>i"  where
    "recursor(a,b,k) \<equiv>  transrec(k, %n f. nat_case(a, %m. b(m, f`m), n))"

definition
  rec  :: "[i, i, [i,i]=>i]=>i"  where
    "rec(k,a,b) \<equiv> recursor(a,b,k)"


subsection\<open>Basic Closure Properties\<close>

lemma arg_subset_eclose: "A \<subseteq> eclose(A)"
apply (unfold eclose_def)
apply (rule nat_rec_0 [THEN equalityD2, THEN subset_trans])
apply (rule nat_0I [THEN UN_upper])
done

lemmas arg_into_eclose = arg_subset_eclose [THEN subsetD]

lemma Transset_eclose: "Transset(eclose(A))"
apply (unfold eclose_def Transset_def)
apply (rule subsetI [THEN ballI])
apply (erule UN_E)
apply (rule nat_succI [THEN UN_I], assumption)
apply (erule nat_rec_succ [THEN ssubst])
apply (erule UnionI, assumption)
done

(* @{term"x \<in> eclose(A) \<Longrightarrow> x \<subseteq> eclose(A)"} *)
lemmas eclose_subset =
       Transset_eclose [unfolded Transset_def, THEN bspec]

(* @{term"\<lbrakk>A \<in> eclose(B); c \<in> A\<rbrakk> \<Longrightarrow> c \<in> eclose(B)"} *)
lemmas ecloseD = eclose_subset [THEN subsetD]

lemmas arg_in_eclose_sing = arg_subset_eclose [THEN singleton_subsetD]
lemmas arg_into_eclose_sing = arg_in_eclose_sing [THEN ecloseD]

(* This is epsilon-induction for eclose(A); see also eclose_induct_down...
   \<lbrakk>a \<in> eclose(A);  \<And>x. \<lbrakk>x \<in> eclose(A); \<forall>y\<in>x. P(y)\<rbrakk> \<Longrightarrow> P(x)
\<rbrakk> \<Longrightarrow> P(a)
*)
lemmas eclose_induct =
     Transset_induct [OF _ Transset_eclose, induct set: eclose]


(*Epsilon induction*)
lemma eps_induct:
    "\<lbrakk>\<And>x. \<forall>y\<in>x. P(y) \<Longrightarrow> P(x)\<rbrakk>  \<Longrightarrow>  P(a)"
by (rule arg_in_eclose_sing [THEN eclose_induct], blast)


subsection\<open>Leastness of \<^term>\<open>eclose\<close>\<close>

(** eclose(A) is the least transitive set including A as a subset. **)

lemma eclose_least_lemma:
    "\<lbrakk>Transset(X);  A<=X;  n \<in> nat\<rbrakk> \<Longrightarrow> nat_rec(n, A, %m r. \<Union>(r)) \<subseteq> X"
apply (unfold Transset_def)
apply (erule nat_induct)
apply (simp add: nat_rec_0)
apply (simp add: nat_rec_succ, blast)
done

lemma eclose_least:
     "\<lbrakk>Transset(X);  A<=X\<rbrakk> \<Longrightarrow> eclose(A) \<subseteq> X"
apply (unfold eclose_def)
apply (rule eclose_least_lemma [THEN UN_least], assumption+)
done

(*COMPLETELY DIFFERENT induction principle from eclose_induct\<And>*)
lemma eclose_induct_down [consumes 1]:
    "\<lbrakk>a \<in> eclose(b);
        \<And>y.   \<lbrakk>y \<in> b\<rbrakk> \<Longrightarrow> P(y);
        \<And>y z. \<lbrakk>y \<in> eclose(b);  P(y);  z \<in> y\<rbrakk> \<Longrightarrow> P(z)
\<rbrakk> \<Longrightarrow> P(a)"
apply (rule eclose_least [THEN subsetD, THEN CollectD2, of "eclose(b)"])
  prefer 3 apply assumption
 apply (unfold Transset_def)
 apply (blast intro: ecloseD)
apply (blast intro: arg_subset_eclose [THEN subsetD])
done

lemma Transset_eclose_eq_arg: "Transset(X) \<Longrightarrow> eclose(X) = X"
apply (erule equalityI [OF eclose_least arg_subset_eclose])
apply (rule subset_refl)
done

text\<open>A transitive set either is empty or contains the empty set.\<close>
lemma Transset_0_lemma [rule_format]: "Transset(A) \<Longrightarrow> x\<in>A \<longrightarrow> 0\<in>A"
apply (simp add: Transset_def)
apply (rule_tac a=x in eps_induct, clarify)
apply (drule bspec, assumption)
apply (case_tac "x=0", auto)
done

lemma Transset_0_disj: "Transset(A) \<Longrightarrow> A=0 | 0\<in>A"
by (blast dest: Transset_0_lemma)


subsection\<open>Epsilon Recursion\<close>

(*Unused...*)
lemma mem_eclose_trans: "\<lbrakk>A \<in> eclose(B);  B \<in> eclose(C)\<rbrakk> \<Longrightarrow> A \<in> eclose(C)"
by (rule eclose_least [OF Transset_eclose eclose_subset, THEN subsetD],
    assumption+)

(*Variant of the previous lemma in a useable form for the sequel*)
lemma mem_eclose_sing_trans:
     "\<lbrakk>A \<in> eclose({B});  B \<in> eclose({C})\<rbrakk> \<Longrightarrow> A \<in> eclose({C})"
by (rule eclose_least [OF Transset_eclose singleton_subsetI, THEN subsetD],
    assumption+)

lemma under_Memrel: "\<lbrakk>Transset(i);  j \<in> i\<rbrakk> \<Longrightarrow> Memrel(i)-``{j} = j"
by (unfold Transset_def, blast)

lemma lt_Memrel: "j < i \<Longrightarrow> Memrel(i) -`` {j} = j"
by (simp add: lt_def Ord_def under_Memrel)

(* @{term"j \<in> eclose(A) \<Longrightarrow> Memrel(eclose(A)) -`` j = j"} *)
lemmas under_Memrel_eclose = Transset_eclose [THEN under_Memrel]

lemmas wfrec_ssubst = wf_Memrel [THEN wfrec, THEN ssubst]

lemma wfrec_eclose_eq:
    "\<lbrakk>k \<in> eclose({j});  j \<in> eclose({i})\<rbrakk> \<Longrightarrow>
     wfrec(Memrel(eclose({i})), k, H) = wfrec(Memrel(eclose({j})), k, H)"
apply (erule eclose_induct)
apply (rule wfrec_ssubst)
apply (rule wfrec_ssubst)
apply (simp add: under_Memrel_eclose mem_eclose_sing_trans [of _ j i])
done

lemma wfrec_eclose_eq2:
    "k \<in> i \<Longrightarrow> wfrec(Memrel(eclose({i})),k,H) = wfrec(Memrel(eclose({k})),k,H)"
apply (rule arg_in_eclose_sing [THEN wfrec_eclose_eq])
apply (erule arg_into_eclose_sing)
done

lemma transrec: "transrec(a,H) = H(a, \<lambda>x\<in>a. transrec(x,H))"
apply (unfold transrec_def)
apply (rule wfrec_ssubst)
apply (simp add: wfrec_eclose_eq2 arg_in_eclose_sing under_Memrel_eclose)
done

(*Avoids explosions in proofs; resolve it with a meta-level definition.*)
lemma def_transrec:
    "\<lbrakk>\<And>x. f(x)\<equiv>transrec(x,H)\<rbrakk> \<Longrightarrow> f(a) = H(a, \<lambda>x\<in>a. f(x))"
apply simp
apply (rule transrec)
done

lemma transrec_type:
    "\<lbrakk>\<And>x u. \<lbrakk>x \<in> eclose({a});  u \<in> Pi(x,B)\<rbrakk> \<Longrightarrow> H(x,u) \<in> B(x)\<rbrakk>
     \<Longrightarrow> transrec(a,H) \<in> B(a)"
apply (rule_tac i = a in arg_in_eclose_sing [THEN eclose_induct])
apply (subst transrec)
apply (simp add: lam_type)
done

lemma eclose_sing_Ord: "Ord(i) \<Longrightarrow> eclose({i}) \<subseteq> succ(i)"
apply (erule Ord_is_Transset [THEN Transset_succ, THEN eclose_least])
apply (rule succI1 [THEN singleton_subsetI])
done

lemma succ_subset_eclose_sing: "succ(i) \<subseteq> eclose({i})"
apply (insert arg_subset_eclose [of "{i}"], simp)
apply (frule eclose_subset, blast)
done

lemma eclose_sing_Ord_eq: "Ord(i) \<Longrightarrow> eclose({i}) = succ(i)"
apply (rule equalityI)
apply (erule eclose_sing_Ord)
apply (rule succ_subset_eclose_sing)
done

lemma Ord_transrec_type:
  assumes jini: "j \<in> i"
      and ordi: "Ord(i)"
      and minor: " \<And>x u. \<lbrakk>x \<in> i;  u \<in> Pi(x,B)\<rbrakk> \<Longrightarrow> H(x,u) \<in> B(x)"
  shows "transrec(j,H) \<in> B(j)"
apply (rule transrec_type)
apply (insert jini ordi)
apply (blast intro!: minor
             intro: Ord_trans
             dest: Ord_in_Ord [THEN eclose_sing_Ord, THEN subsetD])
done

subsection\<open>Rank\<close>

(*NOT SUITABLE FOR REWRITING -- RECURSIVE!*)
lemma rank: "rank(a) = (\<Union>y\<in>a. succ(rank(y)))"
by (subst rank_def [THEN def_transrec], simp)

lemma Ord_rank [simp]: "Ord(rank(a))"
apply (rule_tac a=a in eps_induct)
apply (subst rank)
apply (rule Ord_succ [THEN Ord_UN])
apply (erule bspec, assumption)
done

lemma rank_of_Ord: "Ord(i) \<Longrightarrow> rank(i) = i"
apply (erule trans_induct)
apply (subst rank)
apply (simp add: Ord_equality)
done

lemma rank_lt: "a \<in> b \<Longrightarrow> rank(a) < rank(b)"
apply (rule_tac a1 = b in rank [THEN ssubst])
apply (erule UN_I [THEN ltI])
apply (rule_tac [2] Ord_UN, auto)
done

lemma eclose_rank_lt: "a \<in> eclose(b) \<Longrightarrow> rank(a) < rank(b)"
apply (erule eclose_induct_down)
apply (erule rank_lt)
apply (erule rank_lt [THEN lt_trans], assumption)
done

lemma rank_mono: "a<=b \<Longrightarrow> rank(a) \<le> rank(b)"
apply (rule subset_imp_le)
apply (auto simp add: rank [of a] rank [of b])
done

lemma rank_Pow: "rank(Pow(a)) = succ(rank(a))"
apply (rule rank [THEN trans])
apply (rule le_anti_sym)
apply (rule_tac [2] UN_upper_le)
apply (rule UN_least_le)
apply (auto intro: rank_mono simp add: Ord_UN)
done

lemma rank_0 [simp]: "rank(0) = 0"
by (rule rank [THEN trans], blast)

lemma rank_succ [simp]: "rank(succ(x)) = succ(rank(x))"
apply (rule rank [THEN trans])
apply (rule equalityI [OF UN_least succI1 [THEN UN_upper]])
apply (erule succE, blast)
apply (erule rank_lt [THEN leI, THEN succ_leI, THEN le_imp_subset])
done

lemma rank_Union: "rank(\<Union>(A)) = (\<Union>x\<in>A. rank(x))"
apply (rule equalityI)
apply (rule_tac [2] rank_mono [THEN le_imp_subset, THEN UN_least])
apply (erule_tac [2] Union_upper)
apply (subst rank)
apply (rule UN_least)
apply (erule UnionE)
apply (rule subset_trans)
apply (erule_tac [2] RepFunI [THEN Union_upper])
apply (erule rank_lt [THEN succ_leI, THEN le_imp_subset])
done

lemma rank_eclose: "rank(eclose(a)) = rank(a)"
apply (rule le_anti_sym)
apply (rule_tac [2] arg_subset_eclose [THEN rank_mono])
apply (rule_tac a1 = "eclose (a) " in rank [THEN ssubst])
apply (rule Ord_rank [THEN UN_least_le])
apply (erule eclose_rank_lt [THEN succ_leI])
done

lemma rank_pair1: "rank(a) < rank(<a,b>)"
apply (unfold Pair_def)
apply (rule consI1 [THEN rank_lt, THEN lt_trans])
apply (rule consI1 [THEN consI2, THEN rank_lt])
done

lemma rank_pair2: "rank(b) < rank(<a,b>)"
apply (unfold Pair_def)
apply (rule consI1 [THEN consI2, THEN rank_lt, THEN lt_trans])
apply (rule consI1 [THEN consI2, THEN rank_lt])
done

(*Not clear how to remove the P(a) condition, since the "then" part
  must refer to "a"*)
lemma the_equality_if:
     "P(a) \<Longrightarrow> (THE x. P(x)) = (if (\<exists>!x. P(x)) then a else 0)"
by (simp add: the_0 the_equality2)

(*The first premise not only fixs i but ensures @{term"f\<noteq>0"}.
  The second premise is now essential.  Consider otherwise the relation
  r = {<0,0>,<0,1>,<0,2>,...}.  Then f`0 = \<Union>(f``{0}) = \<Union>(nat) = nat,
  whose rank equals that of r.*)
lemma rank_apply: "\<lbrakk>i \<in> domain(f); function(f)\<rbrakk> \<Longrightarrow> rank(f`i) < rank(f)"
apply clarify
apply (simp add: function_apply_equality)
apply (blast intro: lt_trans rank_lt rank_pair2)
done


subsection\<open>Corollaries of Leastness\<close>

lemma mem_eclose_subset: "A \<in> B \<Longrightarrow> eclose(A)<=eclose(B)"
apply (rule Transset_eclose [THEN eclose_least])
apply (erule arg_into_eclose [THEN eclose_subset])
done

lemma eclose_mono: "A<=B \<Longrightarrow> eclose(A) \<subseteq> eclose(B)"
apply (rule Transset_eclose [THEN eclose_least])
apply (erule subset_trans)
apply (rule arg_subset_eclose)
done

(** Idempotence of eclose **)

lemma eclose_idem: "eclose(eclose(A)) = eclose(A)"
apply (rule equalityI)
apply (rule eclose_least [OF Transset_eclose subset_refl])
apply (rule arg_subset_eclose)
done

(** Transfinite recursion for definitions based on the
    three cases of ordinals **)

lemma transrec2_0 [simp]: "transrec2(0,a,b) = a"
by (rule transrec2_def [THEN def_transrec, THEN trans], simp)

lemma transrec2_succ [simp]: "transrec2(succ(i),a,b) = b(i, transrec2(i,a,b))"
apply (rule transrec2_def [THEN def_transrec, THEN trans])
apply (simp add: the_equality if_P)
done

lemma transrec2_Limit:
     "Limit(i) \<Longrightarrow> transrec2(i,a,b) = (\<Union>j<i. transrec2(j,a,b))"
apply (rule transrec2_def [THEN def_transrec, THEN trans])
apply (auto simp add: OUnion_def)
done

lemma def_transrec2:
     "(\<And>x. f(x)\<equiv>transrec2(x,a,b))
      \<Longrightarrow> f(0) = a &
          f(succ(i)) = b(i, f(i)) &
          (Limit(K) \<longrightarrow> f(K) = (\<Union>j<K. f(j)))"
by (simp add: transrec2_Limit)


(** recursor -- better than nat_rec; the succ case has no type requirement! **)

(*NOT suitable for rewriting*)
lemmas recursor_lemma = recursor_def [THEN def_transrec, THEN trans]

lemma recursor_0: "recursor(a,b,0) = a"
by (rule nat_case_0 [THEN recursor_lemma])

lemma recursor_succ: "recursor(a,b,succ(m)) = b(m, recursor(a,b,m))"
by (rule recursor_lemma, simp)


(** rec: old version for compatibility **)

lemma rec_0 [simp]: "rec(0,a,b) = a"
apply (unfold rec_def)
apply (rule recursor_0)
done

lemma rec_succ [simp]: "rec(succ(m),a,b) = b(m, rec(m,a,b))"
apply (unfold rec_def)
apply (rule recursor_succ)
done

lemma rec_type:
    "\<lbrakk>n \<in> nat;
        a \<in> C(0);
        \<And>m z. \<lbrakk>m \<in> nat;  z \<in> C(m)\<rbrakk> \<Longrightarrow> b(m,z): C(succ(m))\<rbrakk>
     \<Longrightarrow> rec(n,a,b) \<in> C(n)"
by (erule nat_induct, auto)

end
