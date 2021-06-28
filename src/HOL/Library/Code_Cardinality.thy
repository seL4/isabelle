subsection \<open>Code setup for sets with cardinality type information\<close>

theory Code_Cardinality imports Cardinality begin

text \<open>
  Implement \<^term>\<open>CARD('a)\<close> via \<^term>\<open>card_UNIV\<close> and provide
  implementations for \<^term>\<open>finite\<close>, \<^term>\<open>card\<close>, \<^term>\<open>(\<subseteq>)\<close>, 
  and \<^term>\<open>(=)\<close>if the calling context already provides \<^class>\<open>finite_UNIV\<close>
  and \<^class>\<open>card_UNIV\<close> instances. If we implemented the latter
  always via \<^term>\<open>card_UNIV\<close>, we would require instances of essentially all 
  element types, i.e., a lot of instantiation proofs and -- at run time --
  possibly slow dictionary constructions.
\<close>

context
begin

qualified definition card_UNIV' :: "'a card_UNIV"
where [code del]: "card_UNIV' = Phantom('a) CARD('a)"

lemma CARD_code [code_unfold]:
  "CARD('a) = of_phantom (card_UNIV' :: 'a card_UNIV)"
by(simp add: card_UNIV'_def)

lemma card_UNIV'_code [code]:
  "card_UNIV' = card_UNIV"
by(simp add: card_UNIV card_UNIV'_def)

end

lemma card_Compl:
  "finite A \<Longrightarrow> card (- A) = card (UNIV :: 'a set) - card (A :: 'a set)"
by (metis Compl_eq_Diff_UNIV card_Diff_subset top_greatest)

context fixes xs :: "'a :: finite_UNIV list"
begin

qualified definition finite' :: "'a set \<Rightarrow> bool"
where [simp, code del, code_abbrev]: "finite' = finite"

lemma finite'_code [code]:
  "finite' (set xs) \<longleftrightarrow> True"
  "finite' (List.coset xs) \<longleftrightarrow> of_phantom (finite_UNIV :: 'a finite_UNIV)"
by(simp_all add: card_gt_0_iff finite_UNIV)

end

context fixes xs :: "'a :: card_UNIV list"
begin

qualified definition card' :: "'a set \<Rightarrow> nat" 
where [simp, code del, code_abbrev]: "card' = card"
 
lemma card'_code [code]:
  "card' (set xs) = length (remdups xs)"
  "card' (List.coset xs) = of_phantom (card_UNIV :: 'a card_UNIV) - length (remdups xs)"
by(simp_all add: List.card_set card_Compl card_UNIV)


qualified definition subset' :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool"
where [simp, code del, code_abbrev]: "subset' = (\<subseteq>)"

lemma subset'_code [code]:
  "subset' A (List.coset ys) \<longleftrightarrow> (\<forall>y \<in> set ys. y \<notin> A)"
  "subset' (set ys) B \<longleftrightarrow> (\<forall>y \<in> set ys. y \<in> B)"
  "subset' (List.coset xs) (set ys) \<longleftrightarrow> (let n = CARD('a) in n > 0 \<and> card(set (xs @ ys)) = n)"
by(auto simp add: Let_def card_gt_0_iff dest: card_eq_UNIV_imp_eq_UNIV intro: arg_cong[where f=card])
  (metis finite_compl finite_set rev_finite_subset)

qualified definition eq_set :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool"
where [simp, code del, code_abbrev]: "eq_set = (=)"

lemma eq_set_code [code]:
  fixes ys
  defines "rhs \<equiv> 
  let n = CARD('a)
  in if n = 0 then False else 
        let xs' = remdups xs; ys' = remdups ys 
        in length xs' + length ys' = n \<and> (\<forall>x \<in> set xs'. x \<notin> set ys') \<and> (\<forall>y \<in> set ys'. y \<notin> set xs')"
  shows "eq_set (List.coset xs) (set ys) \<longleftrightarrow> rhs"
  and "eq_set (set ys) (List.coset xs) \<longleftrightarrow> rhs"
  and "eq_set (set xs) (set ys) \<longleftrightarrow> (\<forall>x \<in> set xs. x \<in> set ys) \<and> (\<forall>y \<in> set ys. y \<in> set xs)"
  and "eq_set (List.coset xs) (List.coset ys) \<longleftrightarrow> (\<forall>x \<in> set xs. x \<in> set ys) \<and> (\<forall>y \<in> set ys. y \<in> set xs)"
proof goal_cases
  {
    case 1
    show ?case (is "?lhs \<longleftrightarrow> ?rhs")
    proof
      show ?rhs if ?lhs
        using that
        by (auto simp add: rhs_def Let_def List.card_set[symmetric]
          card_Un_Int[where A="set xs" and B="- set xs"] card_UNIV
          Compl_partition card_gt_0_iff dest: sym)(metis finite_compl finite_set)
      show ?lhs if ?rhs
      proof - 
        have "\<lbrakk> \<forall>y\<in>set xs. y \<notin> set ys; \<forall>x\<in>set ys. x \<notin> set xs \<rbrakk> \<Longrightarrow> set xs \<inter> set ys = {}" by blast
        with that show ?thesis
          by (auto simp add: rhs_def Let_def List.card_set[symmetric]
            card_UNIV card_gt_0_iff card_Un_Int[where A="set xs" and B="set ys"]
            dest: card_eq_UNIV_imp_eq_UNIV split: if_split_asm)
      qed
    qed
  }
  moreover
  case 2
  ultimately show ?case unfolding eq_set_def by blast
next
  case 3
  show ?case unfolding eq_set_def List.coset_def by blast
next
  case 4
  show ?case unfolding eq_set_def List.coset_def by blast
qed

end

text \<open>
  Provide more informative exceptions than Match for non-rewritten cases.
  If generated code raises one these exceptions, then a code equation calls
  the mentioned operator for an element type that is not an instance of
  \<^class>\<open>card_UNIV\<close> and is therefore not implemented via \<^term>\<open>card_UNIV\<close>.
  Constrain the element type with sort \<^class>\<open>card_UNIV\<close> to change this.
\<close>

lemma card_coset_error [code]:
  "card (List.coset xs) = 
   Code.abort (STR ''card (List.coset _) requires type class instance card_UNIV'')
     (\<lambda>_. card (List.coset xs))"
by(simp)

lemma coset_subseteq_set_code [code]:
  "List.coset xs \<subseteq> set ys \<longleftrightarrow> 
  (if xs = [] \<and> ys = [] then False 
   else Code.abort
     (STR ''subset_eq (List.coset _) (List.set _) requires type class instance card_UNIV'')
     (\<lambda>_. List.coset xs \<subseteq> set ys))"
by simp

notepad begin \<comment> \<open>test code setup\<close>
have "List.coset [True] = set [False] \<and> 
      List.coset [] \<subseteq> List.set [True, False] \<and> 
      finite (List.coset [True])"
  by eval

end

end