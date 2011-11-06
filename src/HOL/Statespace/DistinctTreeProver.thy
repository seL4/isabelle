(*  Title:      HOL/Statespace/DistinctTreeProver.thy
    Author:     Norbert Schirmer, TU Muenchen
*)

header {* Distinctness of Names in a Binary Tree \label{sec:DistinctTreeProver}*}

theory DistinctTreeProver 
imports Main
uses ("distinct_tree_prover.ML")
begin

text {* A state space manages a set of (abstract) names and assumes
that the names are distinct. The names are stored as parameters of a
locale and distinctness as an assumption. The most common request is
to proof distinctness of two given names. We maintain the names in a
balanced binary tree and formulate a predicate that all nodes in the
tree have distinct names. This setup leads to logarithmic certificates.
*}

subsection {* The Binary Tree *}

datatype 'a tree = Node "'a tree" 'a bool "'a tree" | Tip


text {* The boolean flag in the node marks the content of the node as
deleted, without having to build a new tree. We prefer the boolean
flag to an option type, so that the ML-layer can still use the node
content to facilitate binary search in the tree. The ML code keeps the
nodes sorted using the term order. We do not have to push ordering to
the HOL level. *}

subsection {* Distinctness of Nodes *}


primrec set_of :: "'a tree \<Rightarrow> 'a set"
where
  "set_of Tip = {}"
| "set_of (Node l x d r) = (if d then {} else {x}) \<union> set_of l \<union> set_of r"

primrec all_distinct :: "'a tree \<Rightarrow> bool"
where
  "all_distinct Tip = True"
| "all_distinct (Node l x d r) =
    ((d \<or> (x \<notin> set_of l \<and> x \<notin> set_of r)) \<and> 
      set_of l \<inter> set_of r = {} \<and>
      all_distinct l \<and> all_distinct r)"

text {* Given a binary tree @{term "t"} for which 
@{const all_distinct} holds, given two different nodes contained in the tree,
we want to write a ML function that generates a logarithmic
certificate that the content of the nodes is distinct. We use the
following lemmas to achieve this.  *} 

lemma all_distinct_left: "all_distinct (Node l x b r) \<Longrightarrow> all_distinct l"
  by simp

lemma all_distinct_right: "all_distinct (Node l x b r) \<Longrightarrow> all_distinct r"
  by simp

lemma distinct_left: "all_distinct (Node l x False r) \<Longrightarrow> y \<in> set_of l \<Longrightarrow> x \<noteq> y"
  by auto

lemma distinct_right: "all_distinct (Node l x False r) \<Longrightarrow> y \<in> set_of r \<Longrightarrow> x \<noteq> y"
  by auto

lemma distinct_left_right:
    "all_distinct (Node l z b r) \<Longrightarrow> x \<in> set_of l \<Longrightarrow> y \<in> set_of r \<Longrightarrow> x \<noteq> y"
  by auto

lemma in_set_root: "x \<in> set_of (Node l x False r)"
  by simp

lemma in_set_left: "y \<in> set_of l \<Longrightarrow>  y \<in> set_of (Node l x False r)"
  by simp

lemma in_set_right: "y \<in> set_of r \<Longrightarrow>  y \<in> set_of (Node l x False r)"
  by simp

lemma swap_neq: "x \<noteq> y \<Longrightarrow> y \<noteq> x"
  by blast

lemma neq_to_eq_False: "x\<noteq>y \<Longrightarrow> (x=y)\<equiv>False"
  by simp

subsection {* Containment of Trees *}

text {* When deriving a state space from other ones, we create a new
name tree which contains all the names of the parent state spaces and
assume the predicate @{const all_distinct}. We then prove that the new
locale interprets all parent locales. Hence we have to show that the
new distinctness assumption on all names implies the distinctness
assumptions of the parent locales. This proof is implemented in ML. We
do this efficiently by defining a kind of containment check of trees
by ``subtraction''.  We subtract the parent tree from the new tree. If
this succeeds we know that @{const all_distinct} of the new tree
implies @{const all_distinct} of the parent tree.  The resulting
certificate is of the order @{term "n * log(m)"} where @{term "n"} is
the size of the (smaller) parent tree and @{term "m"} the size of the
(bigger) new tree.  *}


primrec delete :: "'a \<Rightarrow> 'a tree \<Rightarrow> 'a tree option"
where
  "delete x Tip = None"
| "delete x (Node l y d r) = (case delete x l of
                                Some l' \<Rightarrow>
                                 (case delete x r of 
                                    Some r' \<Rightarrow> Some (Node l' y (d \<or> (x=y)) r')
                                  | None \<Rightarrow> Some (Node l' y (d \<or> (x=y)) r))
                               | None \<Rightarrow>
                                  (case delete x r of 
                                     Some r' \<Rightarrow> Some (Node l y (d \<or> (x=y)) r')
                                   | None \<Rightarrow> if x=y \<and> \<not>d then Some (Node l y True r)
                                             else None))"


lemma delete_Some_set_of: "delete x t = Some t' \<Longrightarrow> set_of t' \<subseteq> set_of t"
proof (induct t arbitrary: t')
  case Tip thus ?case by simp
next
  case (Node l y d r)
  have del: "delete x (Node l y d r) = Some t'" by fact
  show ?case
  proof (cases "delete x l")
    case (Some l')
    note x_l_Some = this
    with Node.hyps
    have l'_l: "set_of l' \<subseteq> set_of l"
      by simp
    show ?thesis
    proof (cases "delete x r")
      case (Some r')
      with Node.hyps
      have "set_of r' \<subseteq> set_of r"
        by simp
      with l'_l Some x_l_Some del
      show ?thesis
        by (auto split: split_if_asm)
    next
      case None
      with l'_l Some x_l_Some del
      show ?thesis
        by (fastforce split: split_if_asm)
    qed
  next
    case None
    note x_l_None = this
    show ?thesis
    proof (cases "delete x r")
      case (Some r')
      with Node.hyps
      have "set_of r' \<subseteq> set_of r"
        by simp
      with Some x_l_None del
      show ?thesis
        by (fastforce split: split_if_asm)
    next
      case None
      with x_l_None del
      show ?thesis
        by (fastforce split: split_if_asm)
    qed
  qed
qed

lemma delete_Some_all_distinct:
  "delete x t = Some t' \<Longrightarrow> all_distinct t \<Longrightarrow> all_distinct t'"
proof (induct t arbitrary: t')
  case Tip thus ?case by simp
next
  case (Node l y d r)
  have del: "delete x (Node l y d r) = Some t'" by fact
  have "all_distinct (Node l y d r)" by fact
  then obtain
    dist_l: "all_distinct l" and
    dist_r: "all_distinct r" and
    d: "d \<or> (y \<notin> set_of l \<and> y \<notin> set_of r)" and
    dist_l_r: "set_of l \<inter> set_of r = {}"
    by auto
  show ?case
  proof (cases "delete x l")
    case (Some l')
    note x_l_Some = this
    from Node.hyps (1) [OF Some dist_l]
    have dist_l': "all_distinct l'"
      by simp
    from delete_Some_set_of [OF x_l_Some]
    have l'_l: "set_of l' \<subseteq> set_of l".
    show ?thesis
    proof (cases "delete x r")
      case (Some r')
      from Node.hyps (2) [OF Some dist_r]
      have dist_r': "all_distinct r'"
        by simp
      from delete_Some_set_of [OF Some]
      have "set_of r' \<subseteq> set_of r".
      
      with dist_l' dist_r' l'_l Some x_l_Some del d dist_l_r
      show ?thesis
        by fastforce
    next
      case None
      with l'_l dist_l'  x_l_Some del d dist_l_r dist_r
      show ?thesis
        by fastforce
    qed
  next
    case None
    note x_l_None = this
    show ?thesis
    proof (cases "delete x r")
      case (Some r')
      with Node.hyps (2) [OF Some dist_r]
      have dist_r': "all_distinct r'"
        by simp
      from delete_Some_set_of [OF Some]
      have "set_of r' \<subseteq> set_of r".
      with Some dist_r' x_l_None del dist_l d dist_l_r
      show ?thesis
        by fastforce
    next
      case None
      with x_l_None del dist_l dist_r d dist_l_r
      show ?thesis
        by (fastforce split: split_if_asm)
    qed
  qed
qed

lemma delete_None_set_of_conv: "delete x t = None = (x \<notin> set_of t)"
proof (induct t)
  case Tip thus ?case by simp
next
  case (Node l y d r)
  thus ?case
    by (auto split: option.splits)
qed

lemma delete_Some_x_set_of:
  "delete x t = Some t' \<Longrightarrow> x \<in> set_of t \<and> x \<notin> set_of t'"
proof (induct t arbitrary: t')
  case Tip thus ?case by simp
next
  case (Node l y d r)
  have del: "delete x (Node l y d r) = Some t'" by fact
  show ?case
  proof (cases "delete x l")
    case (Some l')
    note x_l_Some = this
    from Node.hyps (1) [OF Some]
    obtain x_l: "x \<in> set_of l" "x \<notin> set_of l'"
      by simp
    show ?thesis
    proof (cases "delete x r")
      case (Some r')
      from Node.hyps (2) [OF Some]
      obtain x_r: "x \<in> set_of r" "x \<notin> set_of r'"
        by simp
      from x_r x_l Some x_l_Some del 
      show ?thesis
        by (clarsimp split: split_if_asm)
    next
      case None
      then have "x \<notin> set_of r"
        by (simp add: delete_None_set_of_conv)
      with x_l None x_l_Some del
      show ?thesis
        by (clarsimp split: split_if_asm)
    qed
  next
    case None
    note x_l_None = this
    then have x_notin_l: "x \<notin> set_of l"
      by (simp add: delete_None_set_of_conv)
    show ?thesis
    proof (cases "delete x r")
      case (Some r')
      from Node.hyps (2) [OF Some]
      obtain x_r: "x \<in> set_of r" "x \<notin> set_of r'"
        by simp
      from x_r x_notin_l Some x_l_None del 
      show ?thesis
        by (clarsimp split: split_if_asm)
    next
      case None
      then have "x \<notin> set_of r"
        by (simp add: delete_None_set_of_conv)
      with None x_l_None x_notin_l del
      show ?thesis
        by (clarsimp split: split_if_asm)
    qed
  qed
qed


primrec subtract :: "'a tree \<Rightarrow> 'a tree \<Rightarrow> 'a tree option"
where
  "subtract Tip t = Some t"
| "subtract (Node l x b r) t =
     (case delete x t of
        Some t' \<Rightarrow> (case subtract l t' of 
                     Some t'' \<Rightarrow> subtract r t''
                    | None \<Rightarrow> None)
       | None \<Rightarrow> None)"

lemma subtract_Some_set_of_res: 
  "subtract t\<^isub>1 t\<^isub>2 = Some t \<Longrightarrow> set_of t \<subseteq> set_of t\<^isub>2"
proof (induct t\<^isub>1 arbitrary: t\<^isub>2 t)
  case Tip thus ?case by simp
next
  case (Node l x b r)
  have sub: "subtract (Node l x b r) t\<^isub>2 = Some t" by fact
  show ?case
  proof (cases "delete x t\<^isub>2")
    case (Some t\<^isub>2')
    note del_x_Some = this
    from delete_Some_set_of [OF Some] 
    have t2'_t2: "set_of t\<^isub>2' \<subseteq> set_of t\<^isub>2" .
    show ?thesis
    proof (cases "subtract l t\<^isub>2'")
      case (Some t\<^isub>2'')
      note sub_l_Some = this
      from Node.hyps (1) [OF Some] 
      have t2''_t2': "set_of t\<^isub>2'' \<subseteq> set_of t\<^isub>2'" .
      show ?thesis
      proof (cases "subtract r t\<^isub>2''")
        case (Some t\<^isub>2''')
        from Node.hyps (2) [OF Some ] 
        have "set_of t\<^isub>2''' \<subseteq> set_of t\<^isub>2''" .
        with Some sub_l_Some del_x_Some sub t2''_t2' t2'_t2
        show ?thesis
          by simp
      next
        case None
        with del_x_Some sub_l_Some sub
        show ?thesis
          by simp
      qed
    next
      case None
      with del_x_Some sub 
      show ?thesis
        by simp
    qed
  next
    case None
    with sub show ?thesis by simp
  qed
qed

lemma subtract_Some_set_of: 
  "subtract t\<^isub>1 t\<^isub>2 = Some t \<Longrightarrow> set_of t\<^isub>1 \<subseteq> set_of t\<^isub>2"
proof (induct t\<^isub>1 arbitrary: t\<^isub>2 t)
  case Tip thus ?case by simp
next
  case (Node l x d r)
  have sub: "subtract (Node l x d r) t\<^isub>2 = Some t" by fact
  show ?case
  proof (cases "delete x t\<^isub>2")
    case (Some t\<^isub>2')
    note del_x_Some = this
    from delete_Some_set_of [OF Some] 
    have t2'_t2: "set_of t\<^isub>2' \<subseteq> set_of t\<^isub>2" .
    from delete_None_set_of_conv [of x t\<^isub>2] Some
    have x_t2: "x \<in> set_of t\<^isub>2"
      by simp
    show ?thesis
    proof (cases "subtract l t\<^isub>2'")
      case (Some t\<^isub>2'')
      note sub_l_Some = this
      from Node.hyps (1) [OF Some] 
      have l_t2': "set_of l \<subseteq> set_of t\<^isub>2'" .
      from subtract_Some_set_of_res [OF Some]
      have t2''_t2': "set_of t\<^isub>2'' \<subseteq> set_of t\<^isub>2'" .
      show ?thesis
      proof (cases "subtract r t\<^isub>2''")
        case (Some t\<^isub>2''')
        from Node.hyps (2) [OF Some ] 
        have r_t\<^isub>2'': "set_of r \<subseteq> set_of t\<^isub>2''" .
        from Some sub_l_Some del_x_Some sub r_t\<^isub>2'' l_t2' t2'_t2 t2''_t2' x_t2
        show ?thesis
          by auto
      next
        case None
        with del_x_Some sub_l_Some sub
        show ?thesis
          by simp
      qed
    next
      case None
      with del_x_Some sub 
      show ?thesis
        by simp
    qed
  next
    case None
    with sub show ?thesis by simp
  qed
qed

lemma subtract_Some_all_distinct_res: 
  "subtract t\<^isub>1 t\<^isub>2 = Some t \<Longrightarrow> all_distinct t\<^isub>2 \<Longrightarrow> all_distinct t"
proof (induct t\<^isub>1 arbitrary: t\<^isub>2 t)
  case Tip thus ?case by simp
next
  case (Node l x d r)
  have sub: "subtract (Node l x d r) t\<^isub>2 = Some t" by fact
  have dist_t2: "all_distinct t\<^isub>2" by fact
  show ?case
  proof (cases "delete x t\<^isub>2")
    case (Some t\<^isub>2')
    note del_x_Some = this
    from delete_Some_all_distinct [OF Some dist_t2] 
    have dist_t2': "all_distinct t\<^isub>2'" .
    show ?thesis
    proof (cases "subtract l t\<^isub>2'")
      case (Some t\<^isub>2'')
      note sub_l_Some = this
      from Node.hyps (1) [OF Some dist_t2'] 
      have dist_t2'': "all_distinct t\<^isub>2''" .
      show ?thesis
      proof (cases "subtract r t\<^isub>2''")
        case (Some t\<^isub>2''')
        from Node.hyps (2) [OF Some dist_t2''] 
        have dist_t2''': "all_distinct t\<^isub>2'''" .
        from Some sub_l_Some del_x_Some sub 
             dist_t2'''
        show ?thesis
          by simp
      next
        case None
        with del_x_Some sub_l_Some sub
        show ?thesis
          by simp
      qed
    next
      case None
      with del_x_Some sub 
      show ?thesis
        by simp
    qed
  next
    case None
    with sub show ?thesis by simp
  qed
qed


lemma subtract_Some_dist_res: 
  "subtract t\<^isub>1 t\<^isub>2 = Some t \<Longrightarrow> set_of t\<^isub>1 \<inter> set_of t = {}"
proof (induct t\<^isub>1 arbitrary: t\<^isub>2 t)
  case Tip thus ?case by simp
next
  case (Node l x d r)
  have sub: "subtract (Node l x d r) t\<^isub>2 = Some t" by fact
  show ?case
  proof (cases "delete x t\<^isub>2")
    case (Some t\<^isub>2')
    note del_x_Some = this
    from delete_Some_x_set_of [OF Some]
    obtain x_t2: "x \<in> set_of t\<^isub>2" and x_not_t2': "x \<notin> set_of t\<^isub>2'"
      by simp
    from delete_Some_set_of [OF Some]
    have t2'_t2: "set_of t\<^isub>2' \<subseteq> set_of t\<^isub>2" .
    show ?thesis
    proof (cases "subtract l t\<^isub>2'")
      case (Some t\<^isub>2'')
      note sub_l_Some = this
      from Node.hyps (1) [OF Some ] 
      have dist_l_t2'': "set_of l \<inter> set_of t\<^isub>2'' = {}".
      from subtract_Some_set_of_res [OF Some]
      have t2''_t2': "set_of t\<^isub>2'' \<subseteq> set_of t\<^isub>2'" .
      show ?thesis
      proof (cases "subtract r t\<^isub>2''")
        case (Some t\<^isub>2''')
        from Node.hyps (2) [OF Some] 
        have dist_r_t2''': "set_of r \<inter> set_of t\<^isub>2''' = {}" .
        from subtract_Some_set_of_res [OF Some]
        have t2'''_t2'': "set_of t\<^isub>2''' \<subseteq> set_of t\<^isub>2''".
        
        from Some sub_l_Some del_x_Some sub t2'''_t2'' dist_l_t2'' dist_r_t2'''
             t2''_t2' t2'_t2 x_not_t2'
        show ?thesis
          by auto
      next
        case None
        with del_x_Some sub_l_Some sub
        show ?thesis
          by simp
      qed
    next
      case None
      with del_x_Some sub 
      show ?thesis
        by simp
    qed
  next
    case None
    with sub show ?thesis by simp
  qed
qed
        
lemma subtract_Some_all_distinct:
  "subtract t\<^isub>1 t\<^isub>2 = Some t \<Longrightarrow> all_distinct t\<^isub>2 \<Longrightarrow> all_distinct t\<^isub>1"
proof (induct t\<^isub>1 arbitrary: t\<^isub>2 t)
  case Tip thus ?case by simp
next
  case (Node l x d r)
  have sub: "subtract (Node l x d r) t\<^isub>2 = Some t" by fact
  have dist_t2: "all_distinct t\<^isub>2" by fact
  show ?case
  proof (cases "delete x t\<^isub>2")
    case (Some t\<^isub>2')
    note del_x_Some = this
    from delete_Some_all_distinct [OF Some dist_t2 ] 
    have dist_t2': "all_distinct t\<^isub>2'" .
    from delete_Some_set_of [OF Some]
    have t2'_t2: "set_of t\<^isub>2' \<subseteq> set_of t\<^isub>2" .
    from delete_Some_x_set_of [OF Some]
    obtain x_t2: "x \<in> set_of t\<^isub>2" and x_not_t2': "x \<notin> set_of t\<^isub>2'"
      by simp

    show ?thesis
    proof (cases "subtract l t\<^isub>2'")
      case (Some t\<^isub>2'')
      note sub_l_Some = this
      from Node.hyps (1) [OF Some dist_t2' ] 
      have dist_l: "all_distinct l" .
      from subtract_Some_all_distinct_res [OF Some dist_t2'] 
      have dist_t2'': "all_distinct t\<^isub>2''" .
      from subtract_Some_set_of [OF Some]
      have l_t2': "set_of l \<subseteq> set_of t\<^isub>2'" .
      from subtract_Some_set_of_res [OF Some]
      have t2''_t2': "set_of t\<^isub>2'' \<subseteq> set_of t\<^isub>2'" .
      from subtract_Some_dist_res [OF Some]
      have dist_l_t2'': "set_of l \<inter> set_of t\<^isub>2'' = {}".
      show ?thesis
      proof (cases "subtract r t\<^isub>2''")
        case (Some t\<^isub>2''')
        from Node.hyps (2) [OF Some dist_t2''] 
        have dist_r: "all_distinct r" .
        from subtract_Some_set_of [OF Some]
        have r_t2'': "set_of r \<subseteq> set_of t\<^isub>2''" .
        from subtract_Some_dist_res [OF Some]
        have dist_r_t2''': "set_of r \<inter> set_of t\<^isub>2''' = {}".

        from dist_l dist_r Some sub_l_Some del_x_Some r_t2'' l_t2' x_t2 x_not_t2' 
             t2''_t2' dist_l_t2'' dist_r_t2'''
        show ?thesis
          by auto
      next
        case None
        with del_x_Some sub_l_Some sub
        show ?thesis
          by simp
      qed
    next
      case None
      with del_x_Some sub 
      show ?thesis
        by simp
    qed
  next
    case None
    with sub show ?thesis by simp
  qed
qed


lemma delete_left:
  assumes dist: "all_distinct (Node l y d r)" 
  assumes del_l: "delete x l = Some l'"
  shows "delete x (Node l y d r) = Some (Node l' y d r)"
proof -
  from delete_Some_x_set_of [OF del_l]
  obtain "x \<in> set_of l"
    by simp
  moreover with dist 
  have "delete x r = None"
    by (cases "delete x r") (auto dest:delete_Some_x_set_of)

  ultimately 
  show ?thesis
    using del_l dist
    by (auto split: option.splits)
qed

lemma delete_right:
  assumes dist: "all_distinct (Node l y d r)" 
  assumes del_r: "delete x r = Some r'"
  shows "delete x (Node l y d r) = Some (Node l y d r')"
proof -
  from delete_Some_x_set_of [OF del_r]
  obtain "x \<in> set_of r"
    by simp
  moreover with dist 
  have "delete x l = None"
    by (cases "delete x l") (auto dest:delete_Some_x_set_of)

  ultimately 
  show ?thesis
    using del_r dist
    by (auto split: option.splits)
qed

lemma delete_root: 
  assumes dist: "all_distinct (Node l x False r)" 
  shows "delete x (Node l x False r) = Some (Node l x True r)"
proof -
  from dist have "delete x r = None"
    by (cases "delete x r") (auto dest:delete_Some_x_set_of)
  moreover
  from dist have "delete x l = None"
    by (cases "delete x l") (auto dest:delete_Some_x_set_of)
  ultimately show ?thesis
    using dist
       by (auto split: option.splits)
qed               

lemma subtract_Node:
 assumes del: "delete x t = Some t'"                                
 assumes sub_l: "subtract l t' = Some t''"
 assumes sub_r: "subtract r t'' = Some t'''"
 shows "subtract (Node l x False r) t = Some t'''"
using del sub_l sub_r
by simp

lemma subtract_Tip: "subtract Tip t = Some t"
  by simp
 
text {* Now we have all the theorems in place that are needed for the
certificate generating ML functions. *}

use "distinct_tree_prover.ML"

(* Uncomment for profiling or debugging *)
(*
ML {*
(*
val nums = (0 upto 10000);
val nums' = (200 upto 3000);
*)
val nums = (0 upto 10000);
val nums' = (0 upto 3000);
val const_decls = map (fn i => ("const" ^ string_of_int i, Type ("nat", []), NoSyn)) nums

val consts = sort Term_Ord.fast_term_ord 
              (map (fn i => Const ("DistinctTreeProver.const"^string_of_int i,Type ("nat",[]))) nums)
val consts' = sort Term_Ord.fast_term_ord 
              (map (fn i => Const ("DistinctTreeProver.const"^string_of_int i,Type ("nat",[]))) nums')

val t = DistinctTreeProver.mk_tree I (Type ("nat",[])) consts


val t' = DistinctTreeProver.mk_tree I (Type ("nat",[])) consts'


val dist = 
     HOLogic.Trueprop$
       (Const ("DistinctTreeProver.all_distinct",DistinctTreeProver.treeT (Type ("nat",[])) --> HOLogic.boolT)$t)

val dist' = 
     HOLogic.Trueprop$
       (Const ("DistinctTreeProver.all_distinct",DistinctTreeProver.treeT (Type ("nat",[])) --> HOLogic.boolT)$t')

val da = Unsynchronized.ref refl;

*}

setup {*
Theory.add_consts_i const_decls
#> (fn thy  => let val ([thm],thy') = Global_Theory.add_axioms [(("dist_axiom",dist),[])] thy
               in (da := thm; thy') end)
*}


ML {* 
 val ct' = cterm_of @{theory} t';
*}

ML {*
 timeit (fn () => (DistinctTreeProver.subtractProver (term_of ct') ct' (!da);())) 
*}

(* 590 s *)

ML {*


val p1 = 
 the (DistinctTreeProver.find_tree (Const ("DistinctTreeProver.const1",Type ("nat",[]))) t)
val p2 =
 the (DistinctTreeProver.find_tree (Const ("DistinctTreeProver.const10000",Type ("nat",[]))) t)
*}


ML {* timeit (fn () => DistinctTreeProver.distinctTreeProver (!da )
       p1
       p2)*}


ML {* timeit (fn () => (DistinctTreeProver.deleteProver (!da) p1;())) *}




ML {*
val cdist' = cterm_of @{theory} dist';
DistinctTreeProver.distinct_implProver (!da) cdist';
*}

*)

end
