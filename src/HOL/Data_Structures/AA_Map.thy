(* Author: Tobias Nipkow *)

section "AA Tree Implementation of Maps"

theory AA_Map
imports
  AA_Set
  Lookup2
begin

fun update :: "'a::linorder \<Rightarrow> 'b \<Rightarrow> ('a*'b) aa_tree \<Rightarrow> ('a*'b) aa_tree" where
"update x y Leaf = Node 1 Leaf (x,y) Leaf" |
"update x y (Node lv t1 (a,b) t2) =
  (case cmp x a of
     LT \<Rightarrow> split (skew (Node lv (update x y t1) (a,b) t2)) |
     GT \<Rightarrow> split (skew (Node lv t1 (a,b) (update x y t2))) |
     EQ \<Rightarrow> Node lv t1 (x,y) t2)"

fun delete :: "'a::linorder \<Rightarrow> ('a*'b) aa_tree \<Rightarrow> ('a*'b) aa_tree" where
"delete _ Leaf = Leaf" |
"delete x (Node lv l (a,b) r) =
  (case cmp x a of
     LT \<Rightarrow> adjust (Node lv (delete x l) (a,b) r) |
     GT \<Rightarrow> adjust (Node lv l (a,b) (delete x r)) |
     EQ \<Rightarrow> (if l = Leaf then r
            else let (l',ab') = del_max l in adjust (Node lv l' ab' r)))"


subsection "Invariance"

subsubsection "Proofs for insert"

lemma lvl_update_aux:
  "lvl (update x y t) = lvl t \<or> lvl (update x y t) = lvl t + 1 \<and> sngl (update x y t)"
apply(induction t)
apply (auto simp: lvl_skew)
apply (metis Suc_eq_plus1 lvl.simps(2) lvl_split lvl_skew)+
done

lemma lvl_update: obtains
  (Same) "lvl (update x y t) = lvl t" |
  (Incr) "lvl (update x y t) = lvl t + 1" "sngl (update x y t)"
using lvl_update_aux by fastforce

declare invar.simps(2)[simp]

lemma lvl_update_sngl: "invar t \<Longrightarrow> sngl t \<Longrightarrow> lvl(update x y t) = lvl t"
proof (induction t rule: update.induct)
  case (2 x y lv t1 a b t2)
  consider (LT) "x < a" | (GT) "x > a" | (EQ) "x = a" 
    using less_linear by blast 
  thus ?case proof cases
    case LT
    thus ?thesis using 2 by (auto simp add: skew_case split_case split: tree.splits)
  next
    case GT
    thus ?thesis using 2 proof (cases t1)
      case Node
      thus ?thesis using 2 GT  
        apply (auto simp add: skew_case split_case split: tree.splits)
        by (metis less_not_refl2 lvl.simps(2) lvl_update_aux n_not_Suc_n sngl.simps(3))+ 
    qed (auto simp add: lvl_0_iff)
  qed simp
qed simp

lemma lvl_update_incr_iff: "(lvl(update a b t) = lvl t + 1) \<longleftrightarrow>
  (EX l x r. update a b t = Node (lvl t + 1) l x r \<and> lvl l = lvl r)"
apply(cases t)
apply(auto simp add: skew_case split_case split: if_splits)
apply(auto split: tree.splits if_splits)
done

lemma invar_update: "invar t \<Longrightarrow> invar(update a b t)"
proof(induction t)
  case N: (Node n l xy r)
  hence il: "invar l" and ir: "invar r" by auto
  note iil = N.IH(1)[OF il]
  note iir = N.IH(2)[OF ir]
  obtain x y where [simp]: "xy = (x,y)" by fastforce
  let ?t = "Node n l xy r"
  have "a < x \<or> a = x \<or> x < a" by auto
  moreover
  have ?case if "a < x"
  proof (cases rule: lvl_update[of a b l])
    case (Same) thus ?thesis
      using \<open>a<x\<close> invar_NodeL[OF N.prems iil Same]
      by (simp add: skew_invar split_invar del: invar.simps)
  next
    case (Incr)
    then obtain t1 w t2 where ial[simp]: "update a b l = Node n t1 w t2"
      using N.prems by (auto simp: lvl_Suc_iff)
    have l12: "lvl t1 = lvl t2"
      by (metis Incr(1) ial lvl_update_incr_iff tree.inject)
    have "update a b ?t = split(skew(Node n (update a b l) xy r))"
      by(simp add: \<open>a<x\<close>)
    also have "skew(Node n (update a b l) xy r) = Node n t1 w (Node n t2 xy r)"
      by(simp)
    also have "invar(split \<dots>)"
    proof (cases r)
      case Leaf
      hence "l = Leaf" using N.prems by(auto simp: lvl_0_iff)
      thus ?thesis using Leaf ial by simp
    next
      case [simp]: (Node m t3 y t4)
      show ?thesis (*using N(3) iil l12 by(auto)*)
      proof cases
        assume "m = n" thus ?thesis using N(3) iil by(auto)
      next
        assume "m \<noteq> n" thus ?thesis using N(3) iil l12 by(auto)
      qed
    qed
    finally show ?thesis .
  qed
  moreover
  have ?case if "x < a"
  proof -
    from \<open>invar ?t\<close> have "n = lvl r \<or> n = lvl r + 1" by auto
    thus ?case
    proof
      assume 0: "n = lvl r"
      have "update a b ?t = split(skew(Node n l xy (update a b r)))"
        using \<open>a>x\<close> by(auto)
      also have "skew(Node n l xy (update a b r)) = Node n l xy (update a b r)"
        using N.prems by(simp add: skew_case split: tree.split)
      also have "invar(split \<dots>)"
      proof -
        from lvl_update_sngl[OF ir sngl_if_invar[OF \<open>invar ?t\<close> 0], of a b]
        obtain t1 p t2 where iar: "update a b r = Node n t1 p t2"
          using N.prems 0 by (auto simp: lvl_Suc_iff)
        from N.prems iar 0 iir
        show ?thesis by (auto simp: split_case split: tree.splits)
      qed
      finally show ?thesis .
    next
      assume 1: "n = lvl r + 1"
      hence "sngl ?t" by(cases r) auto
      show ?thesis
      proof (cases rule: lvl_update[of a b r])
        case (Same)
        show ?thesis using \<open>x<a\<close> il ir invar_NodeR[OF N.prems 1 iir Same]
          by (auto simp add: skew_invar split_invar)
      next
        case (Incr)
        thus ?thesis using invar_NodeR2[OF \<open>invar ?t\<close> Incr(2) 1 iir] 1 \<open>x < a\<close>
          by (auto simp add: skew_invar split_invar split: if_splits)
      qed
    qed
  qed
  moreover
  have "a = x \<Longrightarrow> ?case" using N.prems by auto
  ultimately show ?case by blast
qed simp

subsubsection "Proofs for delete"

declare invar.simps(2)[simp del]

theorem post_delete: "invar t \<Longrightarrow> post_del t (delete x t)"
proof (induction t)
  case (Node lv l ab r)

  obtain a b where [simp]: "ab = (a,b)" by fastforce

  let ?l' = "delete x l" and ?r' = "delete x r"
  let ?t = "Node lv l ab r" let ?t' = "delete x ?t"

  from Node.prems have inv_l: "invar l" and inv_r: "invar r" by (auto)

  note post_l' = Node.IH(1)[OF inv_l]
  note preL = pre_adj_if_postL[OF Node.prems post_l']

  note post_r' = Node.IH(2)[OF inv_r]
  note preR = pre_adj_if_postR[OF Node.prems post_r']

  show ?case
  proof (cases rule: linorder_cases[of x a])
    case less
    thus ?thesis using Node.prems by (simp add: post_del_adjL preL)
  next
    case greater
    thus ?thesis using Node.prems preR by (simp add: post_del_adjR post_r')
  next
    case equal
    show ?thesis
    proof cases
      assume "l = Leaf" thus ?thesis using equal Node.prems
        by(auto simp: post_del_def invar.simps(2))
    next
      assume "l \<noteq> Leaf" thus ?thesis using equal Node.prems
        by simp (metis inv_l post_del_adjL post_del_max pre_adj_if_postL)
    qed
  qed
qed (simp add: post_del_def)


subsection \<open>Functional Correctness Proofs\<close>

theorem inorder_update:
  "sorted1(inorder t) \<Longrightarrow> inorder(update x y t) = upd_list x y (inorder t)"
by (induct t) (auto simp: upd_list_simps inorder_split inorder_skew)

theorem inorder_delete:
  "\<lbrakk>invar t; sorted1(inorder t)\<rbrakk> \<Longrightarrow>
  inorder (delete x t) = del_list x (inorder t)"
by(induction t)
  (auto simp: del_list_simps inorder_adjust pre_adj_if_postL pre_adj_if_postR 
              post_del_max post_delete del_maxD split: prod.splits)

interpretation I: Map_by_Ordered
where empty = Leaf and lookup = lookup and update = update and delete = delete
and inorder = inorder and inv = invar
proof (standard, goal_cases)
  case 1 show ?case by simp
next
  case 2 thus ?case by(simp add: lookup_map_of)
next
  case 3 thus ?case by(simp add: inorder_update)
next
  case 4 thus ?case by(simp add: inorder_delete)
next
  case 5 thus ?case by(simp)
next
  case 6 thus ?case by(simp add: invar_update)
next
  case 7 thus ?case using post_delete by(auto simp: post_del_def)
qed

end
