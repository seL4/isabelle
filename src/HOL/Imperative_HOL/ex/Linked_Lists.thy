theory Linked_Lists
imports "~~/src/HOL/Imperative_HOL/Imperative_HOL" Code_Integer
begin

section {* Definition of Linked Lists *}

setup {* Sign.add_const_constraint (@{const_name Ref}, SOME @{typ "nat \<Rightarrow> 'a\<Colon>type ref"}) *}
datatype 'a node = Empty | Node 'a "('a node) ref"

fun
  node_encode :: "'a\<Colon>countable node \<Rightarrow> nat"
where
  "node_encode Empty = 0"
  | "node_encode (Node x r) = Suc (to_nat (x, r))"

instance node :: (countable) countable
proof (rule countable_classI [of "node_encode"])
  fix x y :: "'a\<Colon>countable node"
  show "node_encode x = node_encode y \<Longrightarrow> x = y"
  by (induct x, auto, induct y, auto, induct y, auto)
qed

instance node :: (heap) heap ..

fun make_llist :: "'a\<Colon>heap list \<Rightarrow> 'a node Heap"
where 
  [simp del]: "make_llist []     = return Empty"
            | "make_llist (x#xs) = do tl   \<leftarrow> make_llist xs;
                                      next \<leftarrow> Ref.new tl;
	                              return (Node x next)
		                   done"


text {* define traverse using the MREC combinator *}

definition
  traverse :: "'a\<Colon>heap node \<Rightarrow> 'a list Heap"
where
[code del]: "traverse = MREC (\<lambda>n. case n of Empty \<Rightarrow> return (Inl [])
                                | Node x r \<Rightarrow> (do tl \<leftarrow> Ref.lookup r;
                                                  return (Inr tl) done))
                   (\<lambda>n tl xs. case n of Empty \<Rightarrow> undefined
                                      | Node x r \<Rightarrow> return (x # xs))"


lemma traverse_simps[code, simp]:
  "traverse Empty      = return []"
  "traverse (Node x r) = do tl \<leftarrow> Ref.lookup r;
                            xs \<leftarrow> traverse tl;
                            return (x#xs)
                         done"
unfolding traverse_def
by (auto simp: traverse_def monad_simp MREC_rule)


section {* Proving correctness with relational abstraction *}

subsection {* Definition of list_of, list_of', refs_of and refs_of' *}

fun list_of :: "heap \<Rightarrow> ('a::heap) node \<Rightarrow> 'a list \<Rightarrow> bool"
where
  "list_of h r [] = (r = Empty)"
| "list_of h r (a#as) = (case r of Empty \<Rightarrow> False | Node b bs \<Rightarrow> (a = b \<and> list_of h (get_ref bs h) as))"
 
definition list_of' :: "heap \<Rightarrow> ('a::heap) node ref \<Rightarrow> 'a list \<Rightarrow> bool"
where
  "list_of' h r xs = list_of h (get_ref r h) xs"

fun refs_of :: "heap \<Rightarrow> ('a::heap) node \<Rightarrow> 'a node ref list \<Rightarrow> bool"
where
  "refs_of h r [] = (r = Empty)"
| "refs_of h r (x#xs) = (case r of Empty \<Rightarrow> False | Node b bs \<Rightarrow> (x = bs) \<and> refs_of h (get_ref bs h) xs)"

fun refs_of' :: "heap \<Rightarrow> ('a::heap) node ref \<Rightarrow> 'a node ref list \<Rightarrow> bool"
where
  "refs_of' h r [] = False"
| "refs_of' h r (x#xs) = ((x = r) \<and> refs_of h (get_ref x h) xs)"


subsection {* Properties of these definitions *}

lemma list_of_Empty[simp]: "list_of h Empty xs = (xs = [])"
by (cases xs, auto)

lemma list_of_Node[simp]: "list_of h (Node x ps) xs = (\<exists>xs'. (xs = x # xs') \<and> list_of h (get_ref ps h) xs')"
by (cases xs, auto)

lemma list_of'_Empty[simp]: "get_ref q h = Empty \<Longrightarrow> list_of' h q xs = (xs = [])"
unfolding list_of'_def by simp

lemma list_of'_Node[simp]: "get_ref q h = Node x ps \<Longrightarrow> list_of' h q xs = (\<exists>xs'. (xs = x # xs') \<and> list_of' h ps xs')"
unfolding list_of'_def by simp

lemma list_of'_Nil: "list_of' h q [] \<Longrightarrow> get_ref q h = Empty"
unfolding list_of'_def by simp

lemma list_of'_Cons: 
assumes "list_of' h q (x#xs)"
obtains n where "get_ref q h = Node x n" and "list_of' h n xs"
using assms unfolding list_of'_def by (auto split: node.split_asm)

lemma refs_of_Empty[simp] : "refs_of h Empty xs = (xs = [])"
  by (cases xs, auto)

lemma refs_of_Node[simp]: "refs_of h (Node x ps) xs = (\<exists>prs. xs = ps # prs \<and> refs_of h (get_ref ps h) prs)"
  by (cases xs, auto)

lemma refs_of'_def': "refs_of' h p ps = (\<exists>prs. (ps = (p # prs)) \<and> refs_of h (get_ref p h) prs)"
by (cases ps, auto)

lemma refs_of'_Node:
  assumes "refs_of' h p xs"
  assumes "get_ref p h = Node x pn"
  obtains pnrs
  where "xs = p # pnrs" and "refs_of' h pn pnrs"
using assms
unfolding refs_of'_def' by auto

lemma list_of_is_fun: "\<lbrakk> list_of h n xs; list_of h n ys\<rbrakk> \<Longrightarrow> xs = ys"
proof (induct xs arbitrary: ys n)
  case Nil thus ?case by auto
next
  case (Cons x xs')
  thus ?case
    by (cases ys,  auto split: node.split_asm)
qed

lemma refs_of_is_fun: "\<lbrakk> refs_of h n xs; refs_of h n ys\<rbrakk> \<Longrightarrow> xs = ys"
proof (induct xs arbitrary: ys n)
  case Nil thus ?case by auto
next
  case (Cons x xs')
  thus ?case
    by (cases ys,  auto split: node.split_asm)
qed

lemma refs_of'_is_fun: "\<lbrakk> refs_of' h p as; refs_of' h p bs \<rbrakk> \<Longrightarrow> as = bs"
unfolding refs_of'_def' by (auto dest: refs_of_is_fun)


lemma list_of_refs_of_HOL:
  assumes "list_of h r xs"
  shows "\<exists>rs. refs_of h r rs"
using assms
proof (induct xs arbitrary: r)
  case Nil thus ?case by auto
next
  case (Cons x xs')
  thus ?case
    by (cases r, auto)
qed
    
lemma list_of_refs_of:
  assumes "list_of h r xs"
  obtains rs where "refs_of h r rs"
using list_of_refs_of_HOL[OF assms]
by auto

lemma list_of'_refs_of'_HOL:
  assumes "list_of' h r xs"
  shows "\<exists>rs. refs_of' h r rs"
proof -
  from assms obtain rs' where "refs_of h (get_ref r h) rs'"
    unfolding list_of'_def by (rule list_of_refs_of)
  thus ?thesis unfolding refs_of'_def' by auto
qed

lemma list_of'_refs_of':
  assumes "list_of' h r xs"
  obtains rs where "refs_of' h r rs"
using list_of'_refs_of'_HOL[OF assms]
by auto

lemma refs_of_list_of_HOL:
  assumes "refs_of h r rs"
  shows "\<exists>xs. list_of h r xs"
using assms
proof (induct rs arbitrary: r)
  case Nil thus ?case by auto
next
  case (Cons r rs')
  thus ?case
    by (cases r, auto)
qed

lemma refs_of_list_of:
  assumes "refs_of h r rs"
  obtains xs where "list_of h r xs"
using refs_of_list_of_HOL[OF assms]
by auto

lemma refs_of'_list_of'_HOL:
  assumes "refs_of' h r rs"
  shows "\<exists>xs. list_of' h r xs"
using assms
unfolding list_of'_def refs_of'_def'
by (auto intro: refs_of_list_of)


lemma refs_of'_list_of':
  assumes "refs_of' h r rs"
  obtains xs where "list_of' h r xs"
using refs_of'_list_of'_HOL[OF assms]
by auto

lemma refs_of'E: "refs_of' h q rs \<Longrightarrow> q \<in> set rs"
unfolding refs_of'_def' by auto

lemma list_of'_refs_of'2:
  assumes "list_of' h r xs"
  shows "\<exists>rs'. refs_of' h r (r#rs')"
proof -
  from assms obtain rs where "refs_of' h r rs" by (rule list_of'_refs_of')
  thus ?thesis by (auto simp add: refs_of'_def')
qed

subsection {* More complicated properties of these predicates *}

lemma list_of_append:
  "list_of h n (as @ bs) \<Longrightarrow> \<exists>m. list_of h m bs"
apply (induct as arbitrary: n)
apply auto
apply (case_tac n)
apply auto
done

lemma refs_of_append: "refs_of h n (as @ bs) \<Longrightarrow> \<exists>m. refs_of h m bs"
apply (induct as arbitrary: n)
apply auto
apply (case_tac n)
apply auto
done

lemma refs_of_next:
assumes "refs_of h (get_ref p h) rs"
  shows "p \<notin> set rs"
proof (rule ccontr)
  assume a: "\<not> (p \<notin> set rs)"
  from this obtain as bs where split:"rs = as @ p # bs" by (fastsimp dest: split_list)
  with assms obtain q where "refs_of h q (p # bs)" by (fast dest: refs_of_append)
  with assms split show "False"
    by (cases q,auto dest: refs_of_is_fun)
qed

lemma refs_of_distinct: "refs_of h p rs \<Longrightarrow> distinct rs"
proof (induct rs arbitrary: p)
  case Nil thus ?case by simp
next
  case (Cons r rs')
  thus ?case
    by (cases p, auto simp add: refs_of_next)
qed

lemma refs_of'_distinct: "refs_of' h p rs \<Longrightarrow> distinct rs"
  unfolding refs_of'_def'
  by (fastsimp simp add: refs_of_distinct refs_of_next)


subsection {* Interaction of these predicates with our heap transitions *}

lemma list_of_set_ref: "refs_of h q rs \<Longrightarrow> p \<notin> set rs \<Longrightarrow> list_of (set_ref p v h) q as = list_of h q as"
using assms
proof (induct as arbitrary: q rs)
  case Nil thus ?case by simp
next
  case (Cons x xs)
  thus ?case
  proof (cases q)
    case Empty thus ?thesis by auto
  next
    case (Node a ref)
    from Cons(2) Node obtain rs' where 1: "refs_of h (get_ref ref h) rs'" and rs_rs': "rs = ref # rs'" by auto
    from Cons(3) rs_rs' have "ref \<noteq> p" by fastsimp
    hence ref_eq: "get_ref ref (set_ref p v h) = (get_ref ref h)" by (auto simp add: ref_get_set_neq)
    from rs_rs' Cons(3) have 2: "p \<notin> set rs'" by simp
    from Cons.hyps[OF 1 2] Node ref_eq show ?thesis by simp
  qed
qed

lemma refs_of_set_ref: "refs_of h q rs \<Longrightarrow> p \<notin> set rs \<Longrightarrow> refs_of (set_ref p v h) q as = refs_of h q as"
proof (induct as arbitrary: q rs)
  case Nil thus ?case by simp
next
  case (Cons x xs)
  thus ?case
  proof (cases q)
    case Empty thus ?thesis by auto
  next
    case (Node a ref)
    from Cons(2) Node obtain rs' where 1: "refs_of h (get_ref ref h) rs'" and rs_rs': "rs = ref # rs'" by auto
    from Cons(3) rs_rs' have "ref \<noteq> p" by fastsimp
    hence ref_eq: "get_ref ref (set_ref p v h) = (get_ref ref h)" by (auto simp add: ref_get_set_neq)
    from rs_rs' Cons(3) have 2: "p \<notin> set rs'" by simp
    from Cons.hyps[OF 1 2] Node ref_eq show ?thesis by auto
  qed
qed

lemma refs_of_set_ref2: "refs_of (set_ref p v h) q rs \<Longrightarrow> p \<notin> set rs \<Longrightarrow> refs_of (set_ref p v h) q rs = refs_of h q rs"
proof (induct rs arbitrary: q)
  case Nil thus ?case by simp
next
  case (Cons x xs)
  thus ?case
  proof (cases q)
    case Empty thus ?thesis by auto
  next
    case (Node a ref)
    from Cons(2) Node have 1:"refs_of (set_ref p v h) (get_ref ref (set_ref p v h)) xs" and x_ref: "x = ref" by auto
    from Cons(3) this have "ref \<noteq> p" by fastsimp
    hence ref_eq: "get_ref ref (set_ref p v h) = (get_ref ref h)" by (auto simp add: ref_get_set_neq)
    from Cons(3) have 2: "p \<notin> set xs" by simp
    with Cons.hyps 1 2 Node ref_eq show ?thesis
      by simp
  qed
qed

lemma list_of'_set_ref:
  assumes "refs_of' h q rs"
  assumes "p \<notin> set rs"
  shows "list_of' (set_ref p v h) q as = list_of' h q as"
proof -
  from assms have "q \<noteq> p" by (auto simp only: dest!: refs_of'E)
  with assms show ?thesis
    unfolding list_of'_def refs_of'_def'
    by (auto simp add: list_of_set_ref)
qed

lemma list_of'_set_next_ref_Node[simp]:
  assumes "list_of' h r xs"
  assumes "get_ref p h = Node x r'"
  assumes "refs_of' h r rs"
  assumes "p \<notin> set rs"
  shows "list_of' (set_ref p (Node x r) h) p (x#xs) = list_of' h r xs"
using assms
unfolding list_of'_def refs_of'_def'
by (auto simp add: list_of_set_ref noteq_refs_sym)

lemma refs_of'_set_ref:
  assumes "refs_of' h q rs"
  assumes "p \<notin> set rs"
  shows "refs_of' (set_ref p v h) q as = refs_of' h q as"
using assms
proof -
  from assms have "q \<noteq> p" by (auto simp only: dest!: refs_of'E)
  with assms show ?thesis
    unfolding refs_of'_def'
    by (auto simp add: refs_of_set_ref)
qed

lemma refs_of'_set_ref2:
  assumes "refs_of' (set_ref p v h) q rs"
  assumes "p \<notin> set rs"
  shows "refs_of' (set_ref p v h) q as = refs_of' h q as"
using assms
proof -
  from assms have "q \<noteq> p" by (auto simp only: dest!: refs_of'E)
  with assms show ?thesis
    unfolding refs_of'_def'
    apply auto
    apply (subgoal_tac "prs = prsa")
    apply (insert refs_of_set_ref2[of p v h "get_ref q h"])
    apply (erule_tac x="prs" in meta_allE)
    apply auto
    apply (auto dest: refs_of_is_fun)
    done
qed

lemma refs_of'_set_next_ref:
assumes "get_ref p h1 = Node x pn"
assumes "refs_of' (set_ref p (Node x r1) h1) p rs"
obtains r1s where "rs = (p#r1s)" and "refs_of' h1 r1 r1s"
using assms
proof -
  from assms refs_of'_distinct[OF assms(2)] have "\<exists> r1s. rs = (p # r1s) \<and> refs_of' h1 r1 r1s"
    apply -
    unfolding refs_of'_def'[of _ p]
    apply (auto, frule refs_of_set_ref2) by (auto dest: noteq_refs_sym)
  with prems show thesis by auto
qed

section {* Proving make_llist and traverse correct *}

lemma refs_of_invariant:
  assumes "refs_of h (r::('a::heap) node) xs"
  assumes "\<forall>refs. refs_of h r refs \<longrightarrow> (\<forall>ref \<in> set refs. ref_present ref h \<and> ref_present ref h' \<and> get_ref ref h = get_ref ref h')"
  shows "refs_of h' r xs"
using assms
proof (induct xs arbitrary: r)
  case Nil thus ?case by simp
next
  case (Cons x xs')
  from Cons(2) obtain v where Node: "r = Node v x" by (cases r, auto)
  from Cons(2) Node have refs_of_next: "refs_of h (get_ref x h) xs'" by simp
  from Cons(2-3) Node have ref_eq: "get_ref x h = get_ref x h'" by auto
  from ref_eq refs_of_next have 1: "refs_of h (get_ref x h') xs'" by simp
  from Cons(2) Cons(3) have "\<forall>ref \<in> set xs'. ref_present ref h \<and> ref_present ref h' \<and> get_ref ref h = get_ref ref h'"
    by fastsimp
  with Cons(3) 1 have 2: "\<forall>refs. refs_of h (get_ref x h') refs \<longrightarrow> (\<forall>ref \<in> set refs. ref_present ref h \<and> ref_present ref h' \<and> get_ref ref h = get_ref ref h')"
    by (fastsimp dest: refs_of_is_fun)
  from Cons.hyps[OF 1 2] have "refs_of h' (get_ref x h') xs'" .
  with Node show ?case by simp
qed

lemma refs_of'_invariant:
  assumes "refs_of' h r xs"
  assumes "\<forall>refs. refs_of' h r refs \<longrightarrow> (\<forall>ref \<in> set refs. ref_present ref h \<and> ref_present ref h' \<and> get_ref ref h = get_ref ref h')"
  shows "refs_of' h' r xs"
using assms
proof -
  from assms obtain prs where refs:"refs_of h (get_ref r h) prs" and xs_def: "xs = r # prs"
    unfolding refs_of'_def' by auto
  from xs_def assms have x_eq: "get_ref r h = get_ref r h'" by fastsimp
  from refs assms xs_def have 2: "\<forall>refs. refs_of h (get_ref r h) refs \<longrightarrow>
     (\<forall>ref\<in>set refs. ref_present ref h \<and> ref_present ref h' \<and> get_ref ref h = get_ref ref h')" 
    by (fastsimp dest: refs_of_is_fun)
  from refs_of_invariant [OF refs 2] xs_def x_eq show ?thesis
    unfolding refs_of'_def' by auto
qed

lemma list_of_invariant:
  assumes "list_of h (r::('a::heap) node) xs"
  assumes "\<forall>refs. refs_of h r refs \<longrightarrow> (\<forall>ref \<in> set refs. ref_present ref h \<and> ref_present ref h' \<and> get_ref ref h = get_ref ref h')"
  shows "list_of h' r xs"
using assms
proof (induct xs arbitrary: r)
  case Nil thus ?case by simp
next
  case (Cons x xs')

  from Cons(2) obtain ref where Node: "r = Node x ref"
    by (cases r, auto)
  from Cons(2) obtain rs where rs_def: "refs_of h r rs" by (rule list_of_refs_of)
  from Node rs_def obtain rss where refs_of: "refs_of h r (ref#rss)" and rss_def: "rs = ref#rss" by auto
  from Cons(3) Node refs_of have ref_eq: "get_ref ref h = get_ref ref h'"
    by auto
  from Cons(2) ref_eq Node have 1: "list_of h (get_ref ref h') xs'" by simp
  from refs_of Node ref_eq have refs_of_ref: "refs_of h (get_ref ref h') rss" by simp
  from Cons(3) rs_def have rs_heap_eq: "\<forall>ref\<in>set rs. ref_present ref h \<and> ref_present ref h' \<and> get_ref ref h = get_ref ref h'" by simp
  from refs_of_ref rs_heap_eq rss_def have 2: "\<forall>refs. refs_of h (get_ref ref h') refs \<longrightarrow>
          (\<forall>ref\<in>set refs. ref_present ref h \<and> ref_present ref h' \<and> get_ref ref h = get_ref ref h')"
    by (auto dest: refs_of_is_fun)
  from Cons(1)[OF 1 2]
  have "list_of h' (get_ref ref h') xs'" .
  with Node show ?case
    unfolding list_of'_def
    by simp
qed

lemma make_llist:
assumes "crel (make_llist xs) h h' r"
shows "list_of h' r xs \<and> (\<forall>rs. refs_of h' r rs \<longrightarrow> (\<forall>ref \<in> (set rs). ref_present ref h'))"
using assms 
proof (induct xs arbitrary: h h' r)
  case Nil thus ?case by (auto elim: crel_return simp add: make_llist.simps)
next
  case (Cons x xs')
  from Cons.prems obtain h1 r1 r' where make_llist: "crel (make_llist xs') h h1 r1"
    and crel_refnew:"crel (Ref.new r1) h1 h' r'" and Node: "r = Node x r'"
    unfolding make_llist.simps
    by (auto elim!: crelE crel_return)
  from Cons.hyps[OF make_llist] have list_of_h1: "list_of h1 r1 xs'" ..
  from Cons.hyps[OF make_llist] obtain rs' where rs'_def: "refs_of h1 r1 rs'" by (auto intro: list_of_refs_of)
  from Cons.hyps[OF make_llist] rs'_def have refs_present: "\<forall>ref\<in>set rs'. ref_present ref h1" by simp
  from crel_refnew rs'_def refs_present have refs_unchanged: "\<forall>refs. refs_of h1 r1 refs \<longrightarrow>
         (\<forall>ref\<in>set refs. ref_present ref h1 \<and> ref_present ref h' \<and> get_ref ref h1 = get_ref ref h')"
    by (auto elim!: crel_Ref_new dest: refs_of_is_fun)
  with list_of_invariant[OF list_of_h1 refs_unchanged] Node crel_refnew have fstgoal: "list_of h' r (x # xs')"
    unfolding list_of.simps
    by (auto elim!: crel_Ref_new)
  from refs_unchanged rs'_def have refs_still_present: "\<forall>ref\<in>set rs'. ref_present ref h'" by auto
  from refs_of_invariant[OF rs'_def refs_unchanged] refs_unchanged Node crel_refnew refs_still_present
  have sndgoal: "\<forall>rs. refs_of h' r rs \<longrightarrow> (\<forall>ref\<in>set rs. ref_present ref h')"
    by (fastsimp elim!: crel_Ref_new dest: refs_of_is_fun)
  from fstgoal sndgoal show ?case ..
qed

lemma traverse: "list_of h n r \<Longrightarrow> crel (traverse n) h h r"
proof (induct r arbitrary: n)
  case Nil
  thus ?case
    by (auto intro: crel_returnI)
next
  case (Cons x xs)
  thus ?case
  apply (cases n, auto)
  by (auto intro!: crelI crel_returnI crel_lookupI)
qed

lemma traverse_make_llist':
  assumes crel: "crel (make_llist xs \<guillemotright>= traverse) h h' r"
  shows "r = xs"
proof -
  from crel obtain h1 r1
    where makell: "crel (make_llist xs) h h1 r1"
    and trav: "crel (traverse r1) h1 h' r"
    by (auto elim!: crelE)
  from make_llist[OF makell] have "list_of h1 r1 xs" ..
  from traverse [OF this] trav show ?thesis
    using crel_deterministic by fastsimp
qed

section {* Proving correctness of in-place reversal *}

subsection {* Definition of in-place reversal *}

definition rev' :: "(('a::heap) node ref \<times> 'a node ref) \<Rightarrow> 'a node ref Heap"
where "rev' = MREC (\<lambda>(q, p). do v \<leftarrow> !p; (case v of Empty \<Rightarrow> (return (Inl q))
                            | Node x next \<Rightarrow> do
                                    p := Node x q;
                                    return (Inr (p, next))
                                  done) done)
             (\<lambda>x s z. return z)"

lemma rev'_simps [code]:
  "rev' (q, p) =
   do
     v \<leftarrow> !p;
     (case v of
        Empty \<Rightarrow> return q
      | Node x next \<Rightarrow>
        do
          p := Node x q;
          rev' (p, next)
        done)
  done"
  unfolding rev'_def MREC_rule[of _ _ "(q, p)"] unfolding rev'_def[symmetric]
thm arg_cong2
  by (auto simp add: monad_simp expand_fun_eq intro: arg_cong2[where f = "op \<guillemotright>="] split: node.split)

fun rev :: "('a:: heap) node \<Rightarrow> 'a node Heap" 
where
  "rev Empty = return Empty"
| "rev (Node x n) = (do q \<leftarrow> Ref.new Empty; p \<leftarrow> Ref.new (Node x n); v \<leftarrow> rev' (q, p); !v done)"

subsection {* Correctness Proof *}

lemma rev'_invariant:
  assumes "crel (rev' (q, p)) h h' v"
  assumes "list_of' h q qs"
  assumes "list_of' h p ps"
  assumes "\<forall>qrs prs. refs_of' h q qrs \<and> refs_of' h p prs \<longrightarrow> set prs \<inter> set qrs = {}"
  shows "\<exists>vs. list_of' h' v vs \<and> vs = (List.rev ps) @ qs"
using assms
proof (induct ps arbitrary: qs p q h)
  case Nil
  thus ?case
    unfolding rev'_simps[of q p] list_of'_def
    by (auto elim!: crelE crel_lookup crel_return)
next
  case (Cons x xs)
  (*"LinkedList.list_of h' (get_ref v h') (List.rev xs @ x # qsa)"*)
  from Cons(4) obtain ref where 
    p_is_Node: "get_ref p h = Node x ref"
    (*and "ref_present ref h"*)
    and list_of'_ref: "list_of' h ref xs"
    unfolding list_of'_def by (cases "get_ref p h", auto)
  from p_is_Node Cons(2) have crel_rev': "crel (rev' (p, ref)) (set_ref p (Node x q) h) h' v"
    by (auto simp add: rev'_simps [of q p] elim!: crelE crel_lookup crel_update)
  from Cons(3) obtain qrs where qrs_def: "refs_of' h q qrs" by (elim list_of'_refs_of')
  from Cons(4) obtain prs where prs_def: "refs_of' h p prs" by (elim list_of'_refs_of')
  from qrs_def prs_def Cons(5) have distinct_pointers: "set qrs \<inter> set prs = {}" by fastsimp
  from qrs_def prs_def distinct_pointers refs_of'E have p_notin_qrs: "p \<notin> set qrs" by fastsimp
  from Cons(3) qrs_def this have 1: "list_of' (set_ref p (Node x q) h) p (x#qs)"
    unfolding list_of'_def  
    apply (simp)
    unfolding list_of'_def[symmetric]
    by (simp add: list_of'_set_ref)
  from list_of'_refs_of'2[OF Cons(4)] p_is_Node prs_def obtain refs where refs_def: "refs_of' h ref refs" and prs_refs: "prs = p # refs"
    unfolding refs_of'_def' by auto
  from prs_refs prs_def have p_not_in_refs: "p \<notin> set refs"
    by (fastsimp dest!: refs_of'_distinct)
  with refs_def p_is_Node list_of'_ref have 2: "list_of' (set_ref p (Node x q) h) ref xs"
    by (auto simp add: list_of'_set_ref)
  from p_notin_qrs qrs_def have refs_of1: "refs_of' (set_ref p (Node x q) h) p (p#qrs)"
    unfolding refs_of'_def'
    apply (simp)
    unfolding refs_of'_def'[symmetric]
    by (simp add: refs_of'_set_ref)
  from p_not_in_refs p_is_Node refs_def have refs_of2: "refs_of' (set_ref p (Node x q) h) ref refs"
    by (simp add: refs_of'_set_ref)
  from p_not_in_refs refs_of1 refs_of2 distinct_pointers prs_refs have 3: "\<forall>qrs prs. refs_of' (set_ref p (Node x q) h) p qrs \<and> refs_of' (set_ref p (Node x q) h) ref prs \<longrightarrow> set prs \<inter> set qrs = {}"
    apply - apply (rule allI)+ apply (rule impI) apply (erule conjE)
    apply (drule refs_of'_is_fun) back back apply assumption
    apply (drule refs_of'_is_fun) back back apply assumption
    apply auto done
  from Cons.hyps [OF crel_rev' 1 2 3] show ?case by simp
qed


lemma rev_correctness:
  assumes list_of_h: "list_of h r xs"
  assumes validHeap: "\<forall>refs. refs_of h r refs \<longrightarrow> (\<forall>r \<in> set refs. ref_present r h)"
  assumes crel_rev: "crel (rev r) h h' r'"
  shows "list_of h' r' (List.rev xs)"
using assms
proof (cases r)
  case Empty
  with list_of_h crel_rev show ?thesis
    by (auto simp add: list_of_Empty elim!: crel_return)
next
  case (Node x ps)
  with crel_rev obtain p q h1 h2 h3 v where
    init: "crel (Ref.new Empty) h h1 q"
    "crel (Ref.new (Node x ps)) h1 h2 p"
    and crel_rev':"crel (rev' (q, p)) h2 h3 v"
    and lookup: "crel (!v) h3 h' r'"
    using rev.simps
    by (auto elim!: crelE)
  from init have a1:"list_of' h2 q []"
    unfolding list_of'_def
    by (auto elim!: crel_Ref_new)
  from list_of_h obtain refs where refs_def: "refs_of h r refs" by (rule list_of_refs_of)
  from validHeap init refs_def have heap_eq: "\<forall>refs. refs_of h r refs \<longrightarrow> (\<forall>ref\<in>set refs. ref_present ref h \<and> ref_present ref h2 \<and> get_ref ref h = get_ref ref h2)"
    by (fastsimp elim!: crel_Ref_new dest: refs_of_is_fun)
  from list_of_invariant[OF list_of_h heap_eq] have "list_of h2 r xs" .
  from init this Node have a2: "list_of' h2 p xs"
    apply -
    unfolding list_of'_def
    apply (auto elim!: crel_Ref_new)
    done
  from init have refs_of_q: "refs_of' h2 q [q]"
    by (auto elim!: crel_Ref_new)
  from refs_def Node have refs_of'_ps: "refs_of' h ps refs"
    by (auto simp add: refs_of'_def'[symmetric])
  from validHeap refs_def have all_ref_present: "\<forall>r\<in>set refs. ref_present r h" by simp
  from init refs_of'_ps Node this have heap_eq: "\<forall>refs. refs_of' h ps refs \<longrightarrow> (\<forall>ref\<in>set refs. ref_present ref h \<and> ref_present ref h2 \<and> get_ref ref h = get_ref ref h2)"
    by (fastsimp elim!: crel_Ref_new dest: refs_of'_is_fun)
  from refs_of'_invariant[OF refs_of'_ps this] have "refs_of' h2 ps refs" .
  with init have refs_of_p: "refs_of' h2 p (p#refs)"
    by (auto elim!: crel_Ref_new simp add: refs_of'_def')
  with init all_ref_present have q_is_new: "q \<notin> set (p#refs)"
    by (auto elim!: crel_Ref_new intro!: noteq_refsI)
  from refs_of_p refs_of_q q_is_new have a3: "\<forall>qrs prs. refs_of' h2 q qrs \<and> refs_of' h2 p prs \<longrightarrow> set prs \<inter> set qrs = {}"
    by (fastsimp simp only: set.simps dest: refs_of'_is_fun)
  from rev'_invariant [OF crel_rev' a1 a2 a3] have "list_of h3 (get_ref v h3) (List.rev xs)" 
    unfolding list_of'_def by auto
  with lookup show ?thesis
    by (auto elim: crel_lookup)
qed


section {* The merge function on Linked Lists *}
text {* We also prove merge correct *}

text{* First, we define merge on lists in a natural way. *}

fun Lmerge :: "('a::ord) list \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "Lmerge (x#xs) (y#ys) =
     (if x \<le> y then x # Lmerge xs (y#ys) else y # Lmerge (x#xs) ys)"
| "Lmerge [] ys = ys"
| "Lmerge xs [] = xs"

subsection {* Definition of merge function *}

definition merge' :: "(('a::{heap, ord}) node ref * ('a::{heap, ord})) * ('a::{heap, ord}) node ref * ('a::{heap, ord}) node ref \<Rightarrow> ('a::{heap, ord}) node ref Heap"
where
"merge' = MREC (\<lambda>(_, p, q). (do v \<leftarrow> !p; w \<leftarrow> !q;
  (case v of Empty \<Rightarrow> return (Inl q)
          | Node valp np \<Rightarrow>
            (case w of Empty \<Rightarrow> return (Inl p)
                     | Node valq nq \<Rightarrow>
                       if (valp \<le> valq) then
                         return (Inr ((p, valp), np, q))
                       else
                         return (Inr ((q, valq), p, nq)))) done))
 (\<lambda> _ ((n, v), _, _) r. do n := Node v r; return n done)"

definition merge where "merge p q = merge' (undefined, p, q)"

lemma if_return: "(if P then return x else return y) = return (if P then x else y)"
by auto

lemma if_distrib_App: "(if P then f else g) x = (if P then f x else g x)"
by auto
lemma redundant_if: "(if P then (if P then x else z) else y) = (if P then x else y)"
  "(if P then x else (if P then z else y)) = (if P then x else y)"
by auto



lemma sum_distrib: "sum_case fl fr (case x of Empty \<Rightarrow> y | Node v n \<Rightarrow> (z v n)) = (case x of Empty \<Rightarrow> sum_case fl fr y | Node v n \<Rightarrow> sum_case fl fr (z v n))"
by (cases x) auto

lemma merge: "merge' (x, p, q) = merge p q"
unfolding merge'_def merge_def
apply (simp add: MREC_rule) done
term "Ref.change"
lemma merge_simps [code]:
shows "merge p q =
do v \<leftarrow> !p;
   w \<leftarrow> !q;
   (case v of node.Empty \<Rightarrow> return q
    | Node valp np \<Rightarrow>
        case w of node.Empty \<Rightarrow> return p
        | Node valq nq \<Rightarrow>
            if valp \<le> valq then do r \<leftarrow> merge np q;
                                   p := (Node valp r);
                                   return p
                                done
            else do r \<leftarrow> merge p nq;
                    q := (Node valq r);
                    return q
                 done)
done"
proof -
  {fix v x y
    have case_return: "(case v of Empty \<Rightarrow> return x | Node v n \<Rightarrow> return (y v n)) = return (case v of Empty \<Rightarrow> x | Node v n \<Rightarrow> y v n)" by (cases v) auto
    } note case_return = this
show ?thesis
unfolding merge_def[of p q] merge'_def
apply (simp add: MREC_rule[of _ _ "(undefined, p, q)"])
unfolding bind_bind return_bind
unfolding merge'_def[symmetric]
unfolding if_return case_return bind_bind return_bind sum_distrib sum.cases
unfolding if_distrib[symmetric, where f="Inr"]
unfolding sum.cases
unfolding if_distrib
unfolding split_beta fst_conv snd_conv
unfolding if_distrib_App redundant_if merge
..
qed

subsection {* Induction refinement by applying the abstraction function to our induct rule *}

text {* From our original induction rule Lmerge.induct, we derive a new rule with our list_of' predicate *}

lemma merge_induct2:
  assumes "list_of' h (p::'a::{heap, ord} node ref) xs"
  assumes "list_of' h q ys"
  assumes "\<And> ys p q. \<lbrakk> list_of' h p []; list_of' h q ys; get_ref p h = Empty \<rbrakk> \<Longrightarrow> P p q [] ys"
  assumes "\<And> x xs' p q pn. \<lbrakk> list_of' h p (x#xs'); list_of' h q []; get_ref p h = Node x pn; get_ref q h = Empty \<rbrakk> \<Longrightarrow> P p q (x#xs') []"
  assumes "\<And> x xs' y ys' p q pn qn.
  \<lbrakk> list_of' h p (x#xs'); list_of' h q (y#ys'); get_ref p h = Node x pn; get_ref q h = Node y qn;
  x \<le> y; P pn q xs' (y#ys') \<rbrakk>
  \<Longrightarrow> P p q (x#xs') (y#ys')"
  assumes "\<And> x xs' y ys' p q pn qn.
  \<lbrakk> list_of' h p (x#xs'); list_of' h q (y#ys'); get_ref p h = Node x pn; get_ref q h = Node y qn;
  \<not> x \<le> y; P p qn (x#xs') ys'\<rbrakk>
  \<Longrightarrow> P p q (x#xs') (y#ys')"
  shows "P p q xs ys"
using assms(1-2)
proof (induct xs ys arbitrary: p q rule: Lmerge.induct)
  case (2 ys)
  from 2(1) have "get_ref p h = Empty" unfolding list_of'_def by simp
  with 2(1-2) assms(3) show ?case by blast
next
  case (3 x xs')
  from 3(1) obtain pn where Node: "get_ref p h = Node x pn" by (rule list_of'_Cons)
  from 3(2) have "get_ref q h = Empty" unfolding list_of'_def by simp
  with Node 3(1-2) assms(4) show ?case by blast
next
  case (1 x xs' y ys')
  from 1(3) obtain pn where pNode:"get_ref p h = Node x pn"
    and list_of'_pn: "list_of' h pn xs'" by (rule list_of'_Cons)
  from 1(4) obtain qn where qNode:"get_ref q h = Node y qn"
    and  list_of'_qn: "list_of' h qn ys'" by (rule list_of'_Cons)
  show ?case
  proof (cases "x \<le> y")
    case True
    from 1(1)[OF True list_of'_pn 1(4)] assms(5) 1(3-4) pNode qNode True
    show ?thesis by blast
  next
    case False
    from 1(2)[OF False 1(3) list_of'_qn] assms(6) 1(3-4) pNode qNode False
    show ?thesis by blast
  qed
qed


text {* secondly, we add the crel statement in the premise, and derive the crel statements for the single cases which we then eliminate with our crel elim rules. *}
  
lemma merge_induct3: 
assumes  "list_of' h p xs"
assumes  "list_of' h q ys"
assumes  "crel (merge p q) h h' r"
assumes  "\<And> ys p q. \<lbrakk> list_of' h p []; list_of' h q ys; get_ref p h = Empty \<rbrakk> \<Longrightarrow> P p q h h q [] ys"
assumes  "\<And> x xs' p q pn. \<lbrakk> list_of' h p (x#xs'); list_of' h q []; get_ref p h = Node x pn; get_ref q h = Empty \<rbrakk> \<Longrightarrow> P p q h h p (x#xs') []"
assumes  "\<And> x xs' y ys' p q pn qn h1 r1 h'.
  \<lbrakk> list_of' h p (x#xs'); list_of' h q (y#ys');get_ref p h = Node x pn; get_ref q h = Node y qn;
  x \<le> y; crel (merge pn q) h h1 r1 ; P pn q h h1 r1 xs' (y#ys'); h' = set_ref p (Node x r1) h1 \<rbrakk>
  \<Longrightarrow> P p q h h' p (x#xs') (y#ys')"
assumes "\<And> x xs' y ys' p q pn qn h1 r1 h'.
  \<lbrakk> list_of' h p (x#xs'); list_of' h q (y#ys'); get_ref p h = Node x pn; get_ref q h = Node y qn;
  \<not> x \<le> y; crel (merge p qn) h h1 r1; P p qn h h1 r1 (x#xs') ys'; h' = set_ref q (Node y r1) h1 \<rbrakk>
  \<Longrightarrow> P p q h h' q (x#xs') (y#ys')"
shows "P p q h h' r xs ys"
using assms(3)
proof (induct arbitrary: h' r rule: merge_induct2[OF assms(1) assms(2)])
  case (1 ys p q)
  from 1(3-4) have "h = h' \<and> r = q"
    unfolding merge_simps[of p q]
    by (auto elim!: crel_lookup crelE crel_return)
  with assms(4)[OF 1(1) 1(2) 1(3)] show ?case by simp
next
  case (2 x xs' p q pn)
  from 2(3-5) have "h = h' \<and> r = p"
    unfolding merge_simps[of p q]
    by (auto elim!: crel_lookup crelE crel_return)
  with assms(5)[OF 2(1-4)] show ?case by simp
next
  case (3 x xs' y ys' p q pn qn)
  from 3(3-5) 3(7) obtain h1 r1 where
    1: "crel (merge pn q) h h1 r1" 
    and 2: "h' = set_ref p (Node x r1) h1 \<and> r = p"
    unfolding merge_simps[of p q]
    by (auto elim!: crel_lookup crelE crel_return crel_if crel_update)
  from 3(6)[OF 1] assms(6) [OF 3(1-5)] 1 2 show ?case by simp
next
  case (4 x xs' y ys' p q pn qn)
  from 4(3-5) 4(7) obtain h1 r1 where
    1: "crel (merge p qn) h h1 r1" 
    and 2: "h' = set_ref q (Node y r1) h1 \<and> r = q"
    unfolding merge_simps[of p q]
    by (auto elim!: crel_lookup crelE crel_return crel_if crel_update)
  from 4(6)[OF 1] assms(7) [OF 4(1-5)] 1 2 show ?case by simp
qed


subsection {* Proving merge correct *}

text {* As many parts of the following three proofs are identical, we could actually move the
same reasoning into an extended induction rule *}
 
lemma merge_unchanged:
  assumes "refs_of' h p xs"
  assumes "refs_of' h q ys"  
  assumes "crel (merge p q) h h' r'"
  assumes "set xs \<inter> set ys = {}"
  assumes "r \<notin> set xs \<union> set ys"
  shows "get_ref r h = get_ref r h'"
proof -
  from assms(1) obtain ps where ps_def: "list_of' h p ps" by (rule refs_of'_list_of')
  from assms(2) obtain qs where qs_def: "list_of' h q qs" by (rule refs_of'_list_of')
  show ?thesis using assms(1) assms(2) assms(4) assms(5)
  proof (induct arbitrary: xs ys r rule: merge_induct3[OF ps_def qs_def assms(3)])
    case 1 thus ?case by simp
  next
    case 2 thus ?case by simp
  next
    case (3 x xs' y ys' p q pn qn h1 r1 h' xs ys r)
    from 3(9) 3(3) obtain pnrs
      where pnrs_def: "xs = p#pnrs"
      and refs_of'_pn: "refs_of' h pn pnrs"
      by (rule refs_of'_Node)
    with 3(12) have r_in: "r \<notin> set pnrs \<union> set ys" by auto
    from pnrs_def 3(12) have "r \<noteq> p" by auto
    with 3(11) 3(12) pnrs_def refs_of'_distinct[OF 3(9)] have p_in: "p \<notin> set pnrs \<union> set ys" by auto
    from 3(11) pnrs_def have no_inter: "set pnrs \<inter> set ys = {}" by auto
    from 3(7)[OF refs_of'_pn 3(10) this p_in] 3(3) have p_is_Node: "get_ref p h1 = Node x pn" by simp
    from 3(7)[OF refs_of'_pn 3(10) no_inter r_in] 3(8) `r \<noteq> p` show ?case
      by simp
  next
    case (4 x xs' y ys' p q pn qn h1 r1 h' xs ys r)
    from 4(10) 4(4) obtain qnrs
      where qnrs_def: "ys = q#qnrs"
      and refs_of'_qn: "refs_of' h qn qnrs"
      by (rule refs_of'_Node)
    with 4(12) have r_in: "r \<notin> set xs \<union> set qnrs" by auto
    from qnrs_def 4(12) have "r \<noteq> q" by auto
    with 4(11) 4(12) qnrs_def refs_of'_distinct[OF 4(10)] have q_in: "q \<notin> set xs \<union> set qnrs" by auto
    from 4(11) qnrs_def have no_inter: "set xs \<inter> set qnrs = {}" by auto
    from 4(7)[OF 4(9) refs_of'_qn this q_in] 4(4) have q_is_Node: "get_ref q h1 = Node y qn" by simp
    from 4(7)[OF 4(9) refs_of'_qn no_inter r_in] 4(8) `r \<noteq> q` show ?case
      by simp
  qed
qed

lemma refs_of'_merge:
  assumes "refs_of' h p xs"
  assumes "refs_of' h q ys"
  assumes "crel (merge p q) h h' r"
  assumes "set xs \<inter> set ys = {}"
  assumes "refs_of' h' r rs"
  shows "set rs \<subseteq> set xs \<union> set ys"
proof -
  from assms(1) obtain ps where ps_def: "list_of' h p ps" by (rule refs_of'_list_of')
  from assms(2) obtain qs where qs_def: "list_of' h q qs" by (rule refs_of'_list_of')
  show ?thesis using assms(1) assms(2) assms(4) assms(5)
  proof (induct arbitrary: xs ys rs rule: merge_induct3[OF ps_def qs_def assms(3)])
    case 1
    from 1(5) 1(7) have "rs = ys" by (fastsimp simp add: refs_of'_is_fun)
    thus ?case by auto
  next
    case 2
    from 2(5) 2(8) have "rs = xs" by (auto simp add: refs_of'_is_fun)
    thus ?case by auto
  next
    case (3 x xs' y ys' p q pn qn h1 r1 h' xs ys rs)
    from 3(9) 3(3) obtain pnrs
      where pnrs_def: "xs = p#pnrs"
      and refs_of'_pn: "refs_of' h pn pnrs"
      by (rule refs_of'_Node)
    from 3(10) 3(9) 3(11) pnrs_def refs_of'_distinct[OF 3(9)] have p_in: "p \<notin> set pnrs \<union> set ys" by auto
    from 3(11) pnrs_def have no_inter: "set pnrs \<inter> set ys = {}" by auto
    from merge_unchanged[OF refs_of'_pn 3(10) 3(6) no_inter p_in] have p_stays: "get_ref p h1 = get_ref p h" ..
    from 3 p_stays obtain r1s
      where rs_def: "rs = p#r1s" and refs_of'_r1:"refs_of' h1 r1 r1s"
      by (auto elim: refs_of'_set_next_ref)
    from 3(7)[OF refs_of'_pn 3(10) no_inter refs_of'_r1] rs_def pnrs_def show ?case by auto
  next
    case (4 x xs' y ys' p q pn qn h1 r1 h' xs ys rs)
    from 4(10) 4(4) obtain qnrs
      where qnrs_def: "ys = q#qnrs"
      and refs_of'_qn: "refs_of' h qn qnrs"
      by (rule refs_of'_Node)
    from 4(10) 4(9) 4(11) qnrs_def refs_of'_distinct[OF 4(10)] have q_in: "q \<notin> set xs \<union> set qnrs" by auto
    from 4(11) qnrs_def have no_inter: "set xs \<inter> set qnrs = {}" by auto
    from merge_unchanged[OF 4(9) refs_of'_qn 4(6) no_inter q_in] have q_stays: "get_ref q h1 = get_ref q h" ..
    from 4 q_stays obtain r1s
      where rs_def: "rs = q#r1s" and refs_of'_r1:"refs_of' h1 r1 r1s"
      by (auto elim: refs_of'_set_next_ref)
    from 4(7)[OF 4(9) refs_of'_qn no_inter refs_of'_r1] rs_def qnrs_def show ?case by auto
  qed
qed

lemma
  assumes "list_of' h p xs"
  assumes "list_of' h q ys"
  assumes "crel (merge p q) h h' r"
  assumes "\<forall>qrs prs. refs_of' h q qrs \<and> refs_of' h p prs \<longrightarrow> set prs \<inter> set qrs = {}"
  shows "list_of' h' r (Lmerge xs ys)"
using assms(4)
proof (induct rule: merge_induct3[OF assms(1-3)])
  case 1
  thus ?case by simp
next
  case 2
  thus ?case by simp
next
  case (3 x xs' y ys' p q pn qn h1 r1 h')
  from 3(1) obtain prs where prs_def: "refs_of' h p prs" by (rule list_of'_refs_of')
  from 3(2) obtain qrs where qrs_def: "refs_of' h q qrs" by (rule list_of'_refs_of')
  from prs_def 3(3) obtain pnrs
    where pnrs_def: "prs = p#pnrs"
    and refs_of'_pn: "refs_of' h pn pnrs"
    by (rule refs_of'_Node)
  from prs_def qrs_def 3(9) pnrs_def refs_of'_distinct[OF prs_def] have p_in: "p \<notin> set pnrs \<union> set qrs" by fastsimp
  from prs_def qrs_def 3(9) pnrs_def have no_inter: "set pnrs \<inter> set qrs = {}" by fastsimp
  from no_inter refs_of'_pn qrs_def have no_inter2: "\<forall>qrs prs. refs_of' h q qrs \<and> refs_of' h pn prs \<longrightarrow> set prs \<inter> set qrs = {}"
    by (fastsimp dest: refs_of'_is_fun)
  from merge_unchanged[OF refs_of'_pn qrs_def 3(6) no_inter p_in] have p_stays: "get_ref p h1 = get_ref p h" ..
  from 3(7)[OF no_inter2] obtain rs where rs_def: "refs_of' h1 r1 rs" by (rule list_of'_refs_of')
  from refs_of'_merge[OF refs_of'_pn qrs_def 3(6) no_inter this] p_in have p_rs: "p \<notin> set rs" by auto
  with 3(7)[OF no_inter2] 3(1-5) 3(8) p_rs rs_def p_stays
  show ?case by auto
next
  case (4 x xs' y ys' p q pn qn h1 r1 h')
  from 4(1) obtain prs where prs_def: "refs_of' h p prs" by (rule list_of'_refs_of')
  from 4(2) obtain qrs where qrs_def: "refs_of' h q qrs" by (rule list_of'_refs_of')
  from qrs_def 4(4) obtain qnrs
    where qnrs_def: "qrs = q#qnrs"
    and refs_of'_qn: "refs_of' h qn qnrs"
    by (rule refs_of'_Node)
  from prs_def qrs_def 4(9) qnrs_def refs_of'_distinct[OF qrs_def] have q_in: "q \<notin> set prs \<union> set qnrs" by fastsimp
  from prs_def qrs_def 4(9) qnrs_def have no_inter: "set prs \<inter> set qnrs = {}" by fastsimp
  from no_inter refs_of'_qn prs_def have no_inter2: "\<forall>qrs prs. refs_of' h qn qrs \<and> refs_of' h p prs \<longrightarrow> set prs \<inter> set qrs = {}"
    by (fastsimp dest: refs_of'_is_fun)
  from merge_unchanged[OF prs_def refs_of'_qn 4(6) no_inter q_in] have q_stays: "get_ref q h1 = get_ref q h" ..
  from 4(7)[OF no_inter2] obtain rs where rs_def: "refs_of' h1 r1 rs" by (rule list_of'_refs_of')
  from refs_of'_merge[OF prs_def refs_of'_qn 4(6) no_inter this] q_in have q_rs: "q \<notin> set rs" by auto
  with 4(7)[OF no_inter2] 4(1-5) 4(8) q_rs rs_def q_stays
  show ?case by auto
qed

section {* Code generation *}

export_code merge in SML file -

export_code rev in SML file -

text {* A simple example program *}

definition test_1 where "test_1 = (do ll_xs <- make_llist [1..(15::int)]; xs <- traverse ll_xs; return xs done)" 
definition test_2 where "test_2 = (do ll_xs <- make_llist [1..(15::int)]; ll_ys <- rev ll_xs; ys <- traverse ll_ys; return ys done)"

definition test_3 where "test_3 =
  (do
    ll_xs \<leftarrow> make_llist (filter (%n. n mod 2 = 0) [2..8]);
    ll_ys \<leftarrow> make_llist (filter (%n. n mod 2 = 1) [5..11]);
    r \<leftarrow> Ref.new ll_xs;
    q \<leftarrow> Ref.new ll_ys;
    p \<leftarrow> merge r q;
    ll_zs \<leftarrow> !p;
    zs \<leftarrow> traverse ll_zs;
    return zs
  done)"

ML {* @{code test_1} () *}
ML {* @{code test_2} () *}
ML {* @{code test_3} () *}

end