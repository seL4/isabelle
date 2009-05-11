(*  Title:      HOL/Library/Graphs.thy
    ID:         $Id$
    Author:     Alexander Krauss, TU Muenchen
*)

header {* General Graphs as Sets *}

theory Graphs
imports Main Misc_Tools Kleene_Algebras
begin

subsection {* Basic types, Size Change Graphs *}

datatype ('a, 'b) graph = 
  Graph "('a \<times> 'b \<times> 'a) set"

primrec dest_graph :: "('a, 'b) graph \<Rightarrow> ('a \<times> 'b \<times> 'a) set"
  where "dest_graph (Graph G) = G"

lemma graph_dest_graph[simp]:
  "Graph (dest_graph G) = G"
  by (cases G) simp

lemma split_graph_all:
  "(\<And>gr. PROP P gr) \<equiv> (\<And>set. PROP P (Graph set))"
proof
  fix set
  assume "\<And>gr. PROP P gr"
  then show "PROP P (Graph set)" .
next
  fix gr
  assume "\<And>set. PROP P (Graph set)"
  then have "PROP P (Graph (dest_graph gr))" .
  then show "PROP P gr" by simp
qed

definition 
  has_edge :: "('n,'e) graph \<Rightarrow> 'n \<Rightarrow> 'e \<Rightarrow> 'n \<Rightarrow> bool"
("_ \<turnstile> _ \<leadsto>\<^bsup>_\<^esup> _")
where
  "has_edge G n e n' = ((n, e, n') \<in> dest_graph G)"


subsection {* Graph composition *}

fun grcomp :: "('n, 'e::times) graph \<Rightarrow> ('n, 'e) graph  \<Rightarrow> ('n, 'e) graph"
where
  "grcomp (Graph G) (Graph H) = 
  Graph {(p,b,q) | p b q. 
  (\<exists>k e e'. (p,e,k)\<in>G \<and> (k,e',q)\<in>H \<and> b = e * e')}"


declare grcomp.simps[code del]


lemma graph_ext:
  assumes "\<And>n e n'. has_edge G n e n' = has_edge H n e n'"
  shows "G = H"
  using assms
  by (cases G, cases H) (auto simp:split_paired_all has_edge_def)


instantiation graph :: (type, type) comm_monoid_add
begin

definition
  graph_zero_def: "0 = Graph {}" 

definition
  graph_plus_def [code del]: "G + H = Graph (dest_graph G \<union> dest_graph H)"

instance proof
  fix x y z :: "('a,'b) graph"
  show "x + y + z = x + (y + z)" 
   and "x + y = y + x" 
   and "0 + x = x"
  unfolding graph_plus_def graph_zero_def by auto
qed

end

instantiation graph :: (type, type) "{distrib_lattice, complete_lattice}"
begin

definition
  graph_leq_def [code del]: "G \<le> H \<longleftrightarrow> dest_graph G \<subseteq> dest_graph H"

definition
  graph_less_def [code del]: "G < H \<longleftrightarrow> dest_graph G \<subset> dest_graph H"

definition
  [code del]: "bot = Graph {}"

definition
  [code del]: "top = Graph UNIV"

definition
  [code del]: "inf G H = Graph (dest_graph G \<inter> dest_graph H)"

definition
  [code del]: "sup (G \<Colon> ('a, 'b) graph) H = G + H"

definition
  Inf_graph_def [code del]: "Inf = (\<lambda>Gs. Graph (\<Inter>(dest_graph ` Gs)))"

definition
  Sup_graph_def [code del]: "Sup = (\<lambda>Gs. Graph (\<Union>(dest_graph ` Gs)))"

instance proof
  fix x y z :: "('a,'b) graph"
  fix A :: "('a, 'b) graph set"

  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    unfolding graph_leq_def graph_less_def
    by (cases x, cases y) auto

  show "x \<le> x" unfolding graph_leq_def ..

  { assume "x \<le> y" "y \<le> z" 
    with order_trans show "x \<le> z"
      unfolding graph_leq_def . }

  { assume "x \<le> y" "y \<le> x" thus "x = y" 
      unfolding graph_leq_def 
      by (cases x, cases y) simp }

  show "inf x y \<le> x" "inf x y \<le> y"
    unfolding inf_graph_def graph_leq_def 
    by auto    
  
  { assume "x \<le> y" "x \<le> z" thus "x \<le> inf y z"
      unfolding inf_graph_def graph_leq_def 
      by auto }

  show "x \<le> sup x y" "y \<le> sup x y"
    unfolding sup_graph_def graph_leq_def graph_plus_def by auto

  { assume "y \<le> x" "z \<le> x" thus "sup y z \<le> x"
      unfolding sup_graph_def graph_leq_def graph_plus_def by auto }

  show "bot \<le> x" unfolding graph_leq_def bot_graph_def by simp

  show "x \<le> top" unfolding graph_leq_def top_graph_def by simp
  
  show "sup x (inf y z) = inf (sup x y) (sup x z)"
    unfolding inf_graph_def sup_graph_def graph_leq_def graph_plus_def by auto

  { assume "x \<in> A" thus "Inf A \<le> x" 
      unfolding Inf_graph_def graph_leq_def by auto }

  { assume "\<And>x. x \<in> A \<Longrightarrow> z \<le> x" thus "z \<le> Inf A"
    unfolding Inf_graph_def graph_leq_def by auto }

  { assume "x \<in> A" thus "x \<le> Sup A" 
      unfolding Sup_graph_def graph_leq_def by auto }

  { assume "\<And>x. x \<in> A \<Longrightarrow> x \<le> z" thus "Sup A \<le> z"
    unfolding Sup_graph_def graph_leq_def by auto }
qed

end

lemma in_grplus:
  "has_edge (G + H) p b q = (has_edge G p b q \<or> has_edge H p b q)"
  by (cases G, cases H, auto simp:has_edge_def graph_plus_def)

lemma in_grzero:
  "has_edge 0 p b q = False"
  by (simp add:graph_zero_def has_edge_def)


subsubsection {* Multiplicative Structure *}

instantiation graph :: (type, times) mult_zero
begin

definition
  graph_mult_def [code del]: "G * H = grcomp G H" 

instance proof
  fix a :: "('a, 'b) graph"

  show "0 * a = 0" 
    unfolding graph_mult_def graph_zero_def
    by (cases a) (simp add:grcomp.simps)
  show "a * 0 = 0" 
    unfolding graph_mult_def graph_zero_def
    by (cases a) (simp add:grcomp.simps)
qed

end

instantiation graph :: (type, one) one 
begin

definition
  graph_one_def: "1 = Graph { (x, 1, x) |x. True}"

instance ..

end

lemma in_grcomp:
  "has_edge (G * H) p b q
  = (\<exists>k e e'. has_edge G p e k \<and> has_edge H k e' q \<and> b = e * e')"
  by (cases G, cases H) (auto simp:graph_mult_def has_edge_def image_def)

lemma in_grunit:
  "has_edge 1 p b q = (p = q \<and> b = 1)"
  by (auto simp:graph_one_def has_edge_def)

instance graph :: (type, semigroup_mult) semigroup_mult
proof
  fix G1 G2 G3 :: "('a,'b) graph"
  
  show "G1 * G2 * G3 = G1 * (G2 * G3)"
  proof (rule graph_ext, rule trans)
    fix p J q
    show "has_edge ((G1 * G2) * G3) p J q =
      (\<exists>G i H j I.
      has_edge G1 p G i
      \<and> has_edge G2 i H j
      \<and> has_edge G3 j I q
      \<and> J = (G * H) * I)"
      by (simp only:in_grcomp) blast
    show "\<dots> = has_edge (G1 * (G2 * G3)) p J q"
      by (simp only:in_grcomp mult_assoc) blast
  qed
qed

instance graph :: (type, monoid_mult) "{semiring_1, idem_add}"
proof
  fix a b c :: "('a, 'b) graph"
  
  show "1 * a = a" 
    by (rule graph_ext) (auto simp:in_grcomp in_grunit)
  show "a * 1 = a"
    by (rule graph_ext) (auto simp:in_grcomp in_grunit)

  show "(a + b) * c = a * c + b * c"
    by (rule graph_ext, simp add:in_grcomp in_grplus) blast

  show "a * (b + c) = a * b + a * c"
    by (rule graph_ext, simp add:in_grcomp in_grplus) blast

  show "(0::('a,'b) graph) \<noteq> 1" unfolding graph_zero_def graph_one_def
    by simp

  show "a + a = a" unfolding graph_plus_def by simp
  
qed

instantiation graph :: (type, monoid_mult) star
begin

definition
  graph_star_def: "star (G \<Colon> ('a, 'b) graph) = (SUP n. G ^ n)" 

instance ..

end

lemma graph_leqI:
  assumes "\<And>n e n'. has_edge G n e n' \<Longrightarrow> has_edge H n e n'"
  shows "G \<le> H"
  using assms
  unfolding graph_leq_def has_edge_def
  by auto

lemma in_graph_plusE:
  assumes "has_edge (G + H) n e n'"
  assumes "has_edge G n e n' \<Longrightarrow> P"
  assumes "has_edge H n e n' \<Longrightarrow> P"
  shows P
  using assms
  by (auto simp: in_grplus)

lemma in_graph_compE:
  assumes GH: "has_edge (G * H) n e n'"
  obtains e1 k e2 
  where "has_edge G n e1 k" "has_edge H k e2 n'" "e = e1 * e2"
  using GH
  by (auto simp: in_grcomp)

lemma 
  assumes "x \<in> S k"
  shows "x \<in> (\<Union>k. S k)"
  using assms by blast

lemma graph_union_least:
  assumes "\<And>n. Graph (G n) \<le> C"
  shows "Graph (\<Union>n. G n) \<le> C"
  using assms unfolding graph_leq_def
  by auto

lemma Sup_graph_eq:
  "(SUP n. Graph (G n)) = Graph (\<Union>n. G n)"
proof (rule order_antisym)
  show "(SUP n. Graph (G n)) \<le> Graph (\<Union>n. G n)"
    by  (rule SUP_leI) (auto simp add: graph_leq_def)

  show "Graph (\<Union>n. G n) \<le> (SUP n. Graph (G n))"
  by (rule graph_union_least, rule le_SUPI', rule) 
qed

lemma has_edge_leq: "has_edge G p b q = (Graph {(p,b,q)} \<le> G)"
  unfolding has_edge_def graph_leq_def
  by (cases G) simp


lemma Sup_graph_eq2:
  "(SUP n. G n) = Graph (\<Union>n. dest_graph (G n))"
  using Sup_graph_eq[of "\<lambda>n. dest_graph (G n)", simplified]
  by simp

lemma in_SUP:
  "has_edge (SUP x. Gs x) p b q = (\<exists>x. has_edge (Gs x) p b q)"
  unfolding Sup_graph_eq2 has_edge_leq graph_leq_def
  by simp

instance graph :: (type, monoid_mult) kleene_by_complete_lattice
proof
  fix a b c :: "('a, 'b) graph"

  show "a \<le> b \<longleftrightarrow> a + b = b" unfolding graph_leq_def graph_plus_def
    by (cases a, cases b) auto

  from less_le_not_le show "a < b \<longleftrightarrow> a \<le> b \<and> \<not> b \<le> a" .

  show "a * star b * c = (SUP n. a * b ^ n * c)"
    unfolding graph_star_def
    by (rule graph_ext) (force simp:in_SUP in_grcomp)
qed


lemma in_star: 
  "has_edge (star G) a x b = (\<exists>n. has_edge (G ^ n) a x b)"
  by (auto simp:graph_star_def in_SUP)

lemma tcl_is_SUP:
  "tcl (G::('a::type, 'b::monoid_mult) graph) =
  (SUP n. G ^ (Suc n))"
  unfolding tcl_def 
  using star_cont[of 1 G G]
  by (simp add:power_Suc power_commutes)


lemma in_tcl: 
  "has_edge (tcl G) a x b = (\<exists>n>0. has_edge (G ^ n) a x b)"
  apply (auto simp: tcl_is_SUP in_SUP simp del: power.simps power_Suc)
  apply (rule_tac x = "n - 1" in exI, auto)
  done


subsection {* Infinite Paths *}

types ('n, 'e) ipath = "('n \<times> 'e) sequence"

definition has_ipath :: "('n, 'e) graph \<Rightarrow> ('n, 'e) ipath \<Rightarrow> bool"
where
  "has_ipath G p = 
  (\<forall>i. has_edge G (fst (p i)) (snd (p i)) (fst (p (Suc i))))"


subsection {* Finite Paths *}

types ('n, 'e) fpath = "('n \<times> ('e \<times> 'n) list)"

inductive  has_fpath :: "('n, 'e) graph \<Rightarrow> ('n, 'e) fpath \<Rightarrow> bool" 
  for G :: "('n, 'e) graph"
where
  has_fpath_empty: "has_fpath G (n, [])"
| has_fpath_join: "\<lbrakk>G \<turnstile> n \<leadsto>\<^bsup>e\<^esup> n'; has_fpath G (n', es)\<rbrakk> \<Longrightarrow> has_fpath G (n, (e, n')#es)"

definition 
  "end_node p = 
  (if snd p = [] then fst p else snd (snd p ! (length (snd p) - 1)))"

definition path_nth :: "('n, 'e) fpath \<Rightarrow> nat \<Rightarrow> ('n \<times> 'e \<times> 'n)"
where
  "path_nth p k = (if k = 0 then fst p else snd (snd p ! (k - 1)), snd p ! k)"

lemma endnode_nth:
  assumes "length (snd p) = Suc k"
  shows "end_node p = snd (snd (path_nth p k))"
  using assms unfolding end_node_def path_nth_def
  by auto

lemma path_nth_graph:
  assumes "k < length (snd p)"
  assumes "has_fpath G p"
  shows "(\<lambda>(n,e,n'). has_edge G n e n') (path_nth p k)"
using assms
proof (induct k arbitrary: p)
  case 0 thus ?case 
    unfolding path_nth_def by (auto elim:has_fpath.cases)
next
  case (Suc k p)

  from `has_fpath G p` show ?case 
  proof (rule has_fpath.cases)
    case goal1 with Suc show ?case by simp
  next
    fix n e n' es
    assume st: "p = (n, (e, n') # es)"
       "G \<turnstile> n \<leadsto>\<^bsup>e\<^esup> n'"
       "has_fpath G (n', es)"
    with Suc
    have "(\<lambda>(n, b, a). G \<turnstile> n \<leadsto>\<^bsup>b\<^esup> a) (path_nth (n', es) k)" by simp
    with st show ?thesis by (cases k, auto simp:path_nth_def)
  qed
qed

lemma path_nth_connected:
  assumes "Suc k < length (snd p)"
  shows "fst (path_nth p (Suc k)) = snd (snd (path_nth p k))"
  using assms
  unfolding path_nth_def
  by auto

definition path_loop :: "('n, 'e) fpath \<Rightarrow> ('n, 'e) ipath" ("omega")
where
  "omega p \<equiv> (\<lambda>i. (\<lambda>(n,e,n'). (n,e)) (path_nth p (i mod (length (snd p)))))"

lemma fst_p0: "fst (path_nth p 0) = fst p"
  unfolding path_nth_def by simp

lemma path_loop_connect:
  assumes "fst p = end_node p"
  and "0 < length (snd p)" (is "0 < ?l")
  shows "fst (path_nth p (Suc i mod (length (snd p))))
  = snd (snd (path_nth p (i mod length (snd p))))"
  (is "\<dots> = snd (snd (path_nth p ?k))")
proof -
  from `0 < ?l` have "i mod ?l < ?l" (is "?k < ?l")
    by simp

  show ?thesis 
  proof (cases "Suc ?k < ?l")
    case True
    hence "Suc ?k \<noteq> ?l" by simp
    with path_nth_connected[OF True]
    show ?thesis
      by (simp add:mod_Suc)
  next
    case False 
    with `?k < ?l` have wrap: "Suc ?k = ?l" by simp

    hence "fst (path_nth p (Suc i mod ?l)) = fst (path_nth p 0)" 
      by (simp add: mod_Suc)
    also from fst_p0 have "\<dots> = fst p" .
    also have "\<dots> = end_node p" by fact
    also have "\<dots> = snd (snd (path_nth p ?k))" 
      by (auto simp: endnode_nth wrap)
    finally show ?thesis .
  qed
qed

lemma path_loop_graph:
  assumes "has_fpath G p"
  and loop: "fst p = end_node p"
  and nonempty: "0 < length (snd p)" (is "0 < ?l")
  shows "has_ipath G (omega p)"
proof -
  {
    fix i 
    from `0 < ?l` have "i mod ?l < ?l" (is "?k < ?l")
      by simp
    from this and `has_fpath G p`
    have pk_G: "(\<lambda>(n,e,n'). has_edge G n e n') (path_nth p ?k)"
      by (rule path_nth_graph)

    from path_loop_connect[OF loop nonempty] pk_G
    have "has_edge G (fst (omega p i)) (snd (omega p i)) (fst (omega p (Suc i)))"
      unfolding path_loop_def has_edge_def split_def
      by simp
  }
  then show ?thesis by (auto simp:has_ipath_def)
qed

definition prod :: "('n, 'e::monoid_mult) fpath \<Rightarrow> 'e"
where
  "prod p = foldr (op *) (map fst (snd p)) 1"

lemma prod_simps[simp]:
  "prod (n, []) = 1"
  "prod (n, (e,n')#es) = e * (prod (n',es))"
unfolding prod_def
by simp_all

lemma power_induces_path:
  assumes a: "has_edge (A ^ k) n G m"
  obtains p 
    where "has_fpath A p"
      and "n = fst p" "m = end_node p"
      and "G = prod p"
      and "k = length (snd p)"
  using a
proof (induct k arbitrary:m n G thesis)
  case (0 m n G)
  let ?p = "(n, [])"
  from 0 have "has_fpath A ?p" "m = end_node ?p" "G = prod ?p"
    by (auto simp:in_grunit end_node_def intro:has_fpath.intros)
  thus ?case using 0 by (auto simp:end_node_def)
next
  case (Suc k m n G)
  hence "has_edge (A * A ^ k) n G m" 
    by (simp add:power_Suc power_commutes)
  then obtain G' H j where 
    a_A: "has_edge A n G' j"
    and H_pow: "has_edge (A ^ k) j H m"
    and [simp]: "G = G' * H"
    by (auto simp:in_grcomp) 

  from H_pow and Suc
  obtain p
    where p_path: "has_fpath A p"
    and [simp]: "j = fst p" "m = end_node p" "H = prod p" 
    "k = length (snd p)"
    by blast

  let ?p' = "(n, (G', j)#snd p)"
  from a_A and p_path
  have "has_fpath A ?p'" "m = end_node ?p'" "G = prod ?p'"
    by (auto simp:end_node_def nth.simps intro:has_fpath.intros split:nat.split)
  thus ?case using Suc by auto
qed


subsection {* Sub-Paths *}

definition sub_path :: "('n, 'e) ipath \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('n, 'e) fpath"
("(_\<langle>_,_\<rangle>)")
where
  "p\<langle>i,j\<rangle> =
  (fst (p i), map (\<lambda>k. (snd (p k), fst (p (Suc k)))) [i ..< j])"


lemma sub_path_is_path: 
  assumes ipath: "has_ipath G p"
  assumes l: "i \<le> j"
  shows "has_fpath G (p\<langle>i,j\<rangle>)"
  using l
proof (induct i rule:inc_induct)
  case base show ?case by (auto simp:sub_path_def intro:has_fpath.intros)
next
  case (step i)
  with ipath upt_rec[of i j]
  show ?case
    by (auto simp:sub_path_def has_ipath_def intro:has_fpath.intros)
qed


lemma sub_path_start[simp]:
  "fst (p\<langle>i,j\<rangle>) = fst (p i)"
  by (simp add:sub_path_def)

lemma nth_upto[simp]: "k < j - i \<Longrightarrow> [i ..< j] ! k = i + k"
  by (induct k) auto

lemma sub_path_end[simp]:
  "i < j \<Longrightarrow> end_node (p\<langle>i,j\<rangle>) = fst (p j)"
  by (auto simp:sub_path_def end_node_def)

lemma foldr_map: "foldr f (map g xs) = foldr (f o g) xs"
  by (induct xs) auto

lemma upto_append[simp]:
  assumes "i \<le> j" "j \<le> k"
  shows "[ i ..< j ] @ [j ..< k] = [i ..< k]"
  using assms and upt_add_eq_append[of i j "k - j"]
  by simp

lemma foldr_monoid: "foldr (op *) xs 1 * foldr (op *) ys 1
  = foldr (op *) (xs @ ys) (1::'a::monoid_mult)"
  by (induct xs) (auto simp:mult_assoc)

lemma sub_path_prod:
  assumes "i < j"
  assumes "j < k"
  shows "prod (p\<langle>i,k\<rangle>) = prod (p\<langle>i,j\<rangle>) * prod (p\<langle>j,k\<rangle>)"
  using assms
  unfolding prod_def sub_path_def
  by (simp add:map_compose[symmetric] comp_def)
   (simp only:foldr_monoid map_append[symmetric] upto_append)


lemma path_acgpow_aux:
  assumes "length es = l"
  assumes "has_fpath G (n,es)"
  shows "has_edge (G ^ l) n (prod (n,es)) (end_node (n,es))"
using assms
proof (induct l arbitrary:n es)
  case 0 thus ?case
    by (simp add:in_grunit end_node_def) 
next
  case (Suc l n es)
  hence "es \<noteq> []" by auto
  let ?n' = "snd (hd es)"
  let ?es' = "tl es"
  let ?e = "fst (hd es)"

  from Suc have len: "length ?es' = l" by auto

  from Suc
  have [simp]: "end_node (n, es) = end_node (?n', ?es')"
    by (cases es) (auto simp:end_node_def nth.simps split:nat.split)

  from `has_fpath G (n,es)`
  have "has_fpath G (?n', ?es')"
    by (rule has_fpath.cases) (auto intro:has_fpath.intros)
  with Suc len
  have "has_edge (G ^ l) ?n' (prod (?n', ?es')) (end_node (?n', ?es'))"
    by auto
  moreover
  from `es \<noteq> []`
  have "prod (n, es) = ?e * (prod (?n', ?es'))"
    by (cases es) auto
  moreover
  from `has_fpath G (n,es)` have c:"has_edge G n ?e ?n'"
    by (rule has_fpath.cases) (insert `es \<noteq> []`, auto)

  ultimately
  show ?case
     unfolding power_Suc 
     by (auto simp:in_grcomp)
qed


lemma path_acgpow:
   "has_fpath G p
  \<Longrightarrow> has_edge (G ^ length (snd p)) (fst p) (prod p) (end_node p)"
by (cases p)
   (rule path_acgpow_aux[of "snd p" "length (snd p)" _ "fst p", simplified])


lemma star_paths:
  "has_edge (star G) a x b =
   (\<exists>p. has_fpath G p \<and> a = fst p \<and> b = end_node p \<and> x = prod p)"
proof
  assume "has_edge (star G) a x b"
  then obtain n where pow: "has_edge (G ^ n) a x b"
    by (auto simp:in_star)

  then obtain p where
    "has_fpath G p" "a = fst p" "b = end_node p" "x = prod p"
    by (rule power_induces_path)

  thus "\<exists>p. has_fpath G p \<and> a = fst p \<and> b = end_node p \<and> x = prod p"
    by blast
next
  assume "\<exists>p. has_fpath G p \<and> a = fst p \<and> b = end_node p \<and> x = prod p"
  then obtain p where
    "has_fpath G p" "a = fst p" "b = end_node p" "x = prod p"
    by blast

  hence "has_edge (G ^ length (snd p)) a x b"
    by (auto intro:path_acgpow)

  thus "has_edge (star G) a x b"
    by (auto simp:in_star)
qed


lemma plus_paths:
  "has_edge (tcl G) a x b =
   (\<exists>p. has_fpath G p \<and> a = fst p \<and> b = end_node p \<and> x = prod p \<and> 0 < length (snd p))"
proof
  assume "has_edge (tcl G) a x b"
  
  then obtain n where pow: "has_edge (G ^ n) a x b" and "0 < n"
    by (auto simp:in_tcl)

  from pow obtain p where
    "has_fpath G p" "a = fst p" "b = end_node p" "x = prod p"
    "n = length (snd p)"
    by (rule power_induces_path)

  with `0 < n`
  show "\<exists>p. has_fpath G p \<and> a = fst p \<and> b = end_node p \<and> x = prod p \<and> 0 < length (snd p) "
    by blast
next
  assume "\<exists>p. has_fpath G p \<and> a = fst p \<and> b = end_node p \<and> x = prod p
    \<and> 0 < length (snd p)"
  then obtain p where
    "has_fpath G p" "a = fst p" "b = end_node p" "x = prod p"
    "0 < length (snd p)"
    by blast

  hence "has_edge (G ^ length (snd p)) a x b"
    by (auto intro:path_acgpow)

  with `0 < length (snd p)`
  show "has_edge (tcl G) a x b"
    by (auto simp:in_tcl)
qed


definition
  "contract s p = 
  (\<lambda>i. (fst (p (s i)), prod (p\<langle>s i,s (Suc i)\<rangle>)))"

lemma ipath_contract:
  assumes [simp]: "increasing s"
  assumes ipath: "has_ipath G p"
  shows "has_ipath (tcl G) (contract s p)"
  unfolding has_ipath_def 
proof
  fix i
  let ?p = "p\<langle>s i,s (Suc i)\<rangle>"

  from increasing_strict 
	have "fst (p (s (Suc i))) = end_node ?p" by simp
  moreover
  from increasing_strict[of s i "Suc i"] have "snd ?p \<noteq> []"
    by (simp add:sub_path_def)
  moreover
  from ipath increasing_weak[of s] have "has_fpath G ?p"
    by (rule sub_path_is_path) auto
  ultimately
  show "has_edge (tcl G) 
    (fst (contract s p i)) (snd (contract s p i)) (fst (contract s p (Suc i)))"
    unfolding contract_def plus_paths
    by (intro exI) auto
qed

lemma prod_unfold:
  "i < j \<Longrightarrow> prod (p\<langle>i,j\<rangle>) 
  = snd (p i) * prod (p\<langle>Suc i, j\<rangle>)"
  unfolding prod_def
  by (simp add:sub_path_def upt_rec[of "i" j])


lemma sub_path_loop:
  assumes "0 < k"
  assumes k: "k = length (snd loop)"
  assumes loop: "fst loop = end_node loop"
  shows "(omega loop)\<langle>k * i,k * Suc i\<rangle> = loop" (is "?\<omega> = loop")
proof (rule prod_eqI)
  show "fst ?\<omega> = fst loop"
    by (auto simp:path_loop_def path_nth_def split_def k)

  show "snd ?\<omega> = snd loop"
  proof (rule nth_equalityI[rule_format])
    show leneq: "length (snd ?\<omega>) = length (snd loop)"
      unfolding sub_path_def k by simp

    fix j assume "j < length (snd (?\<omega>))"
    with leneq and k have "j < k" by simp

    have a: "\<And>i. fst (path_nth loop (Suc i mod k))
      = snd (snd (path_nth loop (i mod k)))"
      unfolding k
      apply (rule path_loop_connect[OF loop])
      using `0 < k` and k
      apply auto
      done

    from `j < k` 
    show "snd ?\<omega> ! j = snd loop ! j"
      unfolding sub_path_def
      apply (simp add:path_loop_def split_def add_ac)
      apply (simp add:a k[symmetric])
      apply (simp add:path_nth_def)
      done
  qed
qed

end
