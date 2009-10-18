(*  Title:      HOL/Library/SCT_Theorem.thy
    Author:     Alexander Krauss, TU Muenchen
*)

header "Proof of the Size-Change Principle"

theory Correctness
imports Main Ramsey Misc_Tools Criterion
begin

subsection {* Auxiliary definitions *}

definition is_thread :: "nat \<Rightarrow> 'a sequence \<Rightarrow> ('a, 'a scg) ipath \<Rightarrow> bool"
where
  "is_thread n \<theta> p = (\<forall>i\<ge>n. eqlat p \<theta> i)"

definition is_fthread :: 
  "'a sequence \<Rightarrow> ('a, 'a scg) ipath \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "is_fthread \<theta> mp i j = (\<forall>k\<in>{i..<j}. eqlat mp \<theta> k)"

definition is_desc_fthread ::
  "'a sequence \<Rightarrow> ('a, 'a scg) ipath \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "is_desc_fthread \<theta> mp i j = 
  (is_fthread \<theta> mp i j \<and>
  (\<exists>k\<in>{i..<j}. descat mp \<theta> k))"

definition
  "has_fth p i j n m = 
  (\<exists>\<theta>. is_fthread \<theta> p i j \<and> \<theta> i = n \<and> \<theta> j = m)"

definition
  "has_desc_fth p i j n m = 
  (\<exists>\<theta>. is_desc_fthread \<theta> p i j \<and> \<theta> i = n \<and> \<theta> j = m)"


subsection {* Everything is finite *}

lemma finite_range:
  fixes f :: "nat \<Rightarrow> 'a"
  assumes fin: "finite (range f)"
  shows "\<exists>x. \<exists>\<^sub>\<infinity>i. f i = x"
proof (rule classical)
  assume "\<not>(\<exists>x. \<exists>\<^sub>\<infinity>i. f i = x)"
  hence "\<forall>x. \<exists>j. \<forall>i>j. f i \<noteq> x"
    unfolding INFM_nat by blast
  with choice
  have "\<exists>j. \<forall>x. \<forall>i>(j x). f i \<noteq> x" .
  then obtain j where 
    neq: "\<And>x i. j x < i \<Longrightarrow> f i \<noteq> x" by blast

  from fin have "finite (range (j o f))" 
    by (auto simp:comp_def range_composition)
  with finite_nat_bounded
  obtain m where "range (j o f) \<subseteq> {..<m}" by blast
  hence "j (f m) < m" unfolding comp_def by auto

  with neq[of "f m" m] show ?thesis by blast
qed

lemma finite_range_ignore_prefix:
  fixes f :: "nat \<Rightarrow> 'a"
  assumes fA: "finite A"
  assumes inA: "\<forall>x\<ge>n. f x \<in> A"
  shows "finite (range f)"
proof -
  have a: "UNIV = {0 ..< (n::nat)} \<union> { x. n \<le> x }" by auto
  have b: "range f = f ` {0 ..< n} \<union> f ` { x. n \<le> x }" 
    (is "\<dots> = ?A \<union> ?B")
    by (unfold a) (simp add:image_Un)
  
  have "finite ?A" by (rule finite_imageI) simp
  moreover
  from inA have "?B \<subseteq> A" by auto
  from this fA have "finite ?B" by (rule finite_subset)
  ultimately show ?thesis using b by simp
qed




definition 
  "finite_graph G = finite (dest_graph G)"
definition 
  "all_finite G = (\<forall>n H m. has_edge G n H m \<longrightarrow> finite_graph H)"
definition
  "finite_acg A = (finite_graph A \<and> all_finite A)"
definition 
  "nodes G = fst ` dest_graph G \<union> snd ` snd ` dest_graph G"
definition 
  "edges G = fst ` snd ` dest_graph G"
definition 
  "smallnodes G = \<Union>(nodes ` edges G)"

lemma thread_image_nodes:
  assumes th: "is_thread n \<theta> p"
  shows "\<forall>i\<ge>n. \<theta> i \<in> nodes (snd (p i))"
using prems
unfolding is_thread_def has_edge_def nodes_def
by force

lemma finite_nodes: "finite_graph G \<Longrightarrow> finite (nodes G)"
  unfolding finite_graph_def nodes_def
  by auto

lemma nodes_subgraph: "A \<le> B \<Longrightarrow> nodes A \<subseteq> nodes B"
  unfolding graph_leq_def nodes_def
  by auto

lemma finite_edges: "finite_graph G \<Longrightarrow> finite (edges G)"
  unfolding finite_graph_def edges_def
  by auto

lemma edges_sum[simp]: "edges (A + B) = edges A \<union> edges B"
  unfolding edges_def graph_plus_def
  by auto

lemma nodes_sum[simp]: "nodes (A + B) = nodes A \<union> nodes B"
  unfolding nodes_def graph_plus_def
  by auto

lemma finite_acg_subset:
  "A \<le> B \<Longrightarrow> finite_acg B \<Longrightarrow> finite_acg A"
  unfolding finite_acg_def finite_graph_def all_finite_def
  has_edge_def graph_leq_def
  by (auto elim:finite_subset)

lemma scg_finite: 
  fixes G :: "'a scg"
  assumes fin: "finite (nodes G)"
  shows "finite_graph G"
  unfolding finite_graph_def
proof (rule finite_subset)
  show "dest_graph G \<subseteq> nodes G \<times> UNIV \<times> nodes G" (is "_ \<subseteq> ?P")
    unfolding nodes_def
    by force
  show "finite ?P"
    by (intro finite_cartesian_product fin finite)
qed

lemma smallnodes_sum[simp]: 
  "smallnodes (A + B) = smallnodes A \<union> smallnodes B"
  unfolding smallnodes_def 
  by auto

lemma in_smallnodes:
  fixes A :: "'a acg"
  assumes e: "has_edge A x G y"
  shows "nodes G \<subseteq> smallnodes A"
proof -
  have "fst (snd (x, G, y)) \<in> fst ` snd  ` dest_graph A"
    unfolding has_edge_def
    by (rule imageI)+ (rule e[unfolded has_edge_def])
  then have "G \<in> edges A" 
    unfolding edges_def by simp
  thus ?thesis
    unfolding smallnodes_def
    by blast
qed

lemma finite_smallnodes:
  assumes fA: "finite_acg A"
  shows "finite (smallnodes A)"
  unfolding smallnodes_def edges_def
proof 
  from fA
  show "finite (nodes ` fst ` snd ` dest_graph A)"
    unfolding finite_acg_def finite_graph_def
    by simp
  
  fix M assume "M \<in> nodes ` fst ` snd ` dest_graph A"
  then obtain n G m  
    where M: "M = nodes G" and nGm: "(n,G,m) \<in> dest_graph A"
    by auto
  
  from fA
  have "all_finite A" unfolding finite_acg_def by simp
  with nGm have "finite_graph G" 
    unfolding all_finite_def has_edge_def by auto
  with finite_nodes 
  show "finite M" 
    unfolding finite_graph_def M .
qed

lemma nodes_tcl:
  "nodes (tcl A) = nodes A"
proof
  show "nodes A \<subseteq> nodes (tcl A)"
    apply (rule nodes_subgraph)
    by (subst tcl_unfold_right) simp

  show "nodes (tcl A) \<subseteq> nodes A"
  proof 
    fix x assume "x \<in> nodes (tcl A)"
    then obtain z G y
      where z: "z \<in> dest_graph (tcl A)"
      and dis: "z = (x, G, y) \<or> z = (y, G, x)"
      unfolding nodes_def
      by auto force+

    from dis
    show "x \<in> nodes A"
    proof
      assume "z = (x, G, y)"
      with z have "has_edge (tcl A) x G y" unfolding has_edge_def by simp
      then obtain n where "n > 0 " and An: "has_edge (A ^ n) x G y"
        unfolding in_tcl by auto
      then obtain n' where "n = Suc n'" by (cases n, auto)
      hence "A ^ n = A * A ^ n'" by (simp add:power_Suc)
      with An obtain e k 
        where "has_edge A x e k" by (auto simp:in_grcomp)
      thus "x \<in> nodes A" unfolding has_edge_def nodes_def 
        by force
    next
      assume "z = (y, G, x)"
      with z have "has_edge (tcl A) y G x" unfolding has_edge_def by simp
      then obtain n where "n > 0 " and An: "has_edge (A ^ n) y G x"
        unfolding in_tcl by auto
      then obtain n' where "n = Suc n'" by (cases n, auto)
      hence "A ^ n = A ^ n' * A" by (simp add:power_Suc power_commutes)
      with An obtain e k 
        where "has_edge A k e x" by (auto simp:in_grcomp)
      thus "x \<in> nodes A" unfolding has_edge_def nodes_def 
        by force
    qed
  qed
qed

lemma smallnodes_tcl: 
  fixes A :: "'a acg"
  shows "smallnodes (tcl A) = smallnodes A"
proof (intro equalityI subsetI)
  fix n assume "n \<in> smallnodes (tcl A)"
  then obtain x G y where edge: "has_edge (tcl A) x G y" 
    and "n \<in> nodes G"
    unfolding smallnodes_def edges_def has_edge_def 
    by auto
  
  from `n \<in> nodes G`
  have "n \<in> fst ` dest_graph G \<or> n \<in> snd ` snd ` dest_graph G"
    (is "?A \<or> ?B")
    unfolding nodes_def by blast
  thus "n \<in> smallnodes A"
  proof
    assume ?A
    then obtain m e where A: "has_edge G n e m"
      unfolding has_edge_def by auto

    have "tcl A = A * star A"
      unfolding tcl_def
      by (simp add: star_simulation[of A A A, simplified])

    with edge
    have "has_edge (A * star A) x G y" by simp
    then obtain H H' z
      where AH: "has_edge A x H z" and G: "G = H * H'"
      by (auto simp:in_grcomp)
    from A
    obtain m' e' where "has_edge H n e' m'"
      by (auto simp:G in_grcomp)
    hence "n \<in> nodes H" unfolding nodes_def has_edge_def 
      by force
    with in_smallnodes[OF AH] show "n \<in> smallnodes A" ..
  next
    assume ?B
    then obtain m e where B: "has_edge G m e n"
      unfolding has_edge_def by auto

    with edge
    have "has_edge (star A * A) x G y" by (simp add:tcl_def)
    then obtain H H' z
      where AH': "has_edge A z H' y" and G: "G = H * H'"
      by (auto simp:in_grcomp simp del: star_slide2)
    from B
    obtain m' e' where "has_edge H' m' e' n"
      by (auto simp:G in_grcomp)
    hence "n \<in> nodes H'" unfolding nodes_def has_edge_def 
      by force
    with in_smallnodes[OF AH'] show "n \<in> smallnodes A" ..
  qed
next
  fix x assume "x \<in> smallnodes A"
  then show "x \<in> smallnodes (tcl A)"
    by (subst tcl_unfold_right) simp
qed

lemma finite_nodegraphs:
  assumes F: "finite F"
  shows "finite { G::'a scg. nodes G \<subseteq> F }" (is "finite ?P")
proof (rule finite_subset)
  show "?P \<subseteq> Graph ` (Pow (F \<times> UNIV \<times> F))" (is "?P \<subseteq> ?Q")
  proof
    fix x assume xP: "x \<in> ?P"
    obtain S where x[simp]: "x = Graph S"
      by (cases x) auto
    from xP
    show "x \<in> ?Q"
      apply (simp add:nodes_def)
      apply (rule imageI)
      apply (rule PowI)
      apply force
      done
  qed
  show "finite ?Q"
    by (auto intro:finite_imageI finite_cartesian_product F finite)
qed

lemma finite_graphI:
  fixes A :: "'a acg"
  assumes fin: "finite (nodes A)" "finite (smallnodes A)"
  shows "finite_graph A"
proof -
  obtain S where A[simp]: "A = Graph S"
    by (cases A) auto

  have "finite S" 
  proof (rule finite_subset)
    show "S \<subseteq> nodes A \<times> { G::'a scg. nodes G \<subseteq> smallnodes A } \<times> nodes A"
      (is "S \<subseteq> ?T")
    proof
      fix x assume xS: "x \<in> S"
      obtain a b c where x[simp]: "x = (a, b, c)"
        by (cases x) auto

      then have edg: "has_edge A a b c"
        unfolding has_edge_def using xS
        by simp

      hence "a \<in> nodes A" "c \<in> nodes A"
        unfolding nodes_def has_edge_def by force+
      moreover
      from edg have "nodes b \<subseteq> smallnodes A" by (rule in_smallnodes)
      hence "b \<in> { G :: 'a scg. nodes G \<subseteq> smallnodes A }" by simp
      ultimately show "x \<in> ?T" by simp
    qed

    show "finite ?T"
      by (intro finite_cartesian_product fin finite_nodegraphs)
  qed
  thus ?thesis
    unfolding finite_graph_def by simp
qed


lemma smallnodes_allfinite:
  fixes A :: "'a acg"
  assumes fin: "finite (smallnodes A)"
  shows "all_finite A"
  unfolding all_finite_def
proof (intro allI impI)
  fix n H m assume "has_edge A n H m"
  then have "nodes H \<subseteq> smallnodes A"
    by (rule in_smallnodes)
  then have "finite (nodes H)" 
    by (rule finite_subset) (rule fin)
  thus "finite_graph H" by (rule scg_finite)
qed

lemma finite_tcl: 
  fixes A :: "'a acg"
  shows "finite_acg (tcl A) \<longleftrightarrow> finite_acg A"
proof
  assume f: "finite_acg A"
  from f have g: "finite_graph A" and "all_finite A"
    unfolding finite_acg_def by auto

  from g have "finite (nodes A)" by (rule finite_nodes)
  then have "finite (nodes (tcl A))" unfolding nodes_tcl .
  moreover
  from f have "finite (smallnodes A)" by (rule finite_smallnodes)
  then have fs: "finite (smallnodes (tcl A))" unfolding smallnodes_tcl .
  ultimately
  have "finite_graph (tcl A)" by (rule finite_graphI)

  moreover from fs have "all_finite (tcl A)"
    by (rule smallnodes_allfinite)
  ultimately show "finite_acg (tcl A)" unfolding finite_acg_def ..
next
  assume a: "finite_acg (tcl A)"
  have "A \<le> tcl A" by (rule less_tcl)
  thus "finite_acg A" using a
    by (rule finite_acg_subset)
qed

lemma finite_acg_empty: "finite_acg (Graph {})"
  unfolding finite_acg_def finite_graph_def all_finite_def
  has_edge_def
  by simp

lemma finite_acg_ins: 
  assumes fA: "finite_acg (Graph A)"
  assumes fG: "finite G"
  shows "finite_acg (Graph (insert (a, Graph G, b) A))" 
  using fA fG
  unfolding finite_acg_def finite_graph_def all_finite_def
  has_edge_def
  by auto

lemmas finite_acg_simps = finite_acg_empty finite_acg_ins finite_graph_def

subsection {* Contraction and more *}

abbreviation 
  "pdesc P == (fst P, prod P, end_node P)"

lemma pdesc_acgplus: 
  assumes "has_ipath \<A> p"
  and "i < j"
  shows "has_edge (tcl \<A>) (fst (p\<langle>i,j\<rangle>)) (prod (p\<langle>i,j\<rangle>)) (end_node (p\<langle>i,j\<rangle>))"
  unfolding plus_paths
  apply (rule exI)
  apply (insert prems)  
  by (auto intro:sub_path_is_path[of "\<A>" p i j] simp:sub_path_def)


lemma combine_fthreads: 
  assumes range: "i < j" "j \<le> k"
  shows 
  "has_fth p i k m r =
  (\<exists>n. has_fth p i j m n \<and> has_fth p j k n r)" (is "?L = ?R")
proof (intro iffI)
  assume "?L"
  then obtain \<theta>
    where "is_fthread \<theta> p i k" 
    and [simp]: "\<theta> i = m" "\<theta> k = r"
    by (auto simp:has_fth_def)

  with range
  have "is_fthread \<theta> p i j" and "is_fthread \<theta> p j k"
    by (auto simp:is_fthread_def)
  hence "has_fth p i j m (\<theta> j)" and "has_fth p j k (\<theta> j) r"
    by (auto simp:has_fth_def)
  thus "?R" by auto
next
  assume "?R"
  then obtain n \<theta>1 \<theta>2
    where ths: "is_fthread \<theta>1 p i j" "is_fthread \<theta>2 p j k"
    and [simp]: "\<theta>1 i = m" "\<theta>1 j = n" "\<theta>2 j = n" "\<theta>2 k = r"
    by (auto simp:has_fth_def)

  let ?\<theta> = "(\<lambda>i. if i < j then \<theta>1 i else \<theta>2 i)"
  have "is_fthread ?\<theta> p i k"
    unfolding is_fthread_def
  proof
    fix l assume range: "l \<in> {i..<k}"
    
    show "eqlat p ?\<theta> l"
    proof (cases rule:three_cases)
      assume "Suc l < j"
      with ths range show ?thesis 
        unfolding is_fthread_def Ball_def
        by simp
    next
      assume "Suc l = j"
      hence "l < j" "\<theta>2 (Suc l) = \<theta>1 (Suc l)" by auto
      with ths range show ?thesis 
        unfolding is_fthread_def Ball_def
        by simp
    next
      assume "j \<le> l"
      with ths range show ?thesis 
        unfolding is_fthread_def Ball_def
        by simp
    qed arith
  qed
  moreover 
  have "?\<theta> i = m" "?\<theta> k = r" using range by auto
  ultimately show "has_fth p i k m r" 
    by (auto simp:has_fth_def)
qed 


lemma desc_is_fthread:
  "is_desc_fthread \<theta> p i k \<Longrightarrow> is_fthread \<theta> p i k"
  unfolding is_desc_fthread_def
  by simp


lemma combine_dfthreads: 
  assumes range: "i < j" "j \<le> k"
  shows 
  "has_desc_fth p i k m r =
  (\<exists>n. (has_desc_fth p i j m n \<and> has_fth p j k n r)
  \<or> (has_fth p i j m n \<and> has_desc_fth p j k n r))" (is "?L = ?R")
proof 
  assume "?L"
  then obtain \<theta>
    where desc: "is_desc_fthread \<theta> p i k" 
    and [simp]: "\<theta> i = m" "\<theta> k = r"
    by (auto simp:has_desc_fth_def)

  hence "is_fthread \<theta> p i k"
    by (simp add: desc_is_fthread)
  with range have fths: "is_fthread \<theta> p i j" "is_fthread \<theta> p j k"
    unfolding is_fthread_def
    by auto
  hence hfths: "has_fth p i j m (\<theta> j)" "has_fth p j k (\<theta> j) r"
    by (auto simp:has_fth_def)

  from desc obtain l 
    where "i \<le> l" "l < k"
    and "descat p \<theta> l"
    by (auto simp:is_desc_fthread_def)

  with fths
  have "is_desc_fthread \<theta> p i j \<or> is_desc_fthread \<theta> p j k"
    unfolding is_desc_fthread_def
    by (cases "l < j") auto
  hence "has_desc_fth p i j m (\<theta> j) \<or> has_desc_fth p j k (\<theta> j) r"
    by (auto simp:has_desc_fth_def)
  with hfths show ?R
    by auto
next
  assume "?R"
  then obtain n \<theta>1 \<theta>2
    where "(is_desc_fthread \<theta>1 p i j \<and> is_fthread \<theta>2 p j k)
    \<or> (is_fthread \<theta>1 p i j \<and> is_desc_fthread \<theta>2 p j k)"
    and [simp]: "\<theta>1 i = m" "\<theta>1 j = n" "\<theta>2 j = n" "\<theta>2 k = r"
    by (auto simp:has_fth_def has_desc_fth_def)

  hence ths2: "is_fthread \<theta>1 p i j" "is_fthread \<theta>2 p j k"
    and dths: "is_desc_fthread \<theta>1 p i j \<or> is_desc_fthread \<theta>2 p j k"
    by (auto simp:desc_is_fthread)

  let ?\<theta> = "(\<lambda>i. if i < j then \<theta>1 i else \<theta>2 i)"
  have "is_fthread ?\<theta> p i k"
    unfolding is_fthread_def
  proof
    fix l assume range: "l \<in> {i..<k}"
    
    show "eqlat p ?\<theta> l"
    proof (cases rule:three_cases)
      assume "Suc l < j"
      with ths2 range show ?thesis 
        unfolding is_fthread_def Ball_def
        by simp
    next
      assume "Suc l = j"
      hence "l < j" "\<theta>2 (Suc l) = \<theta>1 (Suc l)" by auto
      with ths2 range show ?thesis 
        unfolding is_fthread_def Ball_def
        by simp
    next
      assume "j \<le> l"
      with ths2 range show ?thesis 
        unfolding is_fthread_def Ball_def
        by simp
    qed arith
  qed
  moreover
  from dths
  have "\<exists>l. i \<le> l \<and> l < k \<and> descat p ?\<theta> l"
  proof
    assume "is_desc_fthread \<theta>1 p i j"

    then obtain l where range: "i \<le> l" "l < j" and "descat p \<theta>1 l"
      unfolding is_desc_fthread_def Bex_def by auto
    hence "descat p ?\<theta> l" 
      by (cases "Suc l = j", auto)
    with `j \<le> k` and range show ?thesis 
      by (rule_tac x="l" in exI, auto)
  next
    assume "is_desc_fthread \<theta>2 p j k"
    then obtain l where range: "j \<le> l" "l < k" and "descat p \<theta>2 l"
      unfolding is_desc_fthread_def Bex_def by auto
    with `i < j` have "descat p ?\<theta> l" "i \<le> l"
      by auto
    with range show ?thesis 
      by (rule_tac x="l" in exI, auto)
  qed
  ultimately have "is_desc_fthread ?\<theta> p i k"
    by (simp add: is_desc_fthread_def Bex_def)

  moreover 
  have "?\<theta> i = m" "?\<theta> k = r" using range by auto

  ultimately show "has_desc_fth p i k m r" 
    by (auto simp:has_desc_fth_def)
qed 

    

lemma fth_single:
  "has_fth p i (Suc i) m n = eql (snd (p i)) m n" (is "?L = ?R")
proof 
  assume "?L" thus "?R"
    unfolding is_fthread_def Ball_def has_fth_def
    by auto
next
  let ?\<theta> = "\<lambda>k. if k = i then m else n"
  assume edge: "?R"
  hence "is_fthread ?\<theta> p i (Suc i) \<and> ?\<theta> i = m \<and> ?\<theta> (Suc i) = n"
    unfolding is_fthread_def Ball_def
    by auto

  thus "?L"
    unfolding has_fth_def 
    by auto
qed

lemma desc_fth_single:
  "has_desc_fth p i (Suc i) m n = 
  dsc (snd (p i)) m n" (is "?L = ?R")
proof 
  assume "?L" thus "?R"
    unfolding is_desc_fthread_def has_desc_fth_def is_fthread_def
    Bex_def 
    by (elim exE conjE) (case_tac "k = i", auto)
next
  let ?\<theta> = "\<lambda>k. if k = i then m else n"
  assume edge: "?R"
  hence "is_desc_fthread ?\<theta> p i (Suc i) \<and> ?\<theta> i = m \<and> ?\<theta> (Suc i) = n"
    unfolding is_desc_fthread_def is_fthread_def Ball_def Bex_def
    by auto
  thus "?L"
    unfolding has_desc_fth_def 
    by auto
qed

lemma mk_eql: "(G \<turnstile> m \<leadsto>\<^bsup>e\<^esup> n) \<Longrightarrow> eql G m n"
  by (cases e, auto)

lemma eql_scgcomp:
  "eql (G * H) m r =
  (\<exists>n. eql G m n \<and> eql H n r)" (is "?L = ?R")
proof
  show "?L \<Longrightarrow> ?R"
    by (auto simp:in_grcomp intro!:mk_eql)

  assume "?R"
  then obtain n where l: "eql G m n" and r:"eql H n r" by auto
  thus ?L
    by (cases "dsc G m n") (auto simp:in_grcomp mult_sedge_def)
qed

lemma desc_scgcomp:
  "dsc (G * H) m r =
  (\<exists>n. (dsc G m n \<and> eql H n r) \<or> (eqp G m n \<and> dsc H n r))" (is "?L = ?R")
proof
  show "?R \<Longrightarrow> ?L" by (auto simp:in_grcomp mult_sedge_def)

  assume "?L"
  thus ?R
    by (auto simp:in_grcomp mult_sedge_def)
  (case_tac "e", auto, case_tac "e'", auto)
qed


lemma has_fth_unfold:
  assumes "i < j"
  shows "has_fth p i j m n = 
    (\<exists>r. has_fth p i (Suc i) m r \<and> has_fth p (Suc i) j r n)"
    by (rule combine_fthreads) (insert `i < j`, auto)

lemma has_dfth_unfold:
  assumes range: "i < j"
  shows 
  "has_desc_fth p i j m r =
  (\<exists>n. (has_desc_fth p i (Suc i) m n \<and> has_fth p (Suc i) j n r)
  \<or> (has_fth p i (Suc i) m n \<and> has_desc_fth p (Suc i) j n r))"
  by (rule combine_dfthreads) (insert `i < j`, auto)


lemma Lemma7a:
 "i \<le> j \<Longrightarrow> has_fth p i j m n = eql (prod (p\<langle>i,j\<rangle>)) m n"
proof (induct i arbitrary: m rule:inc_induct)
  case base show ?case
    unfolding has_fth_def is_fthread_def sub_path_def
    by (auto simp:in_grunit one_sedge_def)
next
  case (step i)
  note IH = `\<And>m. has_fth p (Suc i) j m n = 
  eql (prod (p\<langle>Suc i,j\<rangle>)) m n`

  have "has_fth p i j m n 
    = (\<exists>r. has_fth p i (Suc i) m r \<and> has_fth p (Suc i) j r n)"
    by (rule has_fth_unfold[OF `i < j`])
  also have "\<dots> = (\<exists>r. has_fth p i (Suc i) m r 
    \<and> eql (prod (p\<langle>Suc i,j\<rangle>)) r n)"
    by (simp only:IH)
  also have "\<dots> = (\<exists>r. eql (snd (p i)) m r
    \<and> eql (prod (p\<langle>Suc i,j\<rangle>)) r n)"
    by (simp only:fth_single)
  also have "\<dots> = eql (snd (p i) * prod (p\<langle>Suc i,j\<rangle>)) m n"
    by (simp only:eql_scgcomp)
  also have "\<dots> = eql (prod (p\<langle>i,j\<rangle>)) m n"
    by (simp only:prod_unfold[OF `i < j`])
  finally show ?case .
qed


lemma Lemma7b:
assumes "i \<le> j"
shows
  "has_desc_fth p i j m n = 
  dsc (prod (p\<langle>i,j\<rangle>)) m n"
using prems
proof (induct i arbitrary: m rule:inc_induct)
  case base show ?case
    unfolding has_desc_fth_def is_desc_fthread_def sub_path_def 
    by (auto simp:in_grunit one_sedge_def)
next
  case (step i)
  thus ?case 
    by (simp only:prod_unfold desc_scgcomp desc_fth_single
    has_dfth_unfold fth_single Lemma7a) auto
qed


lemma descat_contract:
  assumes [simp]: "increasing s"
  shows
  "descat (contract s p) \<theta> i = 
  has_desc_fth p (s i) (s (Suc i)) (\<theta> i) (\<theta> (Suc i))"
  by (simp add:Lemma7b increasing_weak contract_def)

lemma eqlat_contract:
  assumes [simp]: "increasing s"
  shows
  "eqlat (contract s p) \<theta> i = 
  has_fth p (s i) (s (Suc i)) (\<theta> i) (\<theta> (Suc i))"
  by (auto simp:Lemma7a increasing_weak contract_def)


subsubsection {* Connecting threads *}

definition
  "connect s \<theta>s = (\<lambda>k. \<theta>s (section_of s k) k)"


lemma next_in_range:
  assumes [simp]: "increasing s"
  assumes a: "k \<in> section s i"
  shows "(Suc k \<in> section s i) \<or> (Suc k \<in> section s (Suc i))"
proof -
  from a have "k < s (Suc i)" by simp
  
  hence "Suc k < s (Suc i) \<or> Suc k = s (Suc i)" by arith
  thus ?thesis
  proof
    assume "Suc k < s (Suc i)"
    with a have "Suc k \<in> section s i" by simp
    thus ?thesis ..
  next
    assume eq: "Suc k = s (Suc i)"
    with increasing_strict have "Suc k < s (Suc (Suc i))" by simp
    with eq have "Suc k \<in> section s (Suc i)" by simp
    thus ?thesis ..
  qed
qed


lemma connect_threads:
  assumes [simp]: "increasing s"
  assumes connected: "\<theta>s i (s (Suc i)) = \<theta>s (Suc i) (s (Suc i))"
  assumes fth: "is_fthread (\<theta>s i) p (s i) (s (Suc i))"

  shows
  "is_fthread (connect s \<theta>s) p (s i) (s (Suc i))"
  unfolding is_fthread_def
proof 
  fix k assume krng: "k \<in> section s i"

  with fth have eqlat: "eqlat p (\<theta>s i) k" 
    unfolding is_fthread_def by simp

  from krng and next_in_range 
  have "(Suc k \<in> section s i) \<or> (Suc k \<in> section s (Suc i))" 
    by simp
  thus "eqlat p (connect s \<theta>s) k"
  proof
    assume "Suc k \<in> section s i"
    with krng eqlat show ?thesis
      unfolding connect_def
      by (simp only:section_of_known `increasing s`)
  next
    assume skrng: "Suc k \<in> section s (Suc i)"
    with krng have "Suc k = s (Suc i)" by auto

    with krng skrng eqlat show ?thesis
      unfolding connect_def
      by (simp only:section_of_known connected[symmetric] `increasing s`)
  qed
qed


lemma connect_dthreads:
  assumes inc[simp]: "increasing s"
  assumes connected: "\<theta>s i (s (Suc i)) = \<theta>s (Suc i) (s (Suc i))"
  assumes fth: "is_desc_fthread (\<theta>s i) p (s i) (s (Suc i))"

  shows
  "is_desc_fthread (connect s \<theta>s) p (s i) (s (Suc i))"
  unfolding is_desc_fthread_def
proof 
  show "is_fthread (connect s \<theta>s) p (s i) (s (Suc i))"
    apply (rule connect_threads)
    apply (insert fth)
    by (auto simp:connected is_desc_fthread_def)

  from fth
  obtain k where dsc: "descat p (\<theta>s i) k" and krng: "k \<in> section s i"
    unfolding is_desc_fthread_def by blast
  
  from krng and next_in_range 
  have "(Suc k \<in> section s i) \<or> (Suc k \<in> section s (Suc i))" 
    by simp
  hence "descat p (connect s \<theta>s) k"
  proof
    assume "Suc k \<in> section s i"
    with krng dsc show ?thesis unfolding connect_def
      by (simp only:section_of_known inc)
  next
    assume skrng: "Suc k \<in> section s (Suc i)"
    with krng have "Suc k = s (Suc i)" by auto

    with krng skrng dsc show ?thesis unfolding connect_def
      by (simp only:section_of_known connected[symmetric] inc)
  qed
  with krng show "\<exists>k\<in>section s i. descat p (connect s \<theta>s) k" ..
qed

lemma mk_inf_thread:
  assumes [simp]: "increasing s"
  assumes fths: "\<And>i. i > n \<Longrightarrow> is_fthread \<theta> p (s i) (s (Suc i))"
  shows "is_thread (s (Suc n)) \<theta> p"
  unfolding is_thread_def 
proof (intro allI impI)
  fix j assume st: "s (Suc n) \<le> j"

  let ?k = "section_of s j"
  from in_section_of st
  have rs: "j \<in> section s ?k" by simp

  with st have "s (Suc n) < s (Suc ?k)" by simp
  with increasing_bij have "n < ?k" by simp
  with rs and fths[of ?k]
  show "eqlat p \<theta> j" by (simp add:is_fthread_def)
qed


lemma mk_inf_desc_thread:
  assumes [simp]: "increasing s"
  assumes fths: "\<And>i. i > n \<Longrightarrow> is_fthread \<theta> p (s i) (s (Suc i))"
  assumes fdths: "\<exists>\<^sub>\<infinity>i. is_desc_fthread \<theta> p (s i) (s (Suc i))"
  shows "is_desc_thread \<theta> p"
  unfolding is_desc_thread_def 
proof (intro exI conjI)

  from mk_inf_thread[of s n \<theta> p] fths
  show "\<forall>i\<ge>s (Suc n). eqlat p \<theta> i" 
    by (fold is_thread_def) simp

  show "\<exists>\<^sub>\<infinity>l. descat p \<theta> l"
    unfolding INFM_nat
  proof
    fix i 
    
    let ?k = "section_of s i"
    from fdths obtain j
      where "?k < j" "is_desc_fthread \<theta> p (s j) (s (Suc j))"
      unfolding INFM_nat by auto
    then obtain l where "s j \<le> l" and desc: "descat p \<theta> l"
      unfolding is_desc_fthread_def
      by auto

    have "i < s (Suc ?k)" by (rule section_of2) simp
    also have "\<dots> \<le> s j"
      by (rule increasing_weak [OF `increasing s`]) (insert `?k < j`, arith)
    also note `\<dots> \<le> l`
    finally have "i < l" .
    with desc
    show "\<exists>l. i < l \<and> descat p \<theta> l" by blast
  qed
qed


lemma desc_ex_choice:
  assumes A: "((\<exists>n.\<forall>i\<ge>n. \<exists>x. P x i) \<and> (\<exists>\<^sub>\<infinity>i. \<exists>x. Q x i))"
  and imp: "\<And>x i. Q x i \<Longrightarrow> P x i"
  shows "\<exists>xs. ((\<exists>n.\<forall>i\<ge>n. P (xs i) i) \<and> (\<exists>\<^sub>\<infinity>i. Q (xs i) i))"
  (is "\<exists>xs. ?Ps xs \<and> ?Qs xs")
proof
  let ?w = "\<lambda>i. (if (\<exists>x. Q x i) then (SOME x. Q x i)
                                 else (SOME x. P x i))"

  from A
  obtain n where P: "\<And>i. n \<le> i \<Longrightarrow> \<exists>x. P x i"
    by auto
  {
    fix i::'a assume "n \<le> i"

    have "P (?w i) i"
    proof (cases "\<exists>x. Q x i")
      case True
      hence "Q (?w i) i" by (auto intro:someI)
      with imp show "P (?w i) i" .
    next
      case False
      with P[OF `n \<le> i`] show "P (?w i) i" 
        by (auto intro:someI)
    qed
  }

  hence "?Ps ?w" by (rule_tac x=n in exI) auto

  moreover
  from A have "\<exists>\<^sub>\<infinity>i. (\<exists>x. Q x i)" ..
  hence "?Qs ?w" by (rule INFM_mono) (auto intro:someI)
  ultimately
  show "?Ps ?w \<and> ?Qs ?w" ..
qed



lemma dthreads_join:
  assumes [simp]: "increasing s"
  assumes dthread: "is_desc_thread \<theta> (contract s p)"
  shows "\<exists>\<theta>s. desc (\<lambda>i. is_fthread (\<theta>s i) p (s i) (s (Suc i))
                           \<and> \<theta>s i (s i) = \<theta> i 
                           \<and> \<theta>s i (s (Suc i)) = \<theta> (Suc i))
                   (\<lambda>i. is_desc_fthread (\<theta>s i) p (s i) (s (Suc i))
                           \<and> \<theta>s i (s i) = \<theta> i 
                           \<and> \<theta>s i (s (Suc i)) = \<theta> (Suc i))"
    apply (rule desc_ex_choice)
    apply (insert dthread)
    apply (simp only:is_desc_thread_def)
    apply (simp add:eqlat_contract)
    apply (simp add:descat_contract)
    apply (simp only:has_fth_def has_desc_fth_def)
    by (auto simp:is_desc_fthread_def)



lemma INFM_drop_prefix:
  "(\<exists>\<^sub>\<infinity>i::nat. i > n \<and> P i) = (\<exists>\<^sub>\<infinity>i. P i)"
  apply (auto simp:INFM_nat)
  apply (drule_tac x = "max m n" in spec)
  apply (elim exE conjE)
  apply (rule_tac x = "na" in exI)
  by auto



lemma contract_keeps_threads:
  assumes inc[simp]: "increasing s"
  shows "(\<exists>\<theta>. is_desc_thread \<theta> p) 
  \<longleftrightarrow> (\<exists>\<theta>. is_desc_thread \<theta> (contract s p))"
  (is "?A \<longleftrightarrow> ?B")
proof 
  assume "?A"
  then obtain \<theta> n 
    where fr: "\<forall>i\<ge>n. eqlat p \<theta> i" 
      and ds: "\<exists>\<^sub>\<infinity>i. descat p \<theta> i"
    unfolding is_desc_thread_def 
    by auto

  let ?c\<theta> = "\<lambda>i. \<theta> (s i)"

  have "is_desc_thread ?c\<theta> (contract s p)"
    unfolding is_desc_thread_def
  proof (intro exI conjI)
    
    show "\<forall>i\<ge>n. eqlat (contract s p) ?c\<theta> i"
    proof (intro allI impI)
      fix i assume "n \<le> i"
      also have "i \<le> s i" 
        using increasing_inc by auto
      finally have "n \<le> s i" .

      with fr have "is_fthread \<theta> p (s i) (s (Suc i))"
        unfolding is_fthread_def by auto
      hence "has_fth p (s i) (s (Suc i)) (\<theta> (s i)) (\<theta> (s (Suc i)))"
        unfolding has_fth_def by auto
      with less_imp_le[OF increasing_strict]
      have "eql (prod (p\<langle>s i,s (Suc i)\<rangle>)) (\<theta> (s i)) (\<theta> (s (Suc i)))"
        by (simp add:Lemma7a)
      thus "eqlat (contract s p) ?c\<theta> i" unfolding contract_def
        by auto
    qed

    show "\<exists>\<^sub>\<infinity>i. descat (contract s p) ?c\<theta> i"
      unfolding INFM_nat 
    proof 
      fix i

      let ?K = "section_of s (max (s (Suc i)) n)"
      from `\<exists>\<^sub>\<infinity>i. descat p \<theta> i` obtain j
          where "s (Suc ?K) < j" "descat p \<theta> j"
        unfolding INFM_nat by blast
      
      let ?L = "section_of s j"
      {
        fix x assume r: "x \<in> section s ?L"
        
        have e1: "max (s (Suc i)) n < s (Suc ?K)" by (rule section_of2) simp
        note `s (Suc ?K) < j`
        also have "j < s (Suc ?L)"
          by (rule section_of2) simp
        finally have "Suc ?K \<le> ?L"
          by (simp add:increasing_bij)          
        with increasing_weak have "s (Suc ?K) \<le> s ?L" by simp
        with e1 r have "max (s (Suc i)) n < x" by simp
        
        hence "(s (Suc i)) < x" "n < x" by auto
      }
      note range_est = this
      
      have "is_desc_fthread \<theta> p (s ?L) (s (Suc ?L))"
        unfolding is_desc_fthread_def is_fthread_def
      proof
        show "\<forall>m\<in>section s ?L. eqlat p \<theta> m"
        proof 
          fix m assume "m\<in>section s ?L"
          with range_est(2) have "n < m" . 
          with fr show "eqlat p \<theta> m" by simp
        qed

        from in_section_of inc less_imp_le[OF `s (Suc ?K) < j`]
        have "j \<in> section s ?L" .

        with `descat p \<theta> j`
        show "\<exists>m\<in>section s ?L. descat p \<theta> m" ..
      qed
      
      with less_imp_le[OF increasing_strict]
      have a: "descat (contract s p) ?c\<theta> ?L"
        unfolding contract_def Lemma7b[symmetric]
        by (auto simp:Lemma7b[symmetric] has_desc_fth_def)
      
      have "i < ?L"
      proof (rule classical)
        assume "\<not> i < ?L" 
        hence "s ?L < s (Suc i)" 
          by (simp add:increasing_bij)
        also have "\<dots> < s ?L"
          by (rule range_est(1)) (simp add:increasing_strict)
        finally show ?thesis .
      qed
      with a show "\<exists>l. i < l \<and> descat (contract s p) ?c\<theta> l"
        by blast
    qed
  qed
  with exI show "?B" .
next
  assume "?B"
  then obtain \<theta> 
    where dthread: "is_desc_thread \<theta> (contract s p)" ..

  with dthreads_join inc 
  obtain \<theta>s where ths_spec:
    "desc (\<lambda>i. is_fthread (\<theta>s i) p (s i) (s (Suc i))
                  \<and> \<theta>s i (s i) = \<theta> i 
                  \<and> \<theta>s i (s (Suc i)) = \<theta> (Suc i))
          (\<lambda>i. is_desc_fthread (\<theta>s i) p (s i) (s (Suc i))
                  \<and> \<theta>s i (s i) = \<theta> i 
                  \<and> \<theta>s i (s (Suc i)) = \<theta> (Suc i))" 
      (is "desc ?alw ?inf") 
    by blast

  then obtain n where fr: "\<forall>i\<ge>n. ?alw i" by blast
  hence connected: "\<And>i. n < i \<Longrightarrow> \<theta>s i (s (Suc i)) = \<theta>s (Suc i) (s (Suc i))"
    by auto
  
  let ?j\<theta> = "connect s \<theta>s"
  
  from fr ths_spec have ths_spec2:
      "\<And>i. i > n \<Longrightarrow> is_fthread (\<theta>s i) p (s i) (s (Suc i))"
      "\<exists>\<^sub>\<infinity>i. is_desc_fthread (\<theta>s i) p (s i) (s (Suc i))"
    by (auto intro:INFM_mono)
  
  have p1: "\<And>i. i > n \<Longrightarrow> is_fthread ?j\<theta> p (s i) (s (Suc i))"
    by (rule connect_threads) (auto simp:connected ths_spec2)
  
  from ths_spec2(2)
  have "\<exists>\<^sub>\<infinity>i. n < i \<and> is_desc_fthread (\<theta>s i) p (s i) (s (Suc i))"
    unfolding INFM_drop_prefix .
  
  hence p2: "\<exists>\<^sub>\<infinity>i. is_desc_fthread ?j\<theta> p (s i) (s (Suc i))"
    apply (rule INFM_mono)
    apply (rule connect_dthreads)
    by (auto simp:connected)
  
  with `increasing s` p1
  have "is_desc_thread ?j\<theta> p" 
    by (rule mk_inf_desc_thread)
  with exI show "?A" .
qed


lemma repeated_edge:
  assumes "\<And>i. i > n \<Longrightarrow> dsc (snd (p i)) k k"
  shows "is_desc_thread (\<lambda>i. k) p"
proof-
  have th: "\<forall> m. \<exists>na>m. n < na" by arith
  show ?thesis using prems
  unfolding is_desc_thread_def 
  apply (auto)
  apply (rule_tac x="Suc n" in exI, auto)
  apply (rule INFM_mono[where P="\<lambda>i. n < i"])
  apply (simp only:INFM_nat)
  by (auto simp add: th)
qed

lemma fin_from_inf:
  assumes "is_thread n \<theta> p"
  assumes "n < i"
  assumes "i < j"
  shows "is_fthread \<theta> p i j"
  using prems
  unfolding is_thread_def is_fthread_def 
  by auto


subsection {* Ramsey's Theorem *}

definition 
  "set2pair S = (THE (x,y). x < y \<and> S = {x,y})"

lemma set2pair_conv: 
  fixes x y :: nat
  assumes "x < y"
  shows "set2pair {x, y} = (x, y)"
  unfolding set2pair_def
proof (rule the_equality, simp_all only:split_conv split_paired_all)
  from `x < y` show "x < y \<and> {x,y}={x,y}" by simp
next
  fix a b
  assume a: "a < b \<and> {x, y} = {a, b}"
  hence "{a, b} = {x, y}" by simp_all
  hence "(a, b) = (x, y) \<or> (a, b) = (y, x)" 
    by (cases "x = y") auto
  thus "(a, b) = (x, y)"
  proof 
    assume "(a, b) = (y, x)"
    with a and `x < y`
    show ?thesis by auto (* contradiction *)
  qed
qed  

definition 
  "set2list = inv set"

lemma finite_set2list: 
  assumes "finite S" 
  shows "set (set2list S) = S"
  unfolding set2list_def 
proof (rule f_inv_onto_f)
  from `finite S` have "\<exists>l. set l = S"
    by (rule finite_list)
  thus "S \<in> range set"
    unfolding image_def
    by auto
qed


corollary RamseyNatpairs:
  fixes S :: "'a set"
    and f :: "nat \<times> nat \<Rightarrow> 'a"

  assumes "finite S"
  and inS: "\<And>x y. x < y \<Longrightarrow> f (x, y) \<in> S"

  obtains T :: "nat set" and s :: "'a"
  where "infinite T"
    and "s \<in> S"
    and "\<And>x y. \<lbrakk>x \<in> T; y \<in> T; x < y\<rbrakk> \<Longrightarrow> f (x, y) = s"
proof -
  from `finite S`
  have "set (set2list S) = S" by (rule finite_set2list)
  then 
  obtain l where S: "S = set l" by auto
  also from set_conv_nth have "\<dots> = {l ! i |i. i < length l}" .
  finally have "S = {l ! i |i. i < length l}" .

  let ?s = "length l"

  from inS 
  have index_less: "\<And>x y. x \<noteq> y \<Longrightarrow> index_of l (f (set2pair {x, y})) < ?s"
  proof -
    fix x y :: nat
    assume neq: "x \<noteq> y"
    have "f (set2pair {x, y}) \<in> S"
    proof (cases "x < y")
      case True hence "set2pair {x, y} = (x, y)"
        by (rule set2pair_conv)
      with True inS
      show ?thesis by simp
    next
      case False 
      with neq have y_less: "y < x" by simp
      have x:"{x,y} = {y,x}" by auto
      with y_less have "set2pair {x, y} = (y, x)"
        by (simp add:set2pair_conv)
      with y_less inS
      show ?thesis by simp
    qed

    thus "index_of l (f (set2pair {x, y})) < length l"
      by (simp add: S index_of_length)
  qed

  have "\<exists>Y. infinite Y \<and>
    (\<exists>t. t < ?s \<and>
         (\<forall>x\<in>Y. \<forall>y\<in>Y. x \<noteq> y \<longrightarrow>
                      index_of l (f (set2pair {x, y})) = t))"
    by (rule Ramsey2[of "UNIV::nat set", simplified])
       (auto simp:index_less)
  then obtain T i
    where inf: "infinite T"
    and i: "i < length l"
    and d: "\<And>x y. \<lbrakk>x \<in> T; y\<in>T; x \<noteq> y\<rbrakk>
    \<Longrightarrow> index_of l (f (set2pair {x, y})) = i"
    by auto

  have "l ! i \<in> S" unfolding S using i
    by (rule nth_mem)
  moreover
  have "\<And>x y. x \<in> T \<Longrightarrow> y\<in>T \<Longrightarrow> x < y
    \<Longrightarrow> f (x, y) = l ! i"
  proof -
    fix x y assume "x \<in> T" "y \<in> T" "x < y"
    with d have 
      "index_of l (f (set2pair {x, y})) = i" by auto
    with `x < y`
    have "i = index_of l (f (x, y))" 
      by (simp add:set2pair_conv)
    with `i < length l`
    show "f (x, y) = l ! i" 
      by (auto intro:index_of_member[symmetric] iff:index_of_length)
  qed
  moreover note inf
  ultimately
  show ?thesis using prems
    by blast
qed


subsection {* Main Result *}


theorem LJA_Theorem4: 
  assumes "finite_acg A"
  shows "SCT A \<longleftrightarrow> SCT' A"
proof
  assume "SCT A"
  
  show "SCT' A"
  proof (rule classical)
    assume "\<not> SCT' A"
    
    then obtain n G
      where in_closure: "(tcl A) \<turnstile> n \<leadsto>\<^bsup>G\<^esup> n"
      and idemp: "G * G = G"
      and no_strict_arc: "\<forall>p. \<not>(G \<turnstile> p \<leadsto>\<^bsup>\<down>\<^esup> p)"
      unfolding SCT'_def no_bad_graphs_def by auto
    
    from in_closure obtain k
      where k_pow: "A ^ k \<turnstile> n \<leadsto>\<^bsup>G\<^esup> n"
      and "0 < k"
      unfolding in_tcl by auto
        
    from power_induces_path k_pow
    obtain loop where loop_props:
      "has_fpath A loop"
      "n = fst loop" "n = end_node loop"
      "G = prod loop" "k = length (snd loop)" . 

    with `0 < k` and path_loop_graph
    have "has_ipath A (omega loop)" by blast
    with `SCT A` 
    have thread: "\<exists>\<theta>. is_desc_thread \<theta> (omega loop)" by (auto simp:SCT_def)

    let ?s = "\<lambda>i. k * i"
    let ?cp = "\<lambda>i::nat. (n, G)"

    from loop_props have "fst loop = end_node loop" by auto
    with `0 < k` `k = length (snd loop)`
    have "\<And>i. (omega loop)\<langle>?s i,?s (Suc i)\<rangle> = loop"
      by (rule sub_path_loop)

    with `n = fst loop` `G = prod loop` `k = length (snd loop)`
    have a: "contract ?s (omega loop) = ?cp"
      unfolding contract_def
      by (simp add:path_loop_def split_def fst_p0)

    from `0 < k` have "increasing ?s"
      by (auto simp:increasing_def)
    with thread have "\<exists>\<theta>. is_desc_thread \<theta> ?cp"
      unfolding a[symmetric] 
      by (unfold contract_keeps_threads[symmetric])

    then obtain \<theta> where desc: "is_desc_thread \<theta> ?cp" by auto

    then obtain n where thr: "is_thread n \<theta> ?cp" 
      unfolding is_desc_thread_def is_thread_def 
      by auto

    have "finite (range \<theta>)"
    proof (rule finite_range_ignore_prefix)
      
      from `finite_acg A`
      have "finite_acg (tcl A)" by (simp add:finite_tcl)
      with in_closure have "finite_graph G" 
        unfolding finite_acg_def all_finite_def by blast
      thus "finite (nodes G)" by (rule finite_nodes)

      from thread_image_nodes[OF thr]
      show "\<forall>i\<ge>n. \<theta> i \<in> nodes G" by simp
    qed
    with finite_range
    obtain p where inf_visit: "\<exists>\<^sub>\<infinity>i. \<theta> i = p" by auto

    then obtain i where "n < i" "\<theta> i = p" 
      by (auto simp:INFM_nat)

    from desc
    have "\<exists>\<^sub>\<infinity>i. descat ?cp \<theta> i"
      unfolding is_desc_thread_def by auto
    then obtain j 
      where "i < j" and "descat ?cp \<theta> j"
      unfolding INFM_nat by auto
    from inf_visit obtain k where "j < k" "\<theta> k = p"
      by (auto simp:INFM_nat)

    from `i < j` `j < k` `n < i` thr 
      fin_from_inf[of n \<theta> ?cp]
      `descat ?cp \<theta> j`
    have "is_desc_fthread \<theta> ?cp i k"
      unfolding is_desc_fthread_def
      by auto

    with `\<theta> k = p` `\<theta> i = p`
    have dfth: "has_desc_fth ?cp i k p p"
      unfolding has_desc_fth_def
      by auto

    from `i < j` `j < k` have "i < k" by auto
    hence "prod (?cp\<langle>i, k\<rangle>) = G"
    proof (induct i rule:strict_inc_induct)
      case base thus ?case by (simp add:sub_path_def)
    next
      case (step i) thus ?case
        by (simp add:sub_path_def upt_rec[of i k] idemp)
    qed

    with `i < j` `j < k` dfth Lemma7b[of i k ?cp p p]
    have "dsc G p p" by auto
    with no_strict_arc have False by auto
    thus ?thesis ..
  qed
next
  assume "SCT' A"

  show "SCT A"
  proof (rule classical)
    assume "\<not> SCT A"

    with SCT_def
    obtain p 
      where ipath: "has_ipath A p"
      and no_desc_th: "\<not> (\<exists>\<theta>. is_desc_thread \<theta> p)"
      by blast

    from `finite_acg A`
    have "finite_acg (tcl A)" by (simp add: finite_tcl)
    hence "finite (dest_graph (tcl A))" (is "finite ?AG")
      by (simp add: finite_acg_def finite_graph_def)

    from pdesc_acgplus[OF ipath]
    have a: "\<And>x y. x<y \<Longrightarrow> pdesc p\<langle>x,y\<rangle> \<in> dest_graph (tcl A)"
      unfolding has_edge_def .
      
    obtain S G
      where "infinite S" "G \<in> dest_graph (tcl A)" 
      and all_G: "\<And>x y. \<lbrakk> x \<in> S; y \<in> S; x < y\<rbrakk> \<Longrightarrow> 
      pdesc (p\<langle>x,y\<rangle>) = G"
      apply (rule RamseyNatpairs[of ?AG "\<lambda>(x,y). pdesc p\<langle>x, y\<rangle>"])
      apply (rule `finite ?AG`)
      by (simp only:split_conv, rule a, auto)

    obtain n H m where
      G_struct: "G = (n, H, m)" by (cases G)

    let ?s = "enumerate S"
    let ?q = "contract ?s p"

    note all_in_S[simp] = enumerate_in_set[OF `infinite S`]
        from `infinite S` 
    have inc[simp]: "increasing ?s" 
      unfolding increasing_def by (simp add:enumerate_mono)
    note increasing_bij[OF this, simp]
      
    from ipath_contract inc ipath
    have "has_ipath (tcl A) ?q" .

    from all_G G_struct 
    have all_H: "\<And>i. (snd (?q i)) = H"
          unfolding contract_def 
      by simp
    
    have loop: "(tcl A) \<turnstile> n \<leadsto>\<^bsup>H\<^esup> n"
      and idemp: "H * H = H"
    proof - 
      let ?i = "?s 0" and ?j = "?s (Suc 0)" and ?k = "?s (Suc (Suc 0))"
      
      have "pdesc (p\<langle>?i,?j\<rangle>) = G"
                and "pdesc (p\<langle>?j,?k\<rangle>) = G"
                and "pdesc (p\<langle>?i,?k\<rangle>) = G"
                using all_G 
                by auto
          
      with G_struct 
      have "m = end_node (p\<langle>?i,?j\<rangle>)"
                                "n = fst (p\<langle>?j,?k\<rangle>)"
                                and Hs: "prod (p\<langle>?i,?j\<rangle>) = H"
                                "prod (p\<langle>?j,?k\<rangle>) = H"
                                "prod (p\<langle>?i,?k\<rangle>) = H"
                by auto
                        
      hence "m = n" by simp
      thus "tcl A \<turnstile> n \<leadsto>\<^bsup>H\<^esup> n"
                using G_struct `G \<in> dest_graph (tcl A)`
                by (simp add:has_edge_def)
          
      from sub_path_prod[of ?i ?j ?k p]      
      show "H * H = H"
                unfolding Hs by simp
    qed
    moreover have "\<And>k. \<not>dsc H k k"
    proof
      fix k :: 'a assume "dsc H k k"
      
      with all_H repeated_edge
      have "\<exists>\<theta>. is_desc_thread \<theta> ?q" by fast
          with inc have "\<exists>\<theta>. is_desc_thread \<theta> p"
                by (subst contract_keeps_threads) 
      with no_desc_th
      show False ..
    qed
    ultimately 
    have False
      using `SCT' A`[unfolded SCT'_def no_bad_graphs_def]
      by blast
    thus ?thesis ..
  qed
qed

end
