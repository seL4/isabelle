theory SCT_Implementation
imports ExecutableSet SCT_Definition
begin

fun edges_match :: "('n \<times> 'e \<times> 'n) \<times> ('n \<times> 'e \<times> 'n) \<Rightarrow> bool"
where
  "edges_match ((n, e, m), (n',e',m')) = (m = n')"

fun connect_edges :: 
  "('n \<times> ('e::times) \<times> 'n) \<times> ('n \<times> 'e \<times> 'n)
  \<Rightarrow> ('n \<times> 'e \<times> 'n)"
where
  "connect_edges ((n,e,m), (n', e', m')) = (n, e * e', m')"

lemma grcomp_code[code]:
  "grcomp (Graph G) (Graph H) = Graph (connect_edges ` { x \<in> G\<times>H. edges_match x })"
  by (rule graph_ext) (auto simp:graph_mult_def has_edge_def image_def)


definition test_SCT :: "acg \<Rightarrow> bool"
where
  "test_SCT \<A> = 
  (let \<T> = mk_tcl \<A> \<A>
    in (\<T> \<noteq> 0 \<and>
       (\<forall>(n,G,m)\<in>dest_graph \<T>. 
          n \<noteq> m \<or> G * G \<noteq> G \<or> 
         (\<exists>(p::nat,e,q)\<in>dest_graph G. p = q \<and> e = LESS))))"


lemma SCT'_exec:
  assumes a: "test_SCT \<A>"
  shows "SCT' \<A>"
proof -
  from mk_tcl_correctness2 a 
  have "mk_tcl \<A> \<A> = tcl \<A>" 
    unfolding test_SCT_def Let_def by auto
  
  with a
  show ?thesis
    unfolding SCT'_def no_bad_graphs_def test_SCT_def Let_def has_edge_def
    by auto
qed

code_modulename SML
  Implementation Graphs

lemma [code func]:
  "(G\<Colon>('a\<Colon>eq, 'b\<Colon>eq) graph) \<le> H \<longleftrightarrow> dest_graph G \<subseteq> dest_graph H"
  "(G\<Colon>('a\<Colon>eq, 'b\<Colon>eq) graph) < H \<longleftrightarrow> dest_graph G \<subset> dest_graph H"
  unfolding graph_leq_def graph_less_def by rule+

lemma [code func]:
  "(G\<Colon>('a\<Colon>eq, 'b\<Colon>eq) graph) + H = Graph (dest_graph G \<union> dest_graph H)"
  unfolding graph_plus_def ..

lemma [code func]:
  "(G\<Colon>('a\<Colon>eq, 'b\<Colon>{eq, times}) graph) * H = grcomp G H"
  unfolding graph_mult_def ..



lemma SCT'_empty: "SCT' (Graph {})"
  unfolding SCT'_def no_bad_graphs_def graph_zero_def[symmetric]
  tcl_zero
  by (simp add:in_grzero)



subsection {* Witness checking *}


definition test_SCT_witness :: "acg \<Rightarrow> acg \<Rightarrow> bool"
where
  "test_SCT_witness A T = 
  (A \<le> T \<and> A * T \<le> T \<and>
       (\<forall>(n,G,m)\<in>dest_graph T. 
          n \<noteq> m \<or> G * G \<noteq> G \<or> 
         (\<exists>(p::nat,e,q)\<in>dest_graph G. p = q \<and> e = LESS)))"


lemma no_bad_graphs_ucl:
  assumes "A \<le> B"
  assumes "no_bad_graphs B"
  shows "no_bad_graphs A"
using prems
unfolding no_bad_graphs_def has_edge_def graph_leq_def 
by blast



lemma SCT'_witness:
  assumes a: "test_SCT_witness A T"
  shows "SCT' A"
proof -
  from a have "A \<le> T" "A * T \<le> T" by (auto simp:test_SCT_witness_def)
  hence "A + A * T \<le> T" 
    by (subst add_idem[of T, symmetric], rule add_mono)
  with star3' have "tcl A \<le> T" unfolding tcl_def .
  moreover
  from a have "no_bad_graphs T"
    unfolding no_bad_graphs_def test_SCT_witness_def has_edge_def
    by auto
  ultimately
  show ?thesis
    unfolding SCT'_def
    by (rule no_bad_graphs_ucl)
qed


code_modulename SML
  Graphs SCT
  Kleene_Algebras SCT
  SCT_Implementation SCT

code_gen test_SCT (SML -)


end








