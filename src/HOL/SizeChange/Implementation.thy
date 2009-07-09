(*  Title:      HOL/Library/SCT_Implementation.thy
    ID:         $Id$
    Author:     Alexander Krauss, TU Muenchen
*)

header {* Implemtation of the SCT criterion *}

theory Implementation
imports Correctness
begin

fun edges_match :: "('n \<times> 'e \<times> 'n) \<times> ('n \<times> 'e \<times> 'n) \<Rightarrow> bool"
where
  "edges_match ((n, e, m), (n',e',m')) = (m = n')"

fun connect_edges :: 
  "('n \<times> ('e::times) \<times> 'n) \<times> ('n \<times> 'e \<times> 'n)
  \<Rightarrow> ('n \<times> 'e \<times> 'n)"
where
  "connect_edges ((n,e,m), (n', e', m')) = (n, e * e', m')"

lemma grcomp_code [code]:
  "grcomp (Graph G) (Graph H) = Graph (connect_edges ` { x \<in> G\<times>H. edges_match x })"
  by (rule graph_ext) (auto simp:graph_mult_def has_edge_def image_def)


lemma mk_tcl_finite_terminates:
  fixes A :: "'a acg"
  assumes fA: "finite_acg A" 
  shows "mk_tcl_dom (A, A)"
proof -
  from fA have fin_tcl: "finite_acg (tcl A)"
    by (simp add:finite_tcl)

  hence "finite (dest_graph (tcl A))"
    unfolding finite_acg_def finite_graph_def ..

  let ?count = "\<lambda>G. card (dest_graph G)"
  let ?N = "?count (tcl A)"
  let ?m = "\<lambda>X. ?N - (?count X)"

  let ?P = "\<lambda>X. mk_tcl_dom (A, X)"
  
  {
    fix X
    assume "X \<le> tcl A"
    then
    have "mk_tcl_dom (A, X)"
    proof (induct X rule:measure_induct_rule[of ?m])
      case (less X)
      show ?case
      proof (cases "X * A \<le> X")
        case True 
        with mk_tcl.domintros show ?thesis by auto
      next
        case False
        then have l: "X < X + X * A"
          unfolding graph_less_def graph_leq_def graph_plus_def
          by auto

        from `X \<le> tcl A` 
        have "X * A \<le> tcl A * A" by (simp add:mult_mono)
        also have "\<dots> \<le> A + tcl A * A" by simp
        also have "\<dots> = tcl A" by (simp add:tcl_unfold_right[symmetric])
        finally have "X * A \<le> tcl A" .
        with `X \<le> tcl A` 
        have "X + X * A \<le> tcl A + tcl A"
          by (rule add_mono)
        hence less_tcl: "X + X * A \<le> tcl A" by simp 
        hence "X < tcl A"
          using l `X \<le> tcl A` by auto

        from less_tcl fin_tcl
        have "finite_acg (X + X * A)" by (rule finite_acg_subset)
        hence "finite (dest_graph (X + X * A))" 
          unfolding finite_acg_def finite_graph_def ..
        
        hence X: "?count X < ?count (X + X * A)"
          using l[simplified graph_less_def graph_leq_def]
          by (rule psubset_card_mono)
        
        have "?count X < ?N" 
          apply (rule psubset_card_mono)
          by fact (rule `X < tcl A`[simplified graph_less_def])
        
        with X have "?m (X + X * A) < ?m X" by arith
        
        from  less.hyps this less_tcl
        have "mk_tcl_dom (A, X + X * A)" .
        with mk_tcl.domintros show ?thesis .
      qed
    qed
  }
  from this less_tcl show ?thesis .
qed


lemma mk_tcl_finite_tcl:
  fixes A :: "'a acg"
  assumes fA: "finite_acg A"
  shows "mk_tcl A A = tcl A"
  using mk_tcl_finite_terminates[OF fA]
  by (simp only: tcl_def mk_tcl_correctness star_simulation)

definition test_SCT :: "nat acg \<Rightarrow> bool"
where
  "test_SCT \<A> = 
  (let \<T> = mk_tcl \<A> \<A>
    in (\<forall>(n,G,m)\<in>dest_graph \<T>. 
          n \<noteq> m \<or> G * G \<noteq> G \<or> 
         (\<exists>(p::nat,e,q)\<in>dest_graph G. p = q \<and> e = LESS)))"


lemma SCT'_exec:
  assumes fin: "finite_acg A"
  shows "SCT' A = test_SCT A"
  using mk_tcl_finite_tcl[OF fin]
  unfolding test_SCT_def Let_def 
  unfolding SCT'_def no_bad_graphs_def has_edge_def
  by force

code_modulename SML
  Implementation Graphs

lemma [code]:
  "(G\<Colon>('a\<Colon>eq, 'b\<Colon>eq) graph) \<le> H \<longleftrightarrow> dest_graph G \<subseteq> dest_graph H"
  "(G\<Colon>('a\<Colon>eq, 'b\<Colon>eq) graph) < H \<longleftrightarrow> dest_graph G \<subset> dest_graph H"
  unfolding graph_leq_def graph_less_def by rule+

lemma [code]:
  "(G\<Colon>('a\<Colon>eq, 'b\<Colon>eq) graph) + H = Graph (dest_graph G \<union> dest_graph H)"
  unfolding graph_plus_def ..

lemma [code]:
  "(G\<Colon>('a\<Colon>eq, 'b\<Colon>{eq, times}) graph) * H = grcomp G H"
  unfolding graph_mult_def ..



lemma SCT'_empty: "SCT' (Graph {})"
  unfolding SCT'_def no_bad_graphs_def graph_zero_def[symmetric]
  tcl_zero
  by (simp add:in_grzero)



subsection {* Witness checking *}

definition test_SCT_witness :: "nat acg \<Rightarrow> nat acg \<Rightarrow> bool"
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
  using assms
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

(* ML {* @{code test_SCT} *} *)

end
