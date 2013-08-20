theory Legacy_Mrec
imports Heap_Monad
begin

subsubsection {* A monadic combinator for simple recursive functions *}

text {*
  NOTE: The use of this obsolete combinator is discouraged. Instead, use the
  @{text "partal_function (heap)"} command.
*}

text {* Using a locale to fix arguments f and g of MREC *}

locale mrec =
  fixes f :: "'a \<Rightarrow> ('b + 'a) Heap"
  and g :: "'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b Heap"
begin

function (default "\<lambda>(x, h). None") mrec :: "'a \<Rightarrow> heap \<Rightarrow> ('b \<times> heap) option" where
  "mrec x h = (case execute (f x) h of
     Some (Inl r, h') \<Rightarrow> Some (r, h')
   | Some (Inr s, h') \<Rightarrow> (case mrec s h' of
             Some (z, h'') \<Rightarrow> execute (g x s z) h''
           | None \<Rightarrow> None)
   | None \<Rightarrow> None)"
by auto

lemma graph_implies_dom:
  "mrec_graph x y \<Longrightarrow> mrec_dom x"
apply (induct rule:mrec_graph.induct) 
apply (rule accpI)
apply (erule mrec_rel.cases)
by simp

lemma mrec_default: "\<not> mrec_dom (x, h) \<Longrightarrow> mrec x h = None"
  unfolding mrec_def 
  by (rule fundef_default_value[OF mrec_sumC_def graph_implies_dom, of _ _ "(x, h)", simplified])

lemma mrec_di_reverse: 
  assumes "\<not> mrec_dom (x, h)"
  shows "
   (case execute (f x) h of
     Some (Inl r, h') \<Rightarrow> False
   | Some (Inr s, h') \<Rightarrow> \<not> mrec_dom (s, h')
   | None \<Rightarrow> False
   )" 
using assms apply (auto split: option.split sum.split)
apply (rule ccontr)
apply (erule notE, rule accpI, elim mrec_rel.cases, auto)+
done

lemma mrec_rule:
  "mrec x h = 
   (case execute (f x) h of
     Some (Inl r, h') \<Rightarrow> Some (r, h')
   | Some (Inr s, h') \<Rightarrow> 
          (case mrec s h' of
             Some (z, h'') \<Rightarrow> execute (g x s z) h''
           | None \<Rightarrow> None)
   | None \<Rightarrow> None
   )"
apply (cases "mrec_dom (x,h)", simp add: mrec.psimps)
apply (frule mrec_default)
apply (frule mrec_di_reverse, simp)
by (auto split: sum.split option.split simp: mrec_default)

definition
  "MREC x = Heap_Monad.Heap (mrec x)"

lemma MREC_rule:
  "MREC x = 
  do { y \<leftarrow> f x;
                (case y of 
                Inl r \<Rightarrow> return r
              | Inr s \<Rightarrow> 
                do { z \<leftarrow> MREC s ;
                     g x s z })}"
  unfolding MREC_def
  unfolding bind_def return_def
  apply simp
  apply (rule ext)
  apply (unfold mrec_rule[of x])
  by (auto simp add: execute_simps split: option.splits prod.splits sum.splits)

lemma MREC_pinduct:
  assumes "execute (MREC x) h = Some (r, h')"
  assumes non_rec_case: "\<And> x h h' r. execute (f x) h = Some (Inl r, h') \<Longrightarrow> P x h h' r"
  assumes rec_case: "\<And> x h h1 h2 h' s z r. execute (f x) h = Some (Inr s, h1) \<Longrightarrow> execute (MREC s) h1 = Some (z, h2) \<Longrightarrow> P s h1 h2 z
    \<Longrightarrow> execute (g x s z) h2 = Some (r, h') \<Longrightarrow> P x h h' r"
  shows "P x h h' r"
proof -
  from assms(1) have mrec: "mrec x h = Some (r, h')"
    unfolding MREC_def execute.simps .
  from mrec have dom: "mrec_dom (x, h)"
    apply -
    apply (rule ccontr)
    apply (drule mrec_default) by auto
  from mrec have h'_r: "h' = snd (the (mrec x h))" "r = fst (the (mrec x h))"
    by auto
  from mrec have "P x h (snd (the (mrec x h))) (fst (the (mrec x h)))"
  proof (induct arbitrary: r h' rule: mrec.pinduct[OF dom])
    case (1 x h)
    obtain rr h' where "the (mrec x h) = (rr, h')" by fastforce
    show ?case
    proof (cases "execute (f x) h")
      case (Some result)
      then obtain a h1 where exec_f: "execute (f x) h = Some (a, h1)" by fastforce
      note Inl' = this
      show ?thesis
      proof (cases a)
        case (Inl aa)
        from this Inl' 1(1) exec_f mrec non_rec_case show ?thesis
          by (auto simp: mrec.psimps)
      next
        case (Inr b)
        note Inr' = this
        show ?thesis
        proof (cases "mrec b h1")
          case (Some result)
          then obtain aaa h2 where mrec_rec: "mrec b h1 = Some (aaa, h2)" by fastforce
          moreover from this have "P b h1 (snd (the (mrec b h1))) (fst (the (mrec b h1)))"
            apply (intro 1(2))
            apply (auto simp add: Inr Inl')
            done
          moreover note mrec mrec_rec exec_f Inl' Inr' 1(1) 1(3)
          ultimately show ?thesis
            apply auto
            apply (rule rec_case)
            apply auto
            unfolding MREC_def by (auto simp: mrec.psimps)
        next
          case None
          from this 1(1) exec_f mrec Inr' 1(3) show ?thesis by (auto simp: mrec.psimps)
        qed
      qed
    next
      case None
      from this 1(1) mrec 1(3) show ?thesis by (simp add: mrec.psimps)
    qed
  qed
  from this h'_r show ?thesis by simp
qed

end

text {* Providing global versions of the constant and the theorems *}

abbreviation "MREC == mrec.MREC"
lemmas MREC_rule = mrec.MREC_rule
lemmas MREC_pinduct = mrec.MREC_pinduct

lemma MREC_induct:
  assumes "effect (MREC f g x) h h' r"
  assumes "\<And> x h h' r. effect (f x) h h' (Inl r) \<Longrightarrow> P x h h' r"
  assumes "\<And> x h h1 h2 h' s z r. effect (f x) h h1 (Inr s) \<Longrightarrow> effect (MREC f g s) h1 h2 z \<Longrightarrow> P s h1 h2 z
    \<Longrightarrow> effect (g x s z) h2 h' r \<Longrightarrow> P x h h' r"
  shows "P x h h' r"
proof (rule MREC_pinduct[OF assms(1) [unfolded effect_def]])
  fix x h h1 h2 h' s z r
  assume "Heap_Monad.execute (f x) h = Some (Inr s, h1)"
    "Heap_Monad.execute (MREC f g s) h1 = Some (z, h2)"
    "P s h1 h2 z"
    "Heap_Monad.execute (g x s z) h2 = Some (r, h')"
  from assms(3) [unfolded effect_def, OF this(1) this(2) this(3) this(4)]
  show "P x h h' r" .
next
qed (auto simp add: assms(2)[unfolded effect_def])

end
