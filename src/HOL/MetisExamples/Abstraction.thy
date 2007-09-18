(*  Title:      HOL/MetisExamples/Abstraction.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory

Testing the metis method
*)

theory Abstraction imports FuncSet
begin

(*For Christoph Benzmueller*)
lemma "x<1 & ((op=) = (op=)) ==> ((op=) = (op=)) & (x<(2::nat))";
  by (metis One_nat_def less_Suc0 not_less0 not_less_eq numeral_2_eq_2)

(*this is a theorem, but we can't prove it unless ext is applied explicitly
lemma "(op=) = (%x y. y=x)"
*)

consts
  monotone :: "['a => 'a, 'a set, ('a *'a)set] => bool"
  pset  :: "'a set => 'a set"
  order :: "'a set => ('a * 'a) set"

ML{*ResAtp.problem_name := "Abstraction__Collect_triv"*}
lemma (*Collect_triv:*) "a \<in> {x. P x} ==> P a"
proof (neg_clausify)
assume 0: "(a\<Colon>'a\<Colon>type) \<in> Collect (P\<Colon>'a\<Colon>type \<Rightarrow> bool)"
assume 1: "\<not> (P\<Colon>'a\<Colon>type \<Rightarrow> bool) (a\<Colon>'a\<Colon>type)"
have 2: "(P\<Colon>'a\<Colon>type \<Rightarrow> bool) (a\<Colon>'a\<Colon>type)"
  by (metis CollectD 0)
show "False"
  by (metis 2 1)
qed

lemma Collect_triv: "a \<in> {x. P x} ==> P a"
by (metis mem_Collect_eq)


ML{*ResAtp.problem_name := "Abstraction__Collect_mp"*}
lemma "a \<in> {x. P x --> Q x} ==> a \<in> {x. P x} ==> a \<in> {x. Q x}"
  by (metis CollectI Collect_imp_eq ComplD UnE mem_Collect_eq);
  --{*34 secs*}

ML{*ResAtp.problem_name := "Abstraction__Sigma_triv"*}
lemma "(a,b) \<in> Sigma A B ==> a \<in> A & b \<in> B a"
proof (neg_clausify)
assume 0: "(a\<Colon>'a\<Colon>type, b\<Colon>'b\<Colon>type) \<in> Sigma (A\<Colon>'a\<Colon>type set) (B\<Colon>'a\<Colon>type \<Rightarrow> 'b\<Colon>type set)"
assume 1: "(a\<Colon>'a\<Colon>type) \<notin> (A\<Colon>'a\<Colon>type set) \<or> (b\<Colon>'b\<Colon>type) \<notin> (B\<Colon>'a\<Colon>type \<Rightarrow> 'b\<Colon>type set) a"
have 2: "(a\<Colon>'a\<Colon>type) \<in> (A\<Colon>'a\<Colon>type set)"
  by (metis SigmaD1 0)
have 3: "(b\<Colon>'b\<Colon>type) \<in> (B\<Colon>'a\<Colon>type \<Rightarrow> 'b\<Colon>type set) (a\<Colon>'a\<Colon>type)"
  by (metis SigmaD2 0)
have 4: "(b\<Colon>'b\<Colon>type) \<notin> (B\<Colon>'a\<Colon>type \<Rightarrow> 'b\<Colon>type set) (a\<Colon>'a\<Colon>type)"
  by (metis 1 2)
show "False"
  by (metis 3 4)
qed

lemma Sigma_triv: "(a,b) \<in> Sigma A B ==> a \<in> A & b \<in> B a"
by (metis SigmaD1 SigmaD2)

ML{*ResAtp.problem_name := "Abstraction__Sigma_Collect"*}
lemma "(a,b) \<in> (SIGMA x: A. {y. x = f y}) ==> a \<in> A & a = f b"
(*???metis cannot prove this
by (metis CollectD SigmaD1 SigmaD2 UN_eq)
Also, UN_eq is unnecessary*)
by (meson CollectD SigmaD1 SigmaD2)



(*single-step*)
lemma "(a,b) \<in> (SIGMA x: A. {y. x = f y}) ==> a \<in> A & a = f b"
proof (neg_clausify)
assume 0: "(a, b) \<in> Sigma A (llabs_subgoal_1 f)"
assume 1: "\<And>f x. llabs_subgoal_1 f x = Collect (COMBB (op = x) f)"
assume 2: "a \<notin> A \<or> a \<noteq> f b"
have 3: "a \<in> A"
  by (metis SigmaD1 0)
have 4: "f b \<noteq> a"
  by (metis 3 2)
have 5: "f b = a"
  by (metis Domain_Id Compl_UNIV_eq singleton_conv2 vimage_Collect_eq 1 vimage_singleton_eq SigmaD2 0)
show "False"
  by (metis 5 4)
qed finish_clausify


ML{*ResAtp.problem_name := "Abstraction__CLF_eq_in_pp"*}
lemma "(cl,f) \<in> CLF ==> CLF = (SIGMA cl: CL.{f. f \<in> pset cl}) ==> f \<in> pset cl"
apply (metis Collect_mem_eq SigmaD2);
done

lemma "(cl,f) \<in> CLF ==> CLF = (SIGMA cl: CL.{f. f \<in> pset cl}) ==> f \<in> pset cl"proof (neg_clausify)
assume 0: "(cl, f) \<in> CLF"
assume 1: "CLF = Sigma CL llabs_subgoal_1"
assume 2: "\<And>cl. llabs_subgoal_1 cl = Collect (llabs_Predicate_Xsup_Un_eq_1_ (pset cl))"
assume 3: "f \<notin> pset cl"
show "False"
  by (metis 0 1 SigmaD2 3 2 Collect_mem_eq)
qed finish_clausify (*ugly hack: combinators??*)

ML{*ResAtp.problem_name := "Abstraction__Sigma_Collect_Pi"*}
lemma
    "(cl,f) \<in> (SIGMA cl: CL. {f. f \<in> pset cl \<rightarrow> pset cl}) ==> 
    f \<in> pset cl \<rightarrow> pset cl"
apply (metis Collect_mem_eq SigmaD2);
done

lemma
    "(cl,f) \<in> (SIGMA cl::'a set : CL. {f. f \<in> pset cl \<rightarrow> pset cl}) ==> 
    f \<in> pset cl \<rightarrow> pset cl"
proof (neg_clausify)
assume 0: "(cl, f) \<in> Sigma CL llabs_subgoal_1"
assume 1: "\<And>cl. llabs_subgoal_1 cl =
     Collect
      (llabs_Predicate_Xsup_Un_eq_1_ (Pi (pset cl) (COMBK (pset cl))))"
assume 2: "f \<notin> Pi (pset cl) (COMBK (pset cl))"
have 3: "\<not> llabs_Predicate_Xsup_Un_eq_1_ (Pi (pset cl) (COMBK (pset cl))) f"
  by (metis Collect_mem_eq 2)
show "False"
  by (metis acc_def 0 Collect_mem_eq SigmaD2 3 1 Collect_mem_eq)
qed finish_clausify
    (*Hack to prevent the "Additional hypotheses" error*)

ML{*ResAtp.problem_name := "Abstraction__Sigma_Collect_Int"*}
lemma
    "(cl,f) \<in> (SIGMA cl: CL. {f. f \<in> pset cl \<inter> cl}) ==>
   f \<in> pset cl \<inter> cl"
by (metis Collect_mem_eq SigmaD2)

ML{*ResAtp.problem_name := "Abstraction__Sigma_Collect_Pi_mono"*}
lemma
    "(cl,f) \<in> (SIGMA cl: CL. {f. f \<in> pset cl \<rightarrow> pset cl & monotone f (pset cl) (order cl)}) ==>
   (f \<in> pset cl \<rightarrow> pset cl)  &  (monotone f (pset cl) (order cl))"
by auto

ML{*ResAtp.problem_name := "Abstraction__CLF_subset_Collect_Int"*}
lemma "(cl,f) \<in> CLF ==> 
   CLF \<subseteq> (SIGMA cl: CL. {f. f \<in> pset cl \<inter> cl}) ==>
   f \<in> pset cl \<inter> cl"
by (metis Collect_mem_eq Int_def SigmaD2 UnCI Un_absorb1)
  --{*@{text Int_def} is redundant}

ML{*ResAtp.problem_name := "Abstraction__CLF_eq_Collect_Int"*}
lemma "(cl,f) \<in> CLF ==> 
   CLF = (SIGMA cl: CL. {f. f \<in> pset cl \<inter> cl}) ==>
   f \<in> pset cl \<inter> cl"
by (metis Collect_mem_eq Int_commute SigmaD2)

ML{*ResAtp.problem_name := "Abstraction__CLF_subset_Collect_Pi"*}
lemma 
   "(cl,f) \<in> CLF ==> 
    CLF \<subseteq> (SIGMA cl': CL. {f. f \<in> pset cl' \<rightarrow> pset cl'}) ==> 
    f \<in> pset cl \<rightarrow> pset cl"
by (metis Collect_mem_eq SigmaD2 subsetD)

ML{*ResAtp.problem_name := "Abstraction__CLF_eq_Collect_Pi"*}
lemma 
  "(cl,f) \<in> CLF ==> 
   CLF = (SIGMA cl: CL. {f. f \<in> pset cl \<rightarrow> pset cl}) ==> 
   f \<in> pset cl \<rightarrow> pset cl"
by (metis Collect_mem_eq SigmaD2 contra_subsetD equalityE)

ML{*ResAtp.problem_name := "Abstraction__CLF_eq_Collect_Pi_mono"*}
lemma 
  "(cl,f) \<in> CLF ==> 
   CLF = (SIGMA cl: CL. {f. f \<in> pset cl \<rightarrow> pset cl & monotone f (pset cl) (order cl)}) ==>
   (f \<in> pset cl \<rightarrow> pset cl)  &  (monotone f (pset cl) (order cl))"
by auto

ML{*ResAtp.problem_name := "Abstraction__map_eq_zipA"*}
lemma "map (%x. (f x, g x)) xs = zip (map f xs) (map g xs)"
apply (induct xs)
(*sledgehammer*)  
apply auto
done

ML{*ResAtp.problem_name := "Abstraction__map_eq_zipB"*}
lemma "map (%w. (w -> w, w \<times> w)) xs = 
       zip (map (%w. w -> w) xs) (map (%w. w \<times> w) xs)"
apply (induct xs)
(*sledgehammer*)  
apply auto
done

ML{*ResAtp.problem_name := "Abstraction__image_evenA"*}
lemma "(%x. Suc(f x)) ` {x. even x} <= A ==> (\<forall>x. even x --> Suc(f x) \<in> A)";
(*sledgehammer*)  
by auto

ML{*ResAtp.problem_name := "Abstraction__image_evenB"*}
lemma "(%x. f (f x)) ` ((%x. Suc(f x)) ` {x. even x}) <= A 
       ==> (\<forall>x. even x --> f (f (Suc(f x))) \<in> A)";
(*sledgehammer*)  
by auto

ML{*ResAtp.problem_name := "Abstraction__image_curry"*}
lemma "f \<in> (%u v. b \<times> u \<times> v) ` A ==> \<forall>u v. P (b \<times> u \<times> v) ==> P(f y)" 
(*sledgehammer*)  
by auto

ML{*ResAtp.problem_name := "Abstraction__image_TimesA"*}
lemma image_TimesA: "(%(x,y). (f x, g y)) ` (A \<times> B) = (f`A) \<times> (g`B)"
(*sledgehammer*) 
apply (rule equalityI)
(***Even the two inclusions are far too difficult
ML{*ResAtp.problem_name := "Abstraction__image_TimesA_simpler"*}
***)
apply (rule subsetI)
apply (erule imageE)
(*V manages from here with help: Abstraction__image_TimesA_simpler_1_b.p*)
apply (erule ssubst)
apply (erule SigmaE)
(*V manages from here: Abstraction__image_TimesA_simpler_1_a.p*)
apply (erule ssubst)
apply (subst split_conv)
apply (rule SigmaI) 
apply (erule imageI) +
txt{*subgoal 2*}
apply (clarify );
apply (simp add: );  
apply (rule rev_image_eqI)  
apply (blast intro: elim:); 
apply (simp add: );
done

(*Given the difficulty of the previous problem, these two are probably
impossible*)

ML{*ResAtp.problem_name := "Abstraction__image_TimesB"*}
lemma image_TimesB:
    "(%(x,y,z). (f x, g y, h z)) ` (A \<times> B \<times> C) = (f`A) \<times> (g`B) \<times> (h`C)" 
(*sledgehammer*) 
by force

ML{*ResAtp.problem_name := "Abstraction__image_TimesC"*}
lemma image_TimesC:
    "(%(x,y). (x \<rightarrow> x, y \<times> y)) ` (A \<times> B) = 
     ((%x. x \<rightarrow> x) ` A) \<times> ((%y. y \<times> y) ` B)" 
(*sledgehammer*) 
by auto

end
