(*  Title:      HOL/MetisExamples/Abstraction.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory

Testing the metis method
*)

theory Abstraction
imports Main FuncSet
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

ML{*AtpWrapper.problem_name := "Abstraction__Collect_triv"*}
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


ML{*AtpWrapper.problem_name := "Abstraction__Collect_mp"*}
lemma "a \<in> {x. P x --> Q x} ==> a \<in> {x. P x} ==> a \<in> {x. Q x}"
  by (metis CollectI Collect_imp_eq ComplD UnE mem_Collect_eq);
  --{*34 secs*}

ML{*AtpWrapper.problem_name := "Abstraction__Sigma_triv"*}
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

ML{*AtpWrapper.problem_name := "Abstraction__Sigma_Collect"*}
lemma "(a,b) \<in> (SIGMA x: A. {y. x = f y}) ==> a \<in> A & a = f b"
(*???metis says this is satisfiable!
by (metis CollectD SigmaD1 SigmaD2)
*)
by (meson CollectD SigmaD1 SigmaD2)


(*single-step*)
lemma "(a,b) \<in> (SIGMA x: A. {y. x = f y}) ==> a \<in> A & a = f b"
by (metis SigmaD1 SigmaD2 insert_def singleton_conv2 Un_empty_right vimage_Collect_eq vimage_def vimage_singleton_eq)


lemma "(a,b) \<in> (SIGMA x: A. {y. x = f y}) ==> a \<in> A & a = f b"
proof (neg_clausify)
assume 0: "(a\<Colon>'a\<Colon>type, b\<Colon>'b\<Colon>type)
\<in> Sigma (A\<Colon>'a\<Colon>type set)
   (COMBB Collect (COMBC (COMBB COMBB op =) (f\<Colon>'b\<Colon>type \<Rightarrow> 'a\<Colon>type)))"
assume 1: "(a\<Colon>'a\<Colon>type) \<notin> (A\<Colon>'a\<Colon>type set) \<or> a \<noteq> (f\<Colon>'b\<Colon>type \<Rightarrow> 'a\<Colon>type) (b\<Colon>'b\<Colon>type)"
have 2: "(a\<Colon>'a\<Colon>type) \<in> (A\<Colon>'a\<Colon>type set)"
  by (metis 0 SigmaD1)
have 3: "(b\<Colon>'b\<Colon>type)
\<in> COMBB Collect (COMBC (COMBB COMBB op =) (f\<Colon>'b\<Colon>type \<Rightarrow> 'a\<Colon>type)) (a\<Colon>'a\<Colon>type)"
  by (metis 0 SigmaD2) 
have 4: "(b\<Colon>'b\<Colon>type) \<in> Collect (COMBB (op = (a\<Colon>'a\<Colon>type)) (f\<Colon>'b\<Colon>type \<Rightarrow> 'a\<Colon>type))"
  by (metis 3)
have 5: "(f\<Colon>'b\<Colon>type \<Rightarrow> 'a\<Colon>type) (b\<Colon>'b\<Colon>type) \<noteq> (a\<Colon>'a\<Colon>type)"
  by (metis 1 2)
have 6: "(f\<Colon>'b\<Colon>type \<Rightarrow> 'a\<Colon>type) (b\<Colon>'b\<Colon>type) = (a\<Colon>'a\<Colon>type)"
  by (metis 4 vimage_singleton_eq insert_def singleton_conv2 Un_empty_right vimage_Collect_eq vimage_def)
show "False"
  by (metis 5 6)
qed

(*Alternative structured proof, untyped*)
lemma "(a,b) \<in> (SIGMA x: A. {y. x = f y}) ==> a \<in> A & a = f b"
proof (neg_clausify)
assume 0: "(a, b) \<in> Sigma A (COMBB Collect (COMBC (COMBB COMBB op =) f))"
have 1: "b \<in> Collect (COMBB (op = a) f)"
  by (metis 0 SigmaD2)
have 2: "f b = a"
  by (metis 1 vimage_Collect_eq singleton_conv2 insert_def Un_empty_right vimage_singleton_eq vimage_def)
assume 3: "a \<notin> A \<or> a \<noteq> f b"
have 4: "a \<in> A"
  by (metis 0 SigmaD1)
have 5: "f b \<noteq> a"
  by (metis 4 3)
show "False"
  by (metis 5 2)
qed


ML{*AtpWrapper.problem_name := "Abstraction__CLF_eq_in_pp"*}
lemma "(cl,f) \<in> CLF ==> CLF = (SIGMA cl: CL.{f. f \<in> pset cl}) ==> f \<in> pset cl"
by (metis Collect_mem_eq SigmaD2)

lemma "(cl,f) \<in> CLF ==> CLF = (SIGMA cl: CL.{f. f \<in> pset cl}) ==> f \<in> pset cl"
proof (neg_clausify)
assume 0: "(cl, f) \<in> CLF"
assume 1: "CLF = Sigma CL (COMBB Collect (COMBB (COMBC op \<in>) pset))"
assume 2: "f \<notin> pset cl"
have 3: "\<And>X1 X2. X2 \<in> COMBB Collect (COMBB (COMBC op \<in>) pset) X1 \<or> (X1, X2) \<notin> CLF"
  by (metis SigmaD2 1)
have 4: "\<And>X1 X2. X2 \<in> pset X1 \<or> (X1, X2) \<notin> CLF"
  by (metis 3 Collect_mem_eq)
have 5: "(cl, f) \<notin> CLF"
  by (metis 2 4)
show "False"
  by (metis 5 0)
qed

ML{*AtpWrapper.problem_name := "Abstraction__Sigma_Collect_Pi"*}
lemma
    "(cl,f) \<in> (SIGMA cl: CL. {f. f \<in> pset cl \<rightarrow> pset cl}) ==> 
    f \<in> pset cl \<rightarrow> pset cl"
proof (neg_clausify)
assume 0: "f \<notin> Pi (pset cl) (COMBK (pset cl))"
assume 1: "(cl, f)
\<in> Sigma CL
   (COMBB Collect
     (COMBB (COMBC op \<in>) (COMBS (COMBB Pi pset) (COMBB COMBK pset))))"
show "False"
(*  by (metis 0 Collect_mem_eq SigmaD2 1) ??doesn't terminate*)
  by (insert 0 1, simp add: COMBB_def COMBS_def COMBC_def)
qed


ML{*AtpWrapper.problem_name := "Abstraction__Sigma_Collect_Int"*}
lemma
    "(cl,f) \<in> (SIGMA cl: CL. {f. f \<in> pset cl \<inter> cl}) ==>
   f \<in> pset cl \<inter> cl"
proof (neg_clausify)
assume 0: "(cl, f)
\<in> Sigma CL
   (COMBB Collect (COMBB (COMBC op \<in>) (COMBS (COMBB op \<inter> pset) COMBI)))"
assume 1: "f \<notin> pset cl \<inter> cl"
have 2: "f \<in> COMBB Collect (COMBB (COMBC op \<in>) (COMBS (COMBB op \<inter> pset) COMBI)) cl" 
  by (insert 0, simp add: COMBB_def) 
(*  by (metis SigmaD2 0)  ??doesn't terminate*)
have 3: "f \<in> COMBS (COMBB op \<inter> pset) COMBI cl"
  by (metis 2 Collect_mem_eq)
have 4: "f \<notin> cl \<inter> pset cl"
  by (metis 1 Int_commute)
have 5: "f \<in> cl \<inter> pset cl"
  by (metis 3 Int_commute)
show "False"
  by (metis 5 4)
qed


ML{*AtpWrapper.problem_name := "Abstraction__Sigma_Collect_Pi_mono"*}
lemma
    "(cl,f) \<in> (SIGMA cl: CL. {f. f \<in> pset cl \<rightarrow> pset cl & monotone f (pset cl) (order cl)}) ==>
   (f \<in> pset cl \<rightarrow> pset cl)  &  (monotone f (pset cl) (order cl))"
by auto

ML{*AtpWrapper.problem_name := "Abstraction__CLF_subset_Collect_Int"*}
lemma "(cl,f) \<in> CLF ==> 
   CLF \<subseteq> (SIGMA cl: CL. {f. f \<in> pset cl \<inter> cl}) ==>
   f \<in> pset cl \<inter> cl"
by auto

(*??no longer terminates, with combinators
by (metis Collect_mem_eq Int_def SigmaD2 UnCI Un_absorb1)
  --{*@{text Int_def} is redundant*}
*)

ML{*AtpWrapper.problem_name := "Abstraction__CLF_eq_Collect_Int"*}
lemma "(cl,f) \<in> CLF ==> 
   CLF = (SIGMA cl: CL. {f. f \<in> pset cl \<inter> cl}) ==>
   f \<in> pset cl \<inter> cl"
by auto
(*??no longer terminates, with combinators
by (metis Collect_mem_eq Int_commute SigmaD2)
*)

ML{*AtpWrapper.problem_name := "Abstraction__CLF_subset_Collect_Pi"*}
lemma 
   "(cl,f) \<in> CLF ==> 
    CLF \<subseteq> (SIGMA cl': CL. {f. f \<in> pset cl' \<rightarrow> pset cl'}) ==> 
    f \<in> pset cl \<rightarrow> pset cl"
by fast
(*??no longer terminates, with combinators
by (metis Collect_mem_eq SigmaD2 subsetD)
*)

ML{*AtpWrapper.problem_name := "Abstraction__CLF_eq_Collect_Pi"*}
lemma 
  "(cl,f) \<in> CLF ==> 
   CLF = (SIGMA cl: CL. {f. f \<in> pset cl \<rightarrow> pset cl}) ==> 
   f \<in> pset cl \<rightarrow> pset cl"
by auto
(*??no longer terminates, with combinators
by (metis Collect_mem_eq SigmaD2 contra_subsetD equalityE)
*)

ML{*AtpWrapper.problem_name := "Abstraction__CLF_eq_Collect_Pi_mono"*}
lemma 
  "(cl,f) \<in> CLF ==> 
   CLF = (SIGMA cl: CL. {f. f \<in> pset cl \<rightarrow> pset cl & monotone f (pset cl) (order cl)}) ==>
   (f \<in> pset cl \<rightarrow> pset cl)  &  (monotone f (pset cl) (order cl))"
by auto

ML{*AtpWrapper.problem_name := "Abstraction__map_eq_zipA"*}
lemma "map (%x. (f x, g x)) xs = zip (map f xs) (map g xs)"
apply (induct xs)
(*sledgehammer*)  
apply auto
done

ML{*AtpWrapper.problem_name := "Abstraction__map_eq_zipB"*}
lemma "map (%w. (w -> w, w \<times> w)) xs = 
       zip (map (%w. w -> w) xs) (map (%w. w \<times> w) xs)"
apply (induct xs)
(*sledgehammer*)  
apply auto
done

ML{*AtpWrapper.problem_name := "Abstraction__image_evenA"*}
lemma "(%x. Suc(f x)) ` {x. even x} <= A ==> (\<forall>x. even x --> Suc(f x) \<in> A)";
(*sledgehammer*)  
by auto

ML{*AtpWrapper.problem_name := "Abstraction__image_evenB"*}
lemma "(%x. f (f x)) ` ((%x. Suc(f x)) ` {x. even x}) <= A 
       ==> (\<forall>x. even x --> f (f (Suc(f x))) \<in> A)";
(*sledgehammer*)  
by auto

ML{*AtpWrapper.problem_name := "Abstraction__image_curry"*}
lemma "f \<in> (%u v. b \<times> u \<times> v) ` A ==> \<forall>u v. P (b \<times> u \<times> v) ==> P(f y)" 
(*sledgehammer*)  
by auto

ML{*AtpWrapper.problem_name := "Abstraction__image_TimesA"*}
lemma image_TimesA: "(%(x,y). (f x, g y)) ` (A \<times> B) = (f`A) \<times> (g`B)"
(*sledgehammer*) 
apply (rule equalityI)
(***Even the two inclusions are far too difficult
ML{*AtpWrapper.problem_name := "Abstraction__image_TimesA_simpler"*}
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

ML{*AtpWrapper.problem_name := "Abstraction__image_TimesB"*}
lemma image_TimesB:
    "(%(x,y,z). (f x, g y, h z)) ` (A \<times> B \<times> C) = (f`A) \<times> (g`B) \<times> (h`C)" 
(*sledgehammer*) 
by force

ML{*AtpWrapper.problem_name := "Abstraction__image_TimesC"*}
lemma image_TimesC:
    "(%(x,y). (x \<rightarrow> x, y \<times> y)) ` (A \<times> B) = 
     ((%x. x \<rightarrow> x) ` A) \<times> ((%y. y \<times> y) ` B)" 
(*sledgehammer*) 
by auto

end
