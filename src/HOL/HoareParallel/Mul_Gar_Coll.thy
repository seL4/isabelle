
header {* \section{The Multi-Mutator Case} *}

theory Mul_Gar_Coll = Graph + OG_Syntax:

text {*  The full theory takes aprox. 18 minutes.  *}

record mut =
  Z :: bool
  R :: nat
  T :: nat

text {* Declaration of variables: *}

record mul_gar_coll_state =
  M :: nodes
  E :: edges
  bc :: "nat set"
  obc :: "nat set"
  Ma :: nodes
  ind :: nat 
  k :: nat
  q :: nat
  l :: nat
  Muts :: "mut list"

subsection {* The Mutators *}

constdefs 
  Mul_mut_init :: "mul_gar_coll_state \<Rightarrow> nat \<Rightarrow> bool"
  "Mul_mut_init \<equiv> \<guillemotleft> \<lambda>n. n=length \<acute>Muts \<and> (\<forall>i<n. R (\<acute>Muts!i)<length \<acute>E 
                          \<and> T (\<acute>Muts!i)<length \<acute>M) \<guillemotright>"

  Mul_Redirect_Edge  :: "nat \<Rightarrow> nat \<Rightarrow> mul_gar_coll_state ann_com"
  "Mul_Redirect_Edge j n \<equiv>
  .{\<acute>Mul_mut_init n \<and> Z (\<acute>Muts!j)}.
  \<langle>IF T(\<acute>Muts!j) \<in> Reach \<acute>E THEN  
  \<acute>E:= \<acute>E[R (\<acute>Muts!j):= (fst (\<acute>E!R(\<acute>Muts!j)), T (\<acute>Muts!j))] FI,, 
  \<acute>Muts:= \<acute>Muts[j:= (\<acute>Muts!j) \<lparr>Z:=False\<rparr>]\<rangle>"

  Mul_Color_Target :: "nat \<Rightarrow> nat \<Rightarrow> mul_gar_coll_state ann_com"
  "Mul_Color_Target j n \<equiv>
  .{\<acute>Mul_mut_init n \<and> \<not> Z (\<acute>Muts!j)}. 
  \<langle>\<acute>M:=\<acute>M[T (\<acute>Muts!j):=Black],, \<acute>Muts:=\<acute>Muts[j:= (\<acute>Muts!j) \<lparr>Z:=True\<rparr>]\<rangle>"

  Mul_Mutator :: "nat \<Rightarrow> nat \<Rightarrow>  mul_gar_coll_state ann_com"
  "Mul_Mutator j n \<equiv>
  .{\<acute>Mul_mut_init n \<and> Z (\<acute>Muts!j)}.  
  WHILE True  
    INV .{\<acute>Mul_mut_init n \<and> Z (\<acute>Muts!j)}.  
  DO Mul_Redirect_Edge j n ;; 
     Mul_Color_Target j n 
  OD"

lemmas mul_mutator_defs = Mul_mut_init_def Mul_Redirect_Edge_def Mul_Color_Target_def 

subsubsection {* Correctness of the proof outline of one mutator *}

lemma Mul_Redirect_Edge: "0\<le>j \<and> j<n \<Longrightarrow> 
  \<turnstile> Mul_Redirect_Edge j n 
     pre(Mul_Color_Target j n)"
apply (unfold mul_mutator_defs)
apply annhoare
apply(simp_all)
apply clarify
apply(simp add:nth_list_update)
done

lemma Mul_Color_Target: "0\<le>j \<and> j<n \<Longrightarrow> 
  \<turnstile>  Mul_Color_Target j n  
    .{\<acute>Mul_mut_init n \<and> Z (\<acute>Muts!j)}."
apply (unfold mul_mutator_defs)
apply annhoare
apply(simp_all)
apply clarify
apply(simp add:nth_list_update)
done

lemma Mul_Mutator: "0\<le>j \<and> j<n \<Longrightarrow>  
 \<turnstile> Mul_Mutator j n .{False}."
apply(unfold Mul_Mutator_def)
apply annhoare
apply(simp_all add:Mul_Redirect_Edge Mul_Color_Target)
apply(simp add:mul_mutator_defs Mul_Redirect_Edge_def)
done

subsubsection {* Interference freedom between mutators *}

lemma Mul_interfree_Redirect_Edge_Redirect_Edge: 
  "\<lbrakk>0\<le>i; i<n; 0\<le>j; j<n; i\<noteq>j\<rbrakk> \<Longrightarrow>  
  interfree_aux (Some (Mul_Redirect_Edge i n),{}, Some(Mul_Redirect_Edge j n))"
apply (unfold mul_mutator_defs)
apply interfree_aux
apply safe
apply(simp_all add: nth_list_update)
done

lemma Mul_interfree_Redirect_Edge_Color_Target: 
  "\<lbrakk>0\<le>i; i<n; 0\<le>j; j<n; i\<noteq>j\<rbrakk> \<Longrightarrow>  
  interfree_aux (Some(Mul_Redirect_Edge i n),{},Some(Mul_Color_Target j n))"
apply (unfold mul_mutator_defs)
apply interfree_aux
apply safe
apply(simp_all add: nth_list_update)
done

lemma Mul_interfree_Color_Target_Redirect_Edge: 
  "\<lbrakk>0\<le>i; i<n; 0\<le>j; j<n; i\<noteq>j\<rbrakk> \<Longrightarrow> 
  interfree_aux (Some(Mul_Color_Target i n),{},Some(Mul_Redirect_Edge j n))"
apply (unfold mul_mutator_defs)
apply interfree_aux
apply safe
apply(simp_all add:nth_list_update)
done

lemma Mul_interfree_Color_Target_Color_Target: 
  " \<lbrakk>0\<le>i; i<n; 0\<le>j; j<n; i\<noteq>j\<rbrakk> \<Longrightarrow> 
  interfree_aux (Some(Mul_Color_Target i n),{},Some(Mul_Color_Target j n))"
apply (unfold mul_mutator_defs)
apply interfree_aux
apply safe
apply(simp_all add: nth_list_update)
done

lemmas mul_mutator_interfree = 
  Mul_interfree_Redirect_Edge_Redirect_Edge Mul_interfree_Redirect_Edge_Color_Target
  Mul_interfree_Color_Target_Redirect_Edge Mul_interfree_Color_Target_Color_Target

lemma Mul_interfree_Mutator_Mutator: "\<lbrakk>i < n; j < n; i \<noteq> j\<rbrakk> \<Longrightarrow> 
  interfree_aux (Some (Mul_Mutator i n), {}, Some (Mul_Mutator j n))"
apply(unfold Mul_Mutator_def)
apply(interfree_aux)
apply(simp_all add:mul_mutator_interfree)
apply(simp_all add: mul_mutator_defs)
apply(tactic {* TRYALL (interfree_aux_tac) *})
apply(tactic {* ALLGOALS Clarify_tac *})
apply (simp_all add:nth_list_update)
done

subsubsection {* Modular Parameterized Mutators *}

lemma Mul_Parameterized_Mutators: "0<n \<Longrightarrow>
 \<parallel>- .{\<acute>Mul_mut_init n \<and> (\<forall>i<n. Z (\<acute>Muts!i))}.
 COBEGIN
 SCHEME  [0\<le> j< n]
  Mul_Mutator j n
 .{False}.
 COEND
 .{False}."
apply oghoare
apply(force simp add:Mul_Mutator_def mul_mutator_defs nth_list_update)
apply(erule Mul_Mutator)
apply(simp add:Mul_interfree_Mutator_Mutator)
apply(force simp add:Mul_Mutator_def mul_mutator_defs nth_list_update)
done

subsection {* The Collector *}

constdefs
  Queue :: "mul_gar_coll_state \<Rightarrow> nat"
 "Queue \<equiv> \<guillemotleft> length (filter (\<lambda>i. \<not> Z i \<and> \<acute>M!(T i) \<noteq> Black) \<acute>Muts) \<guillemotright>"

consts  M_init :: nodes

constdefs
  Proper_M_init :: "mul_gar_coll_state \<Rightarrow> bool"
  "Proper_M_init \<equiv> \<guillemotleft> Blacks M_init=Roots \<and> length M_init=length \<acute>M \<guillemotright>"

  Mul_Proper :: "mul_gar_coll_state \<Rightarrow> nat \<Rightarrow> bool"
  "Mul_Proper \<equiv> \<guillemotleft> \<lambda>n. Proper_Roots \<acute>M \<and> Proper_Edges (\<acute>M, \<acute>E) \<and> \<acute>Proper_M_init \<and> n=length \<acute>Muts \<guillemotright>"

  Safe :: "mul_gar_coll_state \<Rightarrow> bool"
  "Safe \<equiv> \<guillemotleft> Reach \<acute>E \<subseteq> Blacks \<acute>M \<guillemotright>"

lemmas mul_collector_defs = Proper_M_init_def Mul_Proper_def Safe_def

subsubsection {* Blackening Roots *}

constdefs
  Mul_Blacken_Roots :: "nat \<Rightarrow>  mul_gar_coll_state ann_com"
  "Mul_Blacken_Roots n \<equiv>
  .{\<acute>Mul_Proper n}.
  \<acute>ind:=0;;
  .{\<acute>Mul_Proper n \<and> \<acute>ind=0}.
  WHILE \<acute>ind<length \<acute>M 
    INV .{\<acute>Mul_Proper n \<and> (\<forall>i<\<acute>ind. i\<in>Roots \<longrightarrow> \<acute>M!i=Black) \<and> \<acute>ind\<le>length \<acute>M}.
  DO .{\<acute>Mul_Proper n \<and> (\<forall>i<\<acute>ind. i\<in>Roots \<longrightarrow> \<acute>M!i=Black) \<and> \<acute>ind<length \<acute>M}.
       IF \<acute>ind\<in>Roots THEN 
     .{\<acute>Mul_Proper n \<and> (\<forall>i<\<acute>ind. i\<in>Roots \<longrightarrow> \<acute>M!i=Black) \<and> \<acute>ind<length \<acute>M \<and> \<acute>ind\<in>Roots}. 
       \<acute>M:=\<acute>M[\<acute>ind:=Black] FI;;
     .{\<acute>Mul_Proper n \<and> (\<forall>i<\<acute>ind+1. i\<in>Roots \<longrightarrow> \<acute>M!i=Black) \<and> \<acute>ind<length \<acute>M}.
       \<acute>ind:=\<acute>ind+1 
  OD"

lemma Mul_Blacken_Roots: 
  "\<turnstile> Mul_Blacken_Roots n  
  .{\<acute>Mul_Proper n \<and> Roots \<subseteq> Blacks \<acute>M}."
apply (unfold Mul_Blacken_Roots_def)
apply annhoare
apply(simp_all add:mul_collector_defs Graph_defs)
apply safe
apply(simp_all add:nth_list_update)
  apply (erule less_SucE)
   apply simp+
 apply(drule le_imp_less_or_eq)
 apply force
apply force
done

subsubsection {* Propagating Black *} 

constdefs
  Mul_PBInv :: "mul_gar_coll_state \<Rightarrow> bool"
  "Mul_PBInv \<equiv>  \<guillemotleft>\<acute>Safe \<or> \<acute>obc\<subset>Blacks \<acute>M \<or> \<acute>l<\<acute>Queue 
                 \<or> (\<forall>i<\<acute>ind. \<not>BtoW(\<acute>E!i,\<acute>M)) \<and> \<acute>l\<le>\<acute>Queue\<guillemotright>"

  Mul_Auxk :: "mul_gar_coll_state \<Rightarrow> bool"
  "Mul_Auxk \<equiv> \<guillemotleft>\<acute>l<\<acute>Queue \<or> \<acute>M!\<acute>k\<noteq>Black \<or> \<not>BtoW(\<acute>E!\<acute>ind, \<acute>M) \<or> \<acute>obc\<subset>Blacks \<acute>M\<guillemotright>"

constdefs
  Mul_Propagate_Black :: "nat \<Rightarrow>  mul_gar_coll_state ann_com"
  "Mul_Propagate_Black n \<equiv>
 .{\<acute>Mul_Proper n \<and> Roots\<subseteq>Blacks \<acute>M \<and> \<acute>obc\<subseteq>Blacks \<acute>M \<and> \<acute>bc\<subseteq>Blacks \<acute>M 
  \<and> (\<acute>Safe \<or> \<acute>l\<le>\<acute>Queue \<or> \<acute>obc\<subset>Blacks \<acute>M)}. 
 \<acute>ind:=0;;
 .{\<acute>Mul_Proper n \<and> Roots\<subseteq>Blacks \<acute>M 
   \<and> \<acute>obc\<subseteq>Blacks \<acute>M \<and> Blacks \<acute>M\<subseteq>Blacks \<acute>M \<and> \<acute>bc\<subseteq>Blacks \<acute>M 
   \<and> (\<acute>Safe \<or> \<acute>l\<le>\<acute>Queue \<or> \<acute>obc\<subset>Blacks \<acute>M) \<and> \<acute>ind=0}. 
 WHILE \<acute>ind<length \<acute>E 
  INV .{\<acute>Mul_Proper n \<and> Roots\<subseteq>Blacks \<acute>M 
        \<and> \<acute>obc\<subseteq>Blacks \<acute>M \<and> \<acute>bc\<subseteq>Blacks \<acute>M 
        \<and> \<acute>Mul_PBInv \<and> \<acute>ind\<le>length \<acute>E}.
 DO .{\<acute>Mul_Proper n \<and> Roots\<subseteq>Blacks \<acute>M 
     \<and> \<acute>obc\<subseteq>Blacks \<acute>M \<and> \<acute>bc\<subseteq>Blacks \<acute>M 
     \<and> \<acute>Mul_PBInv \<and> \<acute>ind<length \<acute>E}.
   IF \<acute>M!(fst (\<acute>E!\<acute>ind))=Black THEN 
   .{\<acute>Mul_Proper n \<and> Roots\<subseteq>Blacks \<acute>M 
     \<and> \<acute>obc\<subseteq>Blacks \<acute>M \<and> \<acute>bc\<subseteq>Blacks \<acute>M 
     \<and> \<acute>Mul_PBInv \<and> (\<acute>M!fst(\<acute>E!\<acute>ind))=Black \<and> \<acute>ind<length \<acute>E}.
    \<acute>k:=snd(\<acute>E!\<acute>ind);;
   .{\<acute>Mul_Proper n \<and> Roots\<subseteq>Blacks \<acute>M 
     \<and> \<acute>obc\<subseteq>Blacks \<acute>M \<and> \<acute>bc\<subseteq>Blacks \<acute>M 
     \<and> (\<acute>Safe \<or> \<acute>obc\<subset>Blacks \<acute>M \<or> \<acute>l<\<acute>Queue \<or> (\<forall>i<\<acute>ind. \<not>BtoW(\<acute>E!i,\<acute>M)) 
        \<and> \<acute>l\<le>\<acute>Queue \<and> \<acute>Mul_Auxk ) \<and> \<acute>k<length \<acute>M \<and> \<acute>M!fst(\<acute>E!\<acute>ind)=Black 
     \<and> \<acute>ind<length \<acute>E}.
   \<langle>\<acute>M:=\<acute>M[\<acute>k:=Black],,\<acute>ind:=\<acute>ind+1\<rangle>
   ELSE .{\<acute>Mul_Proper n \<and> Roots\<subseteq>Blacks \<acute>M 
         \<and> \<acute>obc\<subseteq>Blacks \<acute>M \<and> \<acute>bc\<subseteq>Blacks \<acute>M 
         \<and> \<acute>Mul_PBInv \<and> \<acute>ind<length \<acute>E}.
	 \<langle>IF \<acute>M!(fst (\<acute>E!\<acute>ind))\<noteq>Black THEN \<acute>ind:=\<acute>ind+1 FI\<rangle> FI
 OD"

lemma Mul_Propagate_Black: 
  "\<turnstile> Mul_Propagate_Black n  
   .{\<acute>Mul_Proper n \<and> Roots\<subseteq>Blacks \<acute>M \<and> \<acute>obc\<subseteq>Blacks \<acute>M \<and> \<acute>bc\<subseteq>Blacks \<acute>M 
     \<and> (\<acute>Safe \<or> \<acute>obc\<subset>Blacks \<acute>M \<or> \<acute>l<\<acute>Queue \<and> (\<acute>l\<le>\<acute>Queue \<or> \<acute>obc\<subset>Blacks \<acute>M))}."
apply(unfold Mul_Propagate_Black_def)
apply annhoare
apply(simp_all add:Mul_PBInv_def mul_collector_defs Mul_Auxk_def Graph6 Graph7 Graph8 Graph12 mul_collector_defs Queue_def)
--{* 8 subgoals left *}
apply force
apply force
apply force
apply(force simp add:BtoW_def Graph_defs)
--{* 4 subgoals left *}
apply clarify
apply(simp add: mul_collector_defs Graph12 Graph6 Graph7 Graph8)
apply(disjE_tac)
 apply(simp_all add:Graph12 Graph13)
 apply(case_tac "M x! k x=Black")
  apply(simp add: Graph10)
 apply(rule disjI2, rule disjI1, erule subset_psubset_trans, erule Graph11, force)
apply(case_tac "M x! k x=Black")
 apply(simp add: Graph10 BtoW_def)
 apply(rule disjI2, clarify, erule less_SucE, force)
 apply(case_tac "M x!snd(E x! ind x)=Black")
  apply(force)
 apply(force)
apply(rule disjI2, rule disjI1, erule subset_psubset_trans, erule Graph11, force)
--{* 3 subgoals left *}
apply force
--{* 2 subgoals left *}
apply clarify
apply(conjI_tac)
apply(disjE_tac)
 apply (simp_all)
apply clarify
apply(erule less_SucE)
 apply force
apply (simp add:BtoW_def)
--{* 1 subgoal left *}
apply clarify
apply simp
apply(disjE_tac)
apply (simp_all)
apply(rule disjI1 , rule Graph1)
 apply simp_all
done

subsubsection {* Counting Black Nodes *}

constdefs
  Mul_CountInv :: "mul_gar_coll_state \<Rightarrow> nat \<Rightarrow> bool"
 "Mul_CountInv \<equiv> \<guillemotleft> \<lambda>ind. {i. i<ind \<and> \<acute>Ma!i=Black}\<subseteq>\<acute>bc \<guillemotright>"

  Mul_Count :: "nat \<Rightarrow>  mul_gar_coll_state ann_com"
  "Mul_Count n \<equiv> 
  .{\<acute>Mul_Proper n \<and> Roots\<subseteq>Blacks \<acute>M 
    \<and> \<acute>obc\<subseteq>Blacks \<acute>Ma \<and> Blacks \<acute>Ma\<subseteq>Blacks \<acute>M \<and> \<acute>bc\<subseteq>Blacks \<acute>M 
    \<and> length \<acute>Ma=length \<acute>M 
    \<and> (\<acute>Safe \<or> \<acute>obc\<subset>Blacks \<acute>Ma \<or> \<acute>l<\<acute>q \<and> (\<acute>q\<le>\<acute>Queue \<or> \<acute>obc\<subset>Blacks \<acute>M) ) 
    \<and> \<acute>q<n+1 \<and> \<acute>bc={}}.
  \<acute>ind:=0;;
  .{\<acute>Mul_Proper n \<and> Roots\<subseteq>Blacks \<acute>M 
    \<and> \<acute>obc\<subseteq>Blacks \<acute>Ma \<and> Blacks \<acute>Ma\<subseteq>Blacks \<acute>M \<and> \<acute>bc\<subseteq>Blacks \<acute>M 
    \<and> length \<acute>Ma=length \<acute>M 
    \<and> (\<acute>Safe \<or> \<acute>obc\<subset>Blacks \<acute>Ma \<or> \<acute>l<\<acute>q \<and> (\<acute>q\<le>\<acute>Queue \<or> \<acute>obc\<subset>Blacks \<acute>M) ) 
    \<and> \<acute>q<n+1 \<and> \<acute>bc={} \<and> \<acute>ind=0}.
  WHILE \<acute>ind<length \<acute>M 
     INV .{\<acute>Mul_Proper n \<and> Roots\<subseteq>Blacks \<acute>M 
          \<and> \<acute>obc\<subseteq>Blacks \<acute>Ma \<and> Blacks \<acute>Ma\<subseteq>Blacks \<acute>M \<and> \<acute>bc\<subseteq>Blacks \<acute>M  
          \<and> length \<acute>Ma=length \<acute>M \<and> \<acute>Mul_CountInv \<acute>ind 
          \<and> (\<acute>Safe \<or> \<acute>obc\<subset>Blacks \<acute>Ma \<or> \<acute>l<\<acute>q \<and> (\<acute>q\<le>\<acute>Queue \<or> \<acute>obc\<subset>Blacks \<acute>M))
	  \<and> \<acute>q<n+1 \<and> \<acute>ind\<le>length \<acute>M}.
  DO .{\<acute>Mul_Proper n \<and> Roots\<subseteq>Blacks \<acute>M 
       \<and> \<acute>obc\<subseteq>Blacks \<acute>Ma \<and> Blacks \<acute>Ma\<subseteq>Blacks \<acute>M \<and> \<acute>bc\<subseteq>Blacks \<acute>M 
       \<and> length \<acute>Ma=length \<acute>M \<and> \<acute>Mul_CountInv \<acute>ind 
       \<and> (\<acute>Safe \<or> \<acute>obc\<subset>Blacks \<acute>Ma \<or> \<acute>l<\<acute>q \<and> (\<acute>q\<le>\<acute>Queue \<or> \<acute>obc\<subset>Blacks \<acute>M))
       \<and> \<acute>q<n+1 \<and> \<acute>ind<length \<acute>M}. 
     IF \<acute>M!\<acute>ind=Black 
     THEN .{\<acute>Mul_Proper n \<and> Roots\<subseteq>Blacks \<acute>M 
            \<and> \<acute>obc\<subseteq>Blacks \<acute>Ma \<and> Blacks \<acute>Ma\<subseteq>Blacks \<acute>M \<and> \<acute>bc\<subseteq>Blacks \<acute>M  
            \<and> length \<acute>Ma=length \<acute>M \<and> \<acute>Mul_CountInv \<acute>ind 
            \<and> (\<acute>Safe \<or> \<acute>obc\<subset>Blacks \<acute>Ma \<or> \<acute>l<\<acute>q \<and> (\<acute>q\<le>\<acute>Queue \<or> \<acute>obc\<subset>Blacks \<acute>M))
            \<and> \<acute>q<n+1 \<and> \<acute>ind<length \<acute>M \<and> \<acute>M!\<acute>ind=Black}.
          \<acute>bc:=insert \<acute>ind \<acute>bc
     FI;;
  .{\<acute>Mul_Proper n \<and> Roots\<subseteq>Blacks \<acute>M 
    \<and> \<acute>obc\<subseteq>Blacks \<acute>Ma \<and> Blacks \<acute>Ma\<subseteq>Blacks \<acute>M \<and> \<acute>bc\<subseteq>Blacks \<acute>M 
    \<and> length \<acute>Ma=length \<acute>M \<and> \<acute>Mul_CountInv (\<acute>ind+1) 
    \<and> (\<acute>Safe \<or> \<acute>obc\<subset>Blacks \<acute>Ma \<or> \<acute>l<\<acute>q \<and> (\<acute>q\<le>\<acute>Queue \<or> \<acute>obc\<subset>Blacks \<acute>M))
    \<and> \<acute>q<n+1 \<and> \<acute>ind<length \<acute>M}.
  \<acute>ind:=\<acute>ind+1
  OD"
 
lemma Mul_Count: 
  "\<turnstile> Mul_Count n  
  .{\<acute>Mul_Proper n \<and> Roots\<subseteq>Blacks \<acute>M 
    \<and> \<acute>obc\<subseteq>Blacks \<acute>Ma \<and> Blacks \<acute>Ma\<subseteq>Blacks \<acute>M \<and> \<acute>bc\<subseteq>Blacks \<acute>M 
    \<and> length \<acute>Ma=length \<acute>M \<and> Blacks \<acute>Ma\<subseteq>\<acute>bc 
    \<and> (\<acute>Safe \<or> \<acute>obc\<subset>Blacks \<acute>Ma \<or> \<acute>l<\<acute>q \<and> (\<acute>q\<le>\<acute>Queue \<or> \<acute>obc\<subset>Blacks \<acute>M)) 
    \<and> \<acute>q<n+1}."
apply (unfold Mul_Count_def)
apply annhoare
apply(simp_all add:Mul_CountInv_def mul_collector_defs Mul_Auxk_def Graph6 Graph7 Graph8 Graph12 mul_collector_defs Queue_def)
--{* 7 subgoals left *}
apply force
apply force
apply force
--{* 4 subgoals left *}
apply clarify
apply(conjI_tac)
apply(disjE_tac)
 apply simp_all
apply(simp add:Blacks_def)
apply clarify
apply(erule less_SucE)
 back
 apply force
apply force
--{* 3 subgoals left *}
apply clarify
apply(conjI_tac)
apply(disjE_tac)
 apply simp_all
apply clarify
apply(erule less_SucE)
 back
 apply force
apply simp
apply(rotate_tac -1)
apply (force simp add:Blacks_def)
--{* 2 subgoals left *}
apply force
--{* 1 subgoal left *}
apply clarify
apply(drule le_imp_less_or_eq)
apply(disjE_tac)
apply (simp_all add:Blacks_def)
done

subsubsection {* Appending garbage nodes to the free list *}

consts  Append_to_free :: "nat \<times> edges \<Rightarrow> edges"

axioms
  Append_to_free0: "length (Append_to_free (i, e)) = length e"
  Append_to_free1: "Proper_Edges (m, e) 
                    \<Longrightarrow> Proper_Edges (m, Append_to_free(i, e))"
  Append_to_free2: "i \<notin> Reach e 
           \<Longrightarrow> n \<in> Reach (Append_to_free(i, e)) = ( n = i \<or> n \<in> Reach e)"

constdefs
  Mul_AppendInv :: "mul_gar_coll_state \<Rightarrow> nat \<Rightarrow> bool"
  "Mul_AppendInv \<equiv> \<guillemotleft> \<lambda>ind. (\<forall>i. ind\<le>i \<longrightarrow> i<length \<acute>M \<longrightarrow> i\<in>Reach \<acute>E \<longrightarrow> \<acute>M!i=Black)\<guillemotright>"

  Mul_Append :: "nat \<Rightarrow>  mul_gar_coll_state ann_com"
  "Mul_Append n \<equiv> 
  .{\<acute>Mul_Proper n \<and> Roots\<subseteq>Blacks \<acute>M \<and> \<acute>Safe}.
  \<acute>ind:=0;;
  .{\<acute>Mul_Proper n \<and> Roots\<subseteq>Blacks \<acute>M \<and> \<acute>Safe \<and> \<acute>ind=0}.
  WHILE \<acute>ind<length \<acute>M 
    INV .{\<acute>Mul_Proper n \<and> \<acute>Mul_AppendInv \<acute>ind \<and> \<acute>ind\<le>length \<acute>M}.
  DO .{\<acute>Mul_Proper n \<and> \<acute>Mul_AppendInv \<acute>ind \<and> \<acute>ind<length \<acute>M}.
      IF \<acute>M!\<acute>ind=Black THEN 
     .{\<acute>Mul_Proper n \<and> \<acute>Mul_AppendInv \<acute>ind \<and> \<acute>ind<length \<acute>M \<and> \<acute>M!\<acute>ind=Black}. 
      \<acute>M:=\<acute>M[\<acute>ind:=White] 
      ELSE 
     .{\<acute>Mul_Proper n \<and> \<acute>Mul_AppendInv \<acute>ind \<and> \<acute>ind<length \<acute>M \<and> \<acute>ind\<notin>Reach \<acute>E}. 
      \<acute>E:=Append_to_free(\<acute>ind,\<acute>E)
      FI;;
  .{\<acute>Mul_Proper n \<and> \<acute>Mul_AppendInv (\<acute>ind+1) \<and> \<acute>ind<length \<acute>M}. 
   \<acute>ind:=\<acute>ind+1
  OD"

lemma Mul_Append: 
  "\<turnstile> Mul_Append n  
     .{\<acute>Mul_Proper n}."
apply(unfold Mul_Append_def)
apply annhoare
apply(simp_all add: mul_collector_defs Mul_AppendInv_def 
      Graph6 Graph7 Graph8 Append_to_free0 Append_to_free1 Graph12)
apply(force simp add:Blacks_def)
apply(force simp add:Blacks_def)
apply(force simp add:Blacks_def)
apply(force simp add:Graph_defs)
apply force
apply(force simp add:Append_to_free1 Append_to_free2)
apply force
apply force
done

subsubsection {* Collector *}

constdefs 
  Mul_Collector :: "nat \<Rightarrow>  mul_gar_coll_state ann_com"
  "Mul_Collector n \<equiv>
.{\<acute>Mul_Proper n}.  
WHILE True INV .{\<acute>Mul_Proper n}. 
DO  
Mul_Blacken_Roots n ;; 
.{\<acute>Mul_Proper n \<and> Roots\<subseteq>Blacks \<acute>M}.  
 \<acute>obc:={};; 
.{\<acute>Mul_Proper n \<and> Roots\<subseteq>Blacks \<acute>M \<and> \<acute>obc={}}.  
 \<acute>bc:=Roots;; 
.{\<acute>Mul_Proper n \<and> Roots\<subseteq>Blacks \<acute>M \<and> \<acute>obc={} \<and> \<acute>bc=Roots}. 
 \<acute>l:=0;; 
.{\<acute>Mul_Proper n \<and> Roots\<subseteq>Blacks \<acute>M \<and> \<acute>obc={} \<and> \<acute>bc=Roots \<and> \<acute>l=0}. 
 WHILE \<acute>l<n+1  
   INV .{\<acute>Mul_Proper n \<and> Roots\<subseteq>Blacks \<acute>M \<and> \<acute>bc\<subseteq>Blacks \<acute>M \<and>  
         (\<acute>Safe \<or> (\<acute>l\<le>\<acute>Queue \<or> \<acute>bc\<subset>Blacks \<acute>M) \<and> \<acute>l<n+1)}. 
 DO .{\<acute>Mul_Proper n \<and> Roots\<subseteq>Blacks \<acute>M \<and> \<acute>bc\<subseteq>Blacks \<acute>M 
      \<and> (\<acute>Safe \<or> \<acute>l\<le>\<acute>Queue \<or> \<acute>bc\<subset>Blacks \<acute>M)}.
    \<acute>obc:=\<acute>bc;;
    Mul_Propagate_Black n;; 
    .{\<acute>Mul_Proper n \<and> Roots\<subseteq>Blacks \<acute>M 
      \<and> \<acute>obc\<subseteq>Blacks \<acute>M \<and> \<acute>bc\<subseteq>Blacks \<acute>M 
      \<and> (\<acute>Safe \<or> \<acute>obc\<subset>Blacks \<acute>M \<or> \<acute>l<\<acute>Queue 
      \<and> (\<acute>l\<le>\<acute>Queue \<or> \<acute>obc\<subset>Blacks \<acute>M))}. 
    \<acute>bc:={};;
    .{\<acute>Mul_Proper n \<and> Roots\<subseteq>Blacks \<acute>M 
      \<and> \<acute>obc\<subseteq>Blacks \<acute>M \<and> \<acute>bc\<subseteq>Blacks \<acute>M 
      \<and> (\<acute>Safe \<or> \<acute>obc\<subset>Blacks \<acute>M \<or> \<acute>l<\<acute>Queue 
      \<and> (\<acute>l\<le>\<acute>Queue \<or> \<acute>obc\<subset>Blacks \<acute>M)) \<and> \<acute>bc={}}. 
       \<langle> \<acute>Ma:=\<acute>M,, \<acute>q:=\<acute>Queue \<rangle>;;
    Mul_Count n;; 
    .{\<acute>Mul_Proper n \<and> Roots\<subseteq>Blacks \<acute>M 
      \<and> \<acute>obc\<subseteq>Blacks \<acute>Ma \<and> Blacks \<acute>Ma\<subseteq>Blacks \<acute>M \<and> \<acute>bc\<subseteq>Blacks \<acute>M 
      \<and> length \<acute>Ma=length \<acute>M \<and> Blacks \<acute>Ma\<subseteq>\<acute>bc 
      \<and> (\<acute>Safe \<or> \<acute>obc\<subset>Blacks \<acute>Ma \<or> \<acute>l<\<acute>q \<and> (\<acute>q\<le>\<acute>Queue \<or> \<acute>obc\<subset>Blacks \<acute>M)) 
      \<and> \<acute>q<n+1}. 
    IF \<acute>obc=\<acute>bc THEN
    .{\<acute>Mul_Proper n \<and> Roots\<subseteq>Blacks \<acute>M 
      \<and> \<acute>obc\<subseteq>Blacks \<acute>Ma \<and> Blacks \<acute>Ma\<subseteq>Blacks \<acute>M \<and> \<acute>bc\<subseteq>Blacks \<acute>M 
      \<and> length \<acute>Ma=length \<acute>M \<and> Blacks \<acute>Ma\<subseteq>\<acute>bc 
      \<and> (\<acute>Safe \<or> \<acute>obc\<subset>Blacks \<acute>Ma \<or> \<acute>l<\<acute>q \<and> (\<acute>q\<le>\<acute>Queue \<or> \<acute>obc\<subset>Blacks \<acute>M)) 
      \<and> \<acute>q<n+1 \<and> \<acute>obc=\<acute>bc}.  
    \<acute>l:=\<acute>l+1  
    ELSE .{\<acute>Mul_Proper n \<and> Roots\<subseteq>Blacks \<acute>M 
          \<and> \<acute>obc\<subseteq>Blacks \<acute>Ma \<and> Blacks \<acute>Ma\<subseteq>Blacks \<acute>M \<and> \<acute>bc\<subseteq>Blacks \<acute>M 
          \<and> length \<acute>Ma=length \<acute>M \<and> Blacks \<acute>Ma\<subseteq>\<acute>bc 
          \<and> (\<acute>Safe \<or> \<acute>obc\<subset>Blacks \<acute>Ma \<or> \<acute>l<\<acute>q \<and> (\<acute>q\<le>\<acute>Queue \<or> \<acute>obc\<subset>Blacks \<acute>M)) 
          \<and> \<acute>q<n+1 \<and> \<acute>obc\<noteq>\<acute>bc}.  
        \<acute>l:=0 FI 
 OD;; 
 Mul_Append n  
OD"

lemmas mul_modules = Mul_Redirect_Edge_def Mul_Color_Target_def 
 Mul_Blacken_Roots_def Mul_Propagate_Black_def 
 Mul_Count_def Mul_Append_def

lemma Mul_Collector:
  "\<turnstile> Mul_Collector n 
  .{False}."
apply(unfold Mul_Collector_def)
apply annhoare
apply(simp_all only:pre.simps Mul_Blacken_Roots 
       Mul_Propagate_Black Mul_Count Mul_Append)
apply(simp_all add:mul_modules)
apply(simp_all add:mul_collector_defs Queue_def)
apply force
apply force
apply force
apply (force simp add: less_Suc_eq_le length_filter)
apply force
apply (force dest:subset_antisym)
apply force
apply force
apply force
done

subsection {* Interference Freedom *}

lemma le_length_filter_update[rule_format]: 
 "\<forall>i. (\<not>P (list!i) \<or> P j) \<and> i<length list 
 \<longrightarrow> length(filter P list) \<le> length(filter P (list[i:=j]))"
apply(induct_tac "list")
 apply(simp)
apply(clarify)
apply(case_tac i)
 apply(simp)
apply(simp)
done

lemma less_length_filter_update [rule_format]: 
 "\<forall>i. P j \<and> \<not>(P (list!i)) \<and> i<length list 
 \<longrightarrow> length(filter P list) < length(filter P (list[i:=j]))"
apply(induct_tac "list")
 apply(simp)
apply(clarify)
apply(case_tac i)
 apply(simp)
apply(simp)
done

lemma Mul_interfree_Blacken_Roots_Redirect_Edge: "\<lbrakk>0\<le>j; j<n\<rbrakk> \<Longrightarrow>  
  interfree_aux (Some(Mul_Blacken_Roots n),{},Some(Mul_Redirect_Edge j n))"
apply (unfold mul_modules)
apply interfree_aux
apply safe
apply(simp_all add:Graph6 Graph9 Graph12 nth_list_update mul_mutator_defs mul_collector_defs)
done

lemma Mul_interfree_Redirect_Edge_Blacken_Roots: "\<lbrakk>0\<le>j; j<n\<rbrakk>\<Longrightarrow> 
  interfree_aux (Some(Mul_Redirect_Edge j n ),{},Some (Mul_Blacken_Roots n))"
apply (unfold mul_modules)
apply interfree_aux
apply safe
apply(simp_all add:mul_mutator_defs nth_list_update)
done

lemma Mul_interfree_Blacken_Roots_Color_Target: "\<lbrakk>0\<le>j; j<n\<rbrakk>\<Longrightarrow>  
  interfree_aux (Some(Mul_Blacken_Roots n),{},Some (Mul_Color_Target j n ))"
apply (unfold mul_modules)
apply interfree_aux
apply safe
apply(simp_all add:mul_mutator_defs mul_collector_defs nth_list_update Graph7 Graph8 Graph9 Graph12)
done

lemma Mul_interfree_Color_Target_Blacken_Roots: "\<lbrakk>0\<le>j; j<n\<rbrakk>\<Longrightarrow>  
  interfree_aux (Some(Mul_Color_Target j n ),{},Some (Mul_Blacken_Roots n ))"
apply (unfold mul_modules)
apply interfree_aux
apply safe
apply(simp_all add:mul_mutator_defs nth_list_update)
done

lemma Mul_interfree_Propagate_Black_Redirect_Edge: "\<lbrakk>0\<le>j; j<n\<rbrakk>\<Longrightarrow>  
  interfree_aux (Some(Mul_Propagate_Black n),{},Some (Mul_Redirect_Edge j n ))"
apply (unfold mul_modules)
apply interfree_aux
apply(simp_all add:mul_mutator_defs mul_collector_defs Mul_PBInv_def nth_list_update Graph6)
--{* 7 subgoals left *}
apply clarify
apply(disjE_tac)
  apply(simp_all add:Graph6)
 apply(rule impI,rule disjI1,rule subset_trans,erule Graph3,simp,simp)
apply(rule conjI)
 apply(rule impI,rule disjI2,rule disjI1,erule le_trans,force simp add:Queue_def less_Suc_eq_le le_length_filter_update)
apply(rule impI,rule disjI2,rule disjI1,erule le_trans,force simp add:Queue_def less_Suc_eq_le le_length_filter_update)
--{* 6 subgoals left *}
apply clarify
apply(disjE_tac)
  apply(simp_all add:Graph6)
 apply(rule impI,rule disjI1,rule subset_trans,erule Graph3,simp,simp)
apply(rule conjI)
 apply(rule impI,rule disjI2,rule disjI1,erule le_trans,force simp add:Queue_def less_Suc_eq_le le_length_filter_update)
apply(rule impI,rule disjI2,rule disjI1,erule le_trans,force simp add:Queue_def less_Suc_eq_le le_length_filter_update)
--{* 5 subgoals left *}
apply clarify
apply(disjE_tac)
  apply(simp_all add:Graph6)
 apply(rule impI,rule disjI1,rule subset_trans,erule Graph3,simp,simp)
apply(rule conjI)
 apply(rule impI,rule disjI2,rule disjI2,rule disjI1,erule less_le_trans,force simp add:Queue_def less_Suc_eq_le le_length_filter_update)
apply(rule impI,rule disjI2,rule disjI2,rule disjI1,erule less_le_trans,force simp add:Queue_def less_Suc_eq_le le_length_filter_update)
apply(erule conjE)
apply(case_tac "M x!(T (Muts x!j))=Black")
 apply(rule conjI)
  apply(rule impI,(rule disjI2)+,rule conjI)
   apply clarify
   apply(case_tac "R (Muts x! j)=i")
    apply (force simp add: nth_list_update BtoW_def)
   apply (force simp add: nth_list_update)
  apply(erule le_trans,force simp add:Queue_def less_Suc_eq_le le_length_filter_update)
 apply(rule impI,(rule disjI2)+, erule le_trans)
 apply(force simp add:Queue_def less_Suc_eq_le le_length_filter_update)
apply(rule conjI)
 apply(rule impI,rule disjI2,rule disjI2,rule disjI1, erule le_less_trans)
 apply(force simp add:Queue_def less_Suc_eq_le less_length_filter_update)
apply(rule impI,rule disjI2,rule disjI2,rule disjI1, erule le_less_trans)
apply(force simp add:Queue_def less_Suc_eq_le less_length_filter_update)
--{* 4 subgoals left *}
apply clarify
apply(disjE_tac)
  apply(simp_all add:Graph6)
 apply(rule impI,rule disjI1,rule subset_trans,erule Graph3,simp,simp)
apply(rule conjI)
 apply(rule impI,rule disjI2,rule disjI2,rule disjI1,erule less_le_trans,force simp add:Queue_def less_Suc_eq_le le_length_filter_update)
apply(rule impI,rule disjI2,rule disjI2,rule disjI1,erule less_le_trans,force simp add:Queue_def less_Suc_eq_le le_length_filter_update)
apply(erule conjE)
apply(case_tac "M x!(T (Muts x!j))=Black")
 apply(rule conjI)
  apply(rule impI,(rule disjI2)+,rule conjI)
   apply clarify
   apply(case_tac "R (Muts x! j)=i")
    apply (force simp add: nth_list_update BtoW_def)
   apply (force simp add: nth_list_update)
  apply(erule le_trans,force simp add:Queue_def less_Suc_eq_le le_length_filter_update)
 apply(rule impI,(rule disjI2)+, erule le_trans)
 apply(force simp add:Queue_def less_Suc_eq_le le_length_filter_update)
apply(rule conjI)
 apply(rule impI,rule disjI2,rule disjI2,rule disjI1, erule le_less_trans)
 apply(force simp add:Queue_def less_Suc_eq_le less_length_filter_update)
apply(rule impI,rule disjI2,rule disjI2,rule disjI1, erule le_less_trans)
apply(force simp add:Queue_def less_Suc_eq_le less_length_filter_update)
--{* 3 subgoals left *}
apply clarify
apply(disjE_tac)
  apply(simp_all add:Graph6)
  apply (rule impI)
   apply(rule conjI)
    apply(rule disjI1,rule subset_trans,erule Graph3,simp,simp)
   apply(case_tac "R (Muts x ! j)= ind x")
    apply(simp add:nth_list_update)
   apply(simp add:nth_list_update)
  apply(case_tac "R (Muts x ! j)= ind x")
   apply(simp add:nth_list_update)
  apply(simp add:nth_list_update)
 apply(case_tac "M x!(T (Muts x!j))=Black")
  apply(rule conjI)
   apply(rule impI)
   apply(rule conjI)
    apply(rule disjI2,rule disjI2,rule disjI1, erule less_le_trans)
    apply(force simp add:Queue_def less_Suc_eq_le le_length_filter_update)
   apply(case_tac "R (Muts x ! j)= ind x")
    apply(simp add:nth_list_update)
   apply(simp add:nth_list_update)
  apply(rule impI)
  apply(rule disjI2,rule disjI2,rule disjI1, erule less_le_trans)
  apply(force simp add:Queue_def less_Suc_eq_le le_length_filter_update)
 apply(rule conjI)
  apply(rule impI)
   apply(rule conjI)
    apply(rule disjI2,rule disjI2,rule disjI1, erule less_le_trans)
    apply(force simp add:Queue_def less_Suc_eq_le le_length_filter_update)
   apply(case_tac "R (Muts x ! j)= ind x")
    apply(simp add:nth_list_update)
   apply(simp add:nth_list_update)
  apply(rule impI)
  apply(rule disjI2,rule disjI2,rule disjI1, erule less_le_trans)
  apply(force simp add:Queue_def less_Suc_eq_le le_length_filter_update)
 apply(erule conjE)
 apply(rule conjI)
  apply(case_tac "M x!(T (Muts x!j))=Black")
   apply(rule impI,rule conjI,(rule disjI2)+,rule conjI)
    apply clarify
    apply(case_tac "R (Muts x! j)=i")
     apply (force simp add: nth_list_update BtoW_def)
    apply (force simp add: nth_list_update)
   apply(erule le_trans,force simp add:Queue_def less_Suc_eq_le le_length_filter_update)
  apply(case_tac "R (Muts x ! j)= ind x")
   apply(simp add:nth_list_update)
  apply(simp add:nth_list_update)
 apply(rule impI,rule conjI)
  apply(rule disjI2,rule disjI2,rule disjI1, erule le_less_trans)
  apply(force simp add:Queue_def less_Suc_eq_le less_length_filter_update)
 apply(case_tac "R (Muts x! j)=ind x")
  apply (force simp add: nth_list_update)
 apply (force simp add: nth_list_update)
apply(rule impI, (rule disjI2)+, erule le_trans)
apply(force simp add:Queue_def less_Suc_eq_le le_length_filter_update)
--{* 2 subgoals left *}
apply clarify
apply(rule conjI)
 apply(disjE_tac)
  apply(simp_all add:Mul_Auxk_def Graph6)
  apply (rule impI)
   apply(rule conjI)
    apply(rule disjI1,rule subset_trans,erule Graph3,simp,simp)
   apply(case_tac "R (Muts x ! j)= ind x")
    apply(simp add:nth_list_update)
   apply(simp add:nth_list_update)
  apply(case_tac "R (Muts x ! j)= ind x")
   apply(simp add:nth_list_update)
  apply(simp add:nth_list_update)
 apply(case_tac "M x!(T (Muts x!j))=Black")
  apply(rule impI)
  apply(rule conjI)
   apply(rule disjI2,rule disjI2,rule disjI1, erule less_le_trans)
   apply(force simp add:Queue_def less_Suc_eq_le le_length_filter_update)
  apply(case_tac "R (Muts x ! j)= ind x")
   apply(simp add:nth_list_update)
  apply(simp add:nth_list_update)
 apply(rule impI)
 apply(rule conjI)
  apply(rule disjI2,rule disjI2,rule disjI1, erule less_le_trans)
  apply(force simp add:Queue_def less_Suc_eq_le le_length_filter_update)
 apply(case_tac "R (Muts x ! j)= ind x")
  apply(simp add:nth_list_update)
 apply(simp add:nth_list_update)
apply(rule impI)
apply(rule conjI)
 apply(erule conjE)+
 apply(case_tac "M x!(T (Muts x!j))=Black")
  apply((rule disjI2)+,rule conjI)
   apply clarify
   apply(case_tac "R (Muts x! j)=i")
    apply (force simp add: nth_list_update BtoW_def)
   apply (force simp add: nth_list_update)
  apply(rule conjI)
   apply(erule le_trans,force simp add:Queue_def less_Suc_eq_le le_length_filter_update)
  apply(rule impI)
  apply(case_tac "R (Muts x ! j)= ind x")
   apply(simp add:nth_list_update BtoW_def)
  apply (simp  add:nth_list_update)
  apply(rule impI)
  apply simp
  apply(disjE_tac)
   apply(rule disjI1, erule less_le_trans)
   apply(force simp add:Queue_def less_Suc_eq_le le_length_filter_update)
  apply force
 apply(rule disjI2,rule disjI2,rule disjI1, erule le_less_trans)
 apply(force simp add:Queue_def less_Suc_eq_le less_length_filter_update)
 apply(case_tac "R (Muts x ! j)= ind x")
  apply(simp add:nth_list_update)
 apply(simp add:nth_list_update)
apply(disjE_tac) 
apply simp_all
apply(conjI_tac)
 apply(rule impI)
 apply(rule disjI2,rule disjI2,rule disjI1, erule less_le_trans)
 apply(force simp add:Queue_def less_Suc_eq_le le_length_filter_update)
apply(erule conjE)+
apply(rule impI,(rule disjI2)+,rule conjI)
 apply(erule le_trans,force simp add:Queue_def less_Suc_eq_le le_length_filter_update)
apply(rule impI)+
apply simp
apply(disjE_tac)
 apply(rule disjI1, erule less_le_trans)
 apply(force simp add:Queue_def less_Suc_eq_le le_length_filter_update)
apply force
--{* 1 subgoal left *} 
apply clarify
apply(disjE_tac)
  apply(simp_all add:Graph6)
 apply(rule impI,rule disjI1,rule subset_trans,erule Graph3,simp,simp)
apply(rule conjI)
 apply(rule impI,rule disjI2,rule disjI2,rule disjI1,erule less_le_trans,force simp add:Queue_def less_Suc_eq_le le_length_filter_update)
apply(rule impI,rule disjI2,rule disjI2,rule disjI1,erule less_le_trans,force simp add:Queue_def less_Suc_eq_le le_length_filter_update)
apply(erule conjE)
apply(case_tac "M x!(T (Muts x!j))=Black")
 apply(rule conjI)
  apply(rule impI,(rule disjI2)+,rule conjI)
   apply clarify
   apply(case_tac "R (Muts x! j)=i")
    apply (force simp add: nth_list_update BtoW_def)
   apply (force simp add: nth_list_update)
  apply(erule le_trans,force simp add:Queue_def less_Suc_eq_le le_length_filter_update)
 apply(rule impI,(rule disjI2)+, erule le_trans)
 apply(force simp add:Queue_def less_Suc_eq_le le_length_filter_update)
apply(rule conjI)
 apply(rule impI,rule disjI2,rule disjI2,rule disjI1, erule le_less_trans)
 apply(force simp add:Queue_def less_Suc_eq_le less_length_filter_update)
apply(rule impI,rule disjI2,rule disjI2,rule disjI1, erule le_less_trans)
apply(force simp add:Queue_def less_Suc_eq_le less_length_filter_update)
done

lemma Mul_interfree_Redirect_Edge_Propagate_Black: "\<lbrakk>0\<le>j; j<n\<rbrakk>\<Longrightarrow>  
  interfree_aux (Some(Mul_Redirect_Edge j n ),{},Some (Mul_Propagate_Black n))"
apply (unfold mul_modules)
apply interfree_aux
apply safe
apply(simp_all add:mul_mutator_defs nth_list_update)
done

lemma Mul_interfree_Propagate_Black_Color_Target: "\<lbrakk>0\<le>j; j<n\<rbrakk>\<Longrightarrow>  
  interfree_aux (Some(Mul_Propagate_Black n),{},Some (Mul_Color_Target j n ))"
apply (unfold mul_modules)
apply interfree_aux
apply(simp_all add: mul_collector_defs mul_mutator_defs)
--{* 7 subgoals left *}
apply clarify
apply (simp add:Graph7 Graph8 Graph12)
apply(disjE_tac)
  apply(simp add:Graph7 Graph8 Graph12)
 apply(case_tac "M x!(T (Muts x!j))=Black")
  apply(rule disjI2,rule disjI1, erule le_trans)
  apply(force simp add:Queue_def less_Suc_eq_le le_length_filter_update Graph10)
 apply((rule disjI2)+,erule subset_psubset_trans, erule Graph11, simp) 
apply((rule disjI2)+,erule psubset_subset_trans, simp add: Graph9)
--{* 6 subgoals left *}
apply clarify
apply (simp add:Graph7 Graph8 Graph12)
apply(disjE_tac)
  apply(simp add:Graph7 Graph8 Graph12)
 apply(case_tac "M x!(T (Muts x!j))=Black")
  apply(rule disjI2,rule disjI1, erule le_trans)
  apply(force simp add:Queue_def less_Suc_eq_le le_length_filter_update Graph10)
 apply((rule disjI2)+,erule subset_psubset_trans, erule Graph11, simp) 
apply((rule disjI2)+,erule psubset_subset_trans, simp add: Graph9)
--{* 5 subgoals left *}
apply clarify
apply (simp add:mul_collector_defs Mul_PBInv_def Graph7 Graph8 Graph12)
apply(disjE_tac)
   apply(simp add:Graph7 Graph8 Graph12) 
  apply(rule disjI2,rule disjI1, erule psubset_subset_trans,simp add:Graph9)
 apply(case_tac "M x!(T (Muts x!j))=Black")
  apply(rule disjI2,rule disjI2,rule disjI1, erule less_le_trans)
  apply(force simp add:Queue_def less_Suc_eq_le le_length_filter_update Graph10)
 apply(rule disjI2,rule disjI1,erule subset_psubset_trans, erule Graph11, simp)
apply(erule conjE)
apply(case_tac "M x!(T (Muts x!j))=Black")
 apply((rule disjI2)+)
 apply (rule conjI)
  apply(simp add:Graph10)
 apply(erule le_trans)
 apply(force simp add:Queue_def less_Suc_eq_le le_length_filter_update Graph10)
apply(rule disjI2,rule disjI1,erule subset_psubset_trans, erule Graph11, simp) 
--{* 4 subgoals left *}
apply clarify
apply (simp add:mul_collector_defs Mul_PBInv_def Graph7 Graph8 Graph12)
apply(disjE_tac)
   apply(simp add:Graph7 Graph8 Graph12)
  apply(rule disjI2,rule disjI1, erule psubset_subset_trans,simp add:Graph9)
 apply(case_tac "M x!(T (Muts x!j))=Black")
  apply(rule disjI2,rule disjI2,rule disjI1, erule less_le_trans)
  apply(force simp add:Queue_def less_Suc_eq_le le_length_filter_update Graph10)
 apply(rule disjI2,rule disjI1,erule subset_psubset_trans, erule Graph11, simp)
apply(erule conjE)
apply(case_tac "M x!(T (Muts x!j))=Black")
 apply((rule disjI2)+)
 apply (rule conjI)
  apply(simp add:Graph10)
 apply(erule le_trans)
 apply(force simp add:Queue_def less_Suc_eq_le le_length_filter_update Graph10)
apply(rule disjI2,rule disjI1,erule subset_psubset_trans, erule Graph11, simp) 
--{* 3 subgoals left *}
apply clarify
apply (simp add:mul_collector_defs Mul_PBInv_def Graph7 Graph8 Graph12)
apply(case_tac "M x!(T (Muts x!j))=Black")
 apply(simp add:Graph10)
 apply(disjE_tac)
  apply simp_all
  apply(rule disjI2, rule disjI2, rule disjI1,erule less_le_trans)
  apply(force simp add:Queue_def less_Suc_eq_le le_length_filter_update Graph10)
 apply(erule conjE)
 apply((rule disjI2)+,erule le_trans)
 apply(force simp add:Queue_def less_Suc_eq_le le_length_filter_update Graph10)
apply(rule conjI)
 apply(rule disjI2,rule disjI1, erule subset_psubset_trans,simp add:Graph11) 
apply (force simp add:nth_list_update)
--{* 2 subgoals left *}
apply clarify 
apply(simp add:Mul_Auxk_def Graph7 Graph8 Graph12)
apply(case_tac "M x!(T (Muts x!j))=Black")
 apply(simp add:Graph10)
 apply(disjE_tac)
  apply simp_all
  apply(rule disjI2, rule disjI2, rule disjI1,erule less_le_trans)
  apply(force simp add:Queue_def less_Suc_eq_le le_length_filter_update Graph10)
 apply(erule conjE)+
 apply((rule disjI2)+,rule conjI, erule le_trans)
  apply(force simp add:Queue_def less_Suc_eq_le le_length_filter_update Graph10)
 apply((rule impI)+)
 apply simp
 apply(erule disjE)
  apply(rule disjI1, erule less_le_trans) 
  apply(force simp add:Queue_def less_Suc_eq_le le_length_filter_update Graph10)
 apply force
apply(rule conjI)
 apply(rule disjI2,rule disjI1, erule subset_psubset_trans,simp add:Graph11) 
apply (force simp add:nth_list_update)
--{* 1 subgoal left *}
apply clarify
apply (simp add:mul_collector_defs Mul_PBInv_def Graph7 Graph8 Graph12)
apply(case_tac "M x!(T (Muts x!j))=Black")
 apply(simp add:Graph10)
 apply(disjE_tac)
  apply simp_all
  apply(rule disjI2, rule disjI2, rule disjI1,erule less_le_trans)
  apply(force simp add:Queue_def less_Suc_eq_le le_length_filter_update Graph10)
 apply(erule conjE)
 apply((rule disjI2)+,erule le_trans)
 apply(force simp add:Queue_def less_Suc_eq_le le_length_filter_update Graph10)
apply(rule disjI2,rule disjI1, erule subset_psubset_trans,simp add:Graph11) 
done

lemma Mul_interfree_Color_Target_Propagate_Black: "\<lbrakk>0\<le>j; j<n\<rbrakk>\<Longrightarrow>  
  interfree_aux (Some(Mul_Color_Target j n),{},Some(Mul_Propagate_Black n ))"
apply (unfold mul_modules)
apply interfree_aux
apply safe
apply(simp_all add:mul_mutator_defs nth_list_update)
done

lemma Mul_interfree_Count_Redirect_Edge: "\<lbrakk>0\<le>j; j<n\<rbrakk>\<Longrightarrow>  
  interfree_aux (Some(Mul_Count n ),{},Some(Mul_Redirect_Edge j n))"
apply (unfold mul_modules)
apply interfree_aux
--{* 9 subgoals left *}
apply(simp add:mul_mutator_defs mul_collector_defs Mul_CountInv_def Graph6)
apply clarify
apply disjE_tac
   apply(simp add:Graph6)
  apply(rule impI,rule disjI1,rule subset_trans,erule Graph3,simp,simp)
 apply(simp add:Graph6)
apply clarify
apply disjE_tac
 apply(simp add:Graph6)
 apply(rule conjI)
  apply(rule impI,rule disjI2,rule disjI2,rule disjI1,erule le_trans,force simp add:Queue_def less_Suc_eq_le le_length_filter_update)
 apply(rule impI,rule disjI2,rule disjI2,rule disjI1,erule le_trans,force simp add:Queue_def less_Suc_eq_le le_length_filter_update)
apply(simp add:Graph6)
--{* 8 subgoals left *}
apply(simp add:mul_mutator_defs nth_list_update)
--{* 7 subgoals left *}
apply(simp add:mul_mutator_defs mul_collector_defs)
apply clarify
apply disjE_tac
   apply(simp add:Graph6)
  apply(rule impI,rule disjI1,rule subset_trans,erule Graph3,simp,simp)
 apply(simp add:Graph6)
apply clarify
apply disjE_tac
 apply(simp add:Graph6)
 apply(rule conjI)
  apply(rule impI,rule disjI2,rule disjI2,rule disjI1,erule le_trans,force simp add:Queue_def less_Suc_eq_le le_length_filter_update)
 apply(rule impI,rule disjI2,rule disjI2,rule disjI1,erule le_trans,force simp add:Queue_def less_Suc_eq_le le_length_filter_update)
apply(simp add:Graph6)
--{* 6 subgoals left *}
apply(simp add:mul_mutator_defs mul_collector_defs Mul_CountInv_def)
apply clarify
apply disjE_tac
   apply(simp add:Graph6 Queue_def)
  apply(rule impI,rule disjI1,rule subset_trans,erule Graph3,simp,simp)
 apply(simp add:Graph6)
apply clarify
apply disjE_tac
 apply(simp add:Graph6)
 apply(rule conjI)
  apply(rule impI,rule disjI2,rule disjI2,rule disjI1,erule le_trans,force simp add:Queue_def less_Suc_eq_le le_length_filter_update)
 apply(rule impI,rule disjI2,rule disjI2,rule disjI1,erule le_trans,force simp add:Queue_def less_Suc_eq_le le_length_filter_update)
apply(simp add:Graph6)
--{* 5 subgoals left *}
apply(simp add:mul_mutator_defs mul_collector_defs Mul_CountInv_def)
apply clarify
apply disjE_tac
   apply(simp add:Graph6)
  apply(rule impI,rule disjI1,rule subset_trans,erule Graph3,simp,simp)
 apply(simp add:Graph6)
apply clarify
apply disjE_tac
 apply(simp add:Graph6)
 apply(rule conjI)
  apply(rule impI,rule disjI2,rule disjI2,rule disjI1,erule le_trans,force simp add:Queue_def less_Suc_eq_le le_length_filter_update)
 apply(rule impI,rule disjI2,rule disjI2,rule disjI1,erule le_trans,force simp add:Queue_def less_Suc_eq_le le_length_filter_update)
apply(simp add:Graph6)
--{* 4 subgoals left *}
apply(simp add:mul_mutator_defs mul_collector_defs Mul_CountInv_def)
apply clarify
apply disjE_tac
   apply(simp add:Graph6)
  apply(rule impI,rule disjI1,rule subset_trans,erule Graph3,simp,simp)
 apply(simp add:Graph6)
apply clarify
apply disjE_tac
 apply(simp add:Graph6)
 apply(rule conjI)
  apply(rule impI,rule disjI2,rule disjI2,rule disjI1,erule le_trans,force simp add:Queue_def less_Suc_eq_le le_length_filter_update)
 apply(rule impI,rule disjI2,rule disjI2,rule disjI1,erule le_trans,force simp add:Queue_def less_Suc_eq_le le_length_filter_update)
apply(simp add:Graph6)
--{* 3 subgoals left *}
apply(simp add:mul_mutator_defs nth_list_update)
--{* 2 subgoals left *}
apply(simp add:mul_mutator_defs mul_collector_defs Mul_CountInv_def)
apply clarify
apply disjE_tac
   apply(simp add:Graph6)
  apply(rule impI,rule disjI1,rule subset_trans,erule Graph3,simp,simp)
 apply(simp add:Graph6)
apply clarify
apply disjE_tac
 apply(simp add:Graph6)
 apply(rule conjI)
  apply(rule impI,rule disjI2,rule disjI2,rule disjI1,erule le_trans,force simp add:Queue_def less_Suc_eq_le le_length_filter_update)
 apply(rule impI,rule disjI2,rule disjI2,rule disjI1,erule le_trans,force simp add:Queue_def less_Suc_eq_le le_length_filter_update)
apply(simp add:Graph6)
--{* 1 subgoal left *}
apply(simp add:mul_mutator_defs nth_list_update)
done

lemma Mul_interfree_Redirect_Edge_Count: "\<lbrakk>0\<le>j; j<n\<rbrakk>\<Longrightarrow>  
  interfree_aux (Some(Mul_Redirect_Edge j n),{},Some(Mul_Count n ))"
apply (unfold mul_modules)
apply interfree_aux
apply safe
apply(simp_all add:mul_mutator_defs nth_list_update)
done

lemma Mul_interfree_Count_Color_Target: "\<lbrakk>0\<le>j; j<n\<rbrakk>\<Longrightarrow>  
  interfree_aux (Some(Mul_Count n ),{},Some(Mul_Color_Target j n))"
apply (unfold mul_modules)
apply interfree_aux
apply(simp_all add:mul_collector_defs mul_mutator_defs Mul_CountInv_def)
--{* 6 subgoals left *}
apply clarify
apply disjE_tac
  apply (simp add: Graph7 Graph8 Graph12)
 apply (simp add: Graph7 Graph8 Graph12)
apply clarify
apply disjE_tac
 apply (simp add: Graph7 Graph8 Graph12)
 apply(case_tac "M x!(T (Muts x!j))=Black")
  apply(rule disjI2,rule disjI2, rule disjI1, erule le_trans)
  apply(force simp add:Queue_def less_Suc_eq_le le_length_filter_update Graph10)
 apply((rule disjI2)+,(erule subset_psubset_trans)+, simp add: Graph11)
apply (simp add: Graph7 Graph8 Graph12)
apply((rule disjI2)+,erule psubset_subset_trans, simp add: Graph9)
--{* 5 subgoals left *}
apply clarify
apply disjE_tac
  apply (simp add: Graph7 Graph8 Graph12)
 apply (simp add: Graph7 Graph8 Graph12)
apply clarify
apply disjE_tac
 apply (simp add: Graph7 Graph8 Graph12)
 apply(case_tac "M x!(T (Muts x!j))=Black")
  apply(rule disjI2,rule disjI2, rule disjI1, erule le_trans)
  apply(force simp add:Queue_def less_Suc_eq_le le_length_filter_update Graph10)
 apply((rule disjI2)+,(erule subset_psubset_trans)+, simp add: Graph11)
apply (simp add: Graph7 Graph8 Graph12)
apply((rule disjI2)+,erule psubset_subset_trans, simp add: Graph9)
--{* 4 subgoals left *}
apply clarify
apply disjE_tac
  apply (simp add: Graph7 Graph8 Graph12)
 apply (simp add: Graph7 Graph8 Graph12)
apply clarify
apply disjE_tac
 apply (simp add: Graph7 Graph8 Graph12)
 apply(case_tac "M x!(T (Muts x!j))=Black")
  apply(rule disjI2,rule disjI2, rule disjI1, erule le_trans)
  apply(force simp add:Queue_def less_Suc_eq_le le_length_filter_update Graph10)
 apply((rule disjI2)+,(erule subset_psubset_trans)+, simp add: Graph11)
apply (simp add: Graph7 Graph8 Graph12)
apply((rule disjI2)+,erule psubset_subset_trans, simp add: Graph9)
--{* 3 subgoals left *}
apply clarify
apply disjE_tac
  apply (simp add: Graph7 Graph8 Graph12)
 apply (simp add: Graph7 Graph8 Graph12)
apply clarify
apply disjE_tac
 apply (simp add: Graph7 Graph8 Graph12)
 apply(case_tac "M x!(T (Muts x!j))=Black")
  apply(rule disjI2,rule disjI2, rule disjI1, erule le_trans)
  apply(force simp add:Queue_def less_Suc_eq_le le_length_filter_update Graph10)
 apply((rule disjI2)+,(erule subset_psubset_trans)+, simp add: Graph11)
apply (simp add: Graph7 Graph8 Graph12)
apply((rule disjI2)+,erule psubset_subset_trans, simp add: Graph9)
--{* 2 subgoals left *}
apply clarify
apply disjE_tac
  apply (simp add: Graph7 Graph8 Graph12 nth_list_update)
 apply (simp add: Graph7 Graph8 Graph12 nth_list_update)
apply clarify
apply disjE_tac
 apply (simp add: Graph7 Graph8 Graph12)
 apply(rule conjI)
  apply(case_tac "M x!(T (Muts x!j))=Black")
   apply(rule disjI2,rule disjI2, rule disjI1, erule le_trans)
   apply(force simp add:Queue_def less_Suc_eq_le le_length_filter_update Graph10)
  apply((rule disjI2)+,(erule subset_psubset_trans)+, simp add: Graph11)
 apply (simp add: nth_list_update)
apply (simp add: Graph7 Graph8 Graph12)
apply(rule conjI)
 apply((rule disjI2)+,erule psubset_subset_trans, simp add: Graph9)
apply (simp add: nth_list_update)
--{* 1 subgoal left *}
apply clarify
apply disjE_tac
  apply (simp add: Graph7 Graph8 Graph12)
 apply (simp add: Graph7 Graph8 Graph12)
apply clarify
apply disjE_tac
 apply (simp add: Graph7 Graph8 Graph12)
 apply(case_tac "M x!(T (Muts x!j))=Black")
  apply(rule disjI2,rule disjI2, rule disjI1, erule le_trans)
  apply(force simp add:Queue_def less_Suc_eq_le le_length_filter_update Graph10)
 apply((rule disjI2)+,(erule subset_psubset_trans)+, simp add: Graph11)
apply (simp add: Graph7 Graph8 Graph12)
apply((rule disjI2)+,erule psubset_subset_trans, simp add: Graph9)
done

lemma Mul_interfree_Color_Target_Count: "\<lbrakk>0\<le>j; j<n\<rbrakk>\<Longrightarrow>  
  interfree_aux (Some(Mul_Color_Target j n),{}, Some(Mul_Count n ))"
apply (unfold mul_modules)
apply interfree_aux
apply safe
apply(simp_all add:mul_mutator_defs nth_list_update)
done

lemma Mul_interfree_Append_Redirect_Edge: "\<lbrakk>0\<le>j; j<n\<rbrakk>\<Longrightarrow>  
  interfree_aux (Some(Mul_Append n),{}, Some(Mul_Redirect_Edge j n))"
apply (unfold mul_modules)
apply interfree_aux
apply(tactic {* ALLGOALS Clarify_tac *})
apply(simp_all add:Graph6 Append_to_free0 Append_to_free1 mul_collector_defs mul_mutator_defs Mul_AppendInv_def)
apply(erule_tac x=j in allE, force dest:Graph3)+
done

lemma Mul_interfree_Redirect_Edge_Append: "\<lbrakk>0\<le>j; j<n\<rbrakk>\<Longrightarrow>  
  interfree_aux (Some(Mul_Redirect_Edge j n),{},Some(Mul_Append n))"
apply (unfold mul_modules)
apply interfree_aux
apply(tactic {* ALLGOALS Clarify_tac *})
apply(simp_all add:mul_collector_defs Append_to_free0 Mul_AppendInv_def  mul_mutator_defs nth_list_update)
done

lemma Mul_interfree_Append_Color_Target: "\<lbrakk>0\<le>j; j<n\<rbrakk>\<Longrightarrow>  
  interfree_aux (Some(Mul_Append n),{}, Some(Mul_Color_Target j n))"
apply (unfold mul_modules)
apply interfree_aux
apply(tactic {* ALLGOALS Clarify_tac *})
apply(simp_all add:mul_mutator_defs mul_collector_defs Mul_AppendInv_def Graph7 Graph8 Append_to_free0 Append_to_free1 
              Graph12 nth_list_update)
done

lemma Mul_interfree_Color_Target_Append: "\<lbrakk>0\<le>j; j<n\<rbrakk>\<Longrightarrow>  
  interfree_aux (Some(Mul_Color_Target j n),{}, Some(Mul_Append n))"
apply (unfold mul_modules)
apply interfree_aux
apply(tactic {* ALLGOALS Clarify_tac *})
apply(simp_all add: mul_mutator_defs nth_list_update)
apply(simp add:Mul_AppendInv_def Append_to_free0)
done

subsubsection {* Interference freedom Collector-Mutator *}

lemmas mul_collector_mutator_interfree =  
 Mul_interfree_Blacken_Roots_Redirect_Edge Mul_interfree_Blacken_Roots_Color_Target 
 Mul_interfree_Propagate_Black_Redirect_Edge Mul_interfree_Propagate_Black_Color_Target  
 Mul_interfree_Count_Redirect_Edge Mul_interfree_Count_Color_Target 
 Mul_interfree_Append_Redirect_Edge Mul_interfree_Append_Color_Target 
 Mul_interfree_Redirect_Edge_Blacken_Roots Mul_interfree_Color_Target_Blacken_Roots 
 Mul_interfree_Redirect_Edge_Propagate_Black Mul_interfree_Color_Target_Propagate_Black  
 Mul_interfree_Redirect_Edge_Count Mul_interfree_Color_Target_Count 
 Mul_interfree_Redirect_Edge_Append Mul_interfree_Color_Target_Append

lemma Mul_interfree_Collector_Mutator: "j<n  \<Longrightarrow> 
  interfree_aux (Some (Mul_Collector n), {}, Some (Mul_Mutator j n))"
apply(unfold Mul_Collector_def Mul_Mutator_def)
apply interfree_aux
apply(simp_all add:mul_collector_mutator_interfree)
apply(unfold mul_modules mul_collector_defs mul_mutator_defs)
apply(tactic  {* TRYALL (interfree_aux_tac) *})
--{* 42 subgoals left *}
apply (clarify,simp add:Graph6 Graph7 Graph8 Append_to_free0 Append_to_free1 Graph12)+
--{* 24 subgoals left *}
apply(simp_all add:Graph6 Graph7 Graph8 Append_to_free0 Append_to_free1 Graph12)
--{* 14 subgoals left *}
apply(tactic {* TRYALL Clarify_tac *})
apply(simp_all add:Graph6 Graph7 Graph8 Append_to_free0 Append_to_free1 Graph12)
apply(tactic {* TRYALL (rtac conjI) *})
apply(tactic {* TRYALL (rtac impI) *})
apply(tactic {* TRYALL (etac disjE) *})
apply(tactic {* TRYALL (etac conjE) *})
apply(tactic {* TRYALL (etac disjE) *})
apply(tactic {* TRYALL (etac disjE) *})
--{* 72 subgoals left *}
apply(simp_all add:Graph6 Graph7 Graph8 Append_to_free0 Append_to_free1 Graph12)
--{* 35 subgoals left *}
apply(tactic {* TRYALL(EVERY'[rtac disjI1,rtac subset_trans,etac (thm "Graph3"),Force_tac, assume_tac]) *})
--{* 28 subgoals left *}
apply(tactic {* TRYALL (etac conjE) *})
apply(tactic {* TRYALL (etac disjE) *})
--{* 34 subgoals left *}
apply(rule disjI2,rule disjI1,erule le_trans,force simp add:Queue_def less_Suc_eq_le le_length_filter_update)
apply(rule disjI2,rule disjI1,erule le_trans,force simp add:Queue_def less_Suc_eq_le le_length_filter_update)
apply(tactic {* ALLGOALS(case_tac "M x!(T (Muts x ! j))=Black") *})
apply(simp_all add:Graph10)
--{* 47 subgoals left *}
apply(tactic {* TRYALL(EVERY'[REPEAT o (rtac disjI2),etac subset_psubset_trans,etac (thm "Graph11"),Force_tac]) *})
--{* 41 subgoals left *}
apply(tactic {* TRYALL(EVERY'[rtac disjI2, rtac disjI1, etac le_trans, force_tac (claset(),simpset() addsimps [thm "Queue_def", less_Suc_eq_le, thm "le_length_filter_update"])]) *})
--{* 35 subgoals left *}
apply(tactic {* TRYALL(EVERY'[rtac disjI2,rtac disjI1,etac psubset_subset_trans,rtac (thm "Graph9"),Force_tac]) *})
--{* 31 subgoals left *}
apply(tactic {* TRYALL(EVERY'[rtac disjI2,rtac disjI1,etac subset_psubset_trans,etac (thm "Graph11"),Force_tac]) *})
--{* 29 subgoals left *}
apply(tactic {* TRYALL(EVERY'[REPEAT o (rtac disjI2),etac subset_psubset_trans,etac subset_psubset_trans,etac (thm "Graph11"),Force_tac]) *})
--{* 25 subgoals left *}
apply(tactic {* TRYALL(EVERY'[rtac disjI2, rtac disjI2, rtac disjI1, etac le_trans, force_tac (claset(),simpset() addsimps [thm "Queue_def", less_Suc_eq_le, thm "le_length_filter_update"])]) *})
--{* 10 subgoals left *}
apply(rule disjI2,rule disjI2,rule conjI,erule less_le_trans,force simp add:Queue_def less_Suc_eq_le le_length_filter_update, rule disjI1, rule less_imp_le, erule less_le_trans, force simp add:Queue_def less_Suc_eq_le le_length_filter_update)+
done

subsubsection {* Interference freedom Mutator-Collector *}

lemma Mul_interfree_Mutator_Collector: " j < n \<Longrightarrow> 
  interfree_aux (Some (Mul_Mutator j n), {}, Some (Mul_Collector n))"
apply(unfold Mul_Collector_def Mul_Mutator_def)
apply interfree_aux
apply(simp_all add:mul_collector_mutator_interfree)
apply(unfold mul_modules mul_collector_defs mul_mutator_defs)
apply(tactic  {* TRYALL (interfree_aux_tac) *})
--{* 76 subgoals left *}
apply (clarify,simp add: nth_list_update)+
--{* 56 subgoals left *}
apply(clarify,simp add:Mul_AppendInv_def Append_to_free0 nth_list_update)+
done

subsubsection {* The Multi-Mutator Garbage Collection Algorithm *}

text {* The total number of verification conditions is 328 *}

lemma Mul_Gar_Coll: 
 "\<parallel>- .{\<acute>Mul_Proper n \<and> \<acute>Mul_mut_init n \<and> (\<forall>i<n. Z (\<acute>Muts!i))}.  
 COBEGIN  
  Mul_Collector n
 .{False}.
 \<parallel>  
 SCHEME  [0\<le> j< n]
  Mul_Mutator j n
 .{False}.  
 COEND  
 .{False}."
apply oghoare
--{* Strengthening the precondition *}
apply(rule Int_greatest)
 apply (case_tac n)
  apply(force simp add: Mul_Collector_def mul_mutator_defs mul_collector_defs nth_append)
 apply(simp add: Mul_Mutator_def mul_collector_defs mul_mutator_defs nth_append)
 apply force
apply clarify
apply(case_tac xa)
 apply(simp add:Mul_Collector_def mul_mutator_defs mul_collector_defs nth_append)
apply(simp add: Mul_Mutator_def mul_mutator_defs mul_collector_defs nth_append nth_map_upt)
--{* Collector *}
apply(rule Mul_Collector)
--{* Mutator *}
apply(erule Mul_Mutator)
--{* Interference freedom *}
apply(simp add:Mul_interfree_Collector_Mutator)
apply(simp add:Mul_interfree_Mutator_Collector)
apply(simp add:Mul_interfree_Mutator_Mutator)
--{* Weakening of the postcondition *}
apply(case_tac n)
 apply(simp add:Mul_Collector_def mul_mutator_defs mul_collector_defs nth_append)
apply(simp add:Mul_Mutator_def mul_mutator_defs mul_collector_defs nth_append)
done

end
