section \<open>The Multi-Mutator Case\<close>

theory Mul_Gar_Coll imports Graph OG_Syntax begin

text \<open>The full theory takes aprox. 18 minutes.\<close>

record mut =
  Z :: bool
  R :: nat
  T :: nat

text \<open>Declaration of variables:\<close>

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

subsection \<open>The Mutators\<close>

definition Mul_mut_init :: "mul_gar_coll_state \<Rightarrow> nat \<Rightarrow> bool" where
  "Mul_mut_init \<equiv> \<guillemotleft> \<lambda>n. n=length \<acute>Muts \<and> (\<forall>i<n. R (\<acute>Muts!i)<length \<acute>E
                          \<and> T (\<acute>Muts!i)<length \<acute>M) \<guillemotright>"

definition Mul_Redirect_Edge  :: "nat \<Rightarrow> nat \<Rightarrow> mul_gar_coll_state ann_com" where
  "Mul_Redirect_Edge j n \<equiv>
  \<lbrace>\<acute>Mul_mut_init n \<and> Z (\<acute>Muts!j)\<rbrace>
  \<langle>IF T(\<acute>Muts!j) \<in> Reach \<acute>E THEN
  \<acute>E:= \<acute>E[R (\<acute>Muts!j):= (fst (\<acute>E!R(\<acute>Muts!j)), T (\<acute>Muts!j))] FI,,
  \<acute>Muts:= \<acute>Muts[j:= (\<acute>Muts!j) \<lparr>Z:=False\<rparr>]\<rangle>"

definition Mul_Color_Target :: "nat \<Rightarrow> nat \<Rightarrow> mul_gar_coll_state ann_com" where
  "Mul_Color_Target j n \<equiv>
  \<lbrace>\<acute>Mul_mut_init n \<and> \<not> Z (\<acute>Muts!j)\<rbrace>
  \<langle>\<acute>M:=\<acute>M[T (\<acute>Muts!j):=Black],, \<acute>Muts:=\<acute>Muts[j:= (\<acute>Muts!j) \<lparr>Z:=True\<rparr>]\<rangle>"

definition Mul_Mutator :: "nat \<Rightarrow> nat \<Rightarrow>  mul_gar_coll_state ann_com" where
  "Mul_Mutator j n \<equiv>
  \<lbrace>\<acute>Mul_mut_init n \<and> Z (\<acute>Muts!j)\<rbrace>
  WHILE True
    INV \<lbrace>\<acute>Mul_mut_init n \<and> Z (\<acute>Muts!j)\<rbrace>
  DO Mul_Redirect_Edge j n ;;
     Mul_Color_Target j n
  OD"

lemmas mul_mutator_defs = Mul_mut_init_def Mul_Redirect_Edge_def Mul_Color_Target_def

subsubsection \<open>Correctness of the proof outline of one mutator\<close>

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
    \<lbrace>\<acute>Mul_mut_init n \<and> Z (\<acute>Muts!j)\<rbrace>"
apply (unfold mul_mutator_defs)
apply annhoare
apply(simp_all)
apply clarify
apply(simp add:nth_list_update)
done

lemma Mul_Mutator: "0\<le>j \<and> j<n \<Longrightarrow>
 \<turnstile> Mul_Mutator j n \<lbrace>False\<rbrace>"
apply(unfold Mul_Mutator_def)
apply annhoare
apply(simp_all add:Mul_Redirect_Edge Mul_Color_Target)
apply(simp add:mul_mutator_defs Mul_Redirect_Edge_def)
done

subsubsection \<open>Interference freedom between mutators\<close>

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
apply(tactic \<open>TRYALL (interfree_aux_tac \<^context>)\<close>)
apply(tactic \<open>ALLGOALS (clarify_tac \<^context>)\<close>)
apply (simp_all add:nth_list_update)
done

subsubsection \<open>Modular Parameterized Mutators\<close>

lemma Mul_Parameterized_Mutators: "0<n \<Longrightarrow>
 \<parallel>- \<lbrace>\<acute>Mul_mut_init n \<and> (\<forall>i<n. Z (\<acute>Muts!i))\<rbrace>
 COBEGIN
 SCHEME  [0\<le> j< n]
  Mul_Mutator j n
 \<lbrace>False\<rbrace>
 COEND
 \<lbrace>False\<rbrace>"
apply oghoare
apply(force simp add:Mul_Mutator_def mul_mutator_defs nth_list_update)
apply(erule Mul_Mutator)
apply(simp add:Mul_interfree_Mutator_Mutator)
apply(force simp add:Mul_Mutator_def mul_mutator_defs nth_list_update)
done

subsection \<open>The Collector\<close>

definition Queue :: "mul_gar_coll_state \<Rightarrow> nat" where
 "Queue \<equiv> \<guillemotleft> length (filter (\<lambda>i. \<not> Z i \<and> \<acute>M!(T i) \<noteq> Black) \<acute>Muts) \<guillemotright>"

consts  M_init :: nodes

definition Proper_M_init :: "mul_gar_coll_state \<Rightarrow> bool" where
  "Proper_M_init \<equiv> \<guillemotleft> Blacks M_init=Roots \<and> length M_init=length \<acute>M \<guillemotright>"

definition Mul_Proper :: "mul_gar_coll_state \<Rightarrow> nat \<Rightarrow> bool" where
  "Mul_Proper \<equiv> \<guillemotleft> \<lambda>n. Proper_Roots \<acute>M \<and> Proper_Edges (\<acute>M, \<acute>E) \<and> \<acute>Proper_M_init \<and> n=length \<acute>Muts \<guillemotright>"

definition Safe :: "mul_gar_coll_state \<Rightarrow> bool" where
  "Safe \<equiv> \<guillemotleft> Reach \<acute>E \<subseteq> Blacks \<acute>M \<guillemotright>"

lemmas mul_collector_defs = Proper_M_init_def Mul_Proper_def Safe_def

subsubsection \<open>Blackening Roots\<close>

definition Mul_Blacken_Roots :: "nat \<Rightarrow>  mul_gar_coll_state ann_com" where
  "Mul_Blacken_Roots n \<equiv>
  \<lbrace>\<acute>Mul_Proper n\<rbrace>
  \<acute>ind:=0;;
  \<lbrace>\<acute>Mul_Proper n \<and> \<acute>ind=0\<rbrace>
  WHILE \<acute>ind<length \<acute>M
    INV \<lbrace>\<acute>Mul_Proper n \<and> (\<forall>i<\<acute>ind. i\<in>Roots \<longrightarrow> \<acute>M!i=Black) \<and> \<acute>ind\<le>length \<acute>M\<rbrace>
  DO \<lbrace>\<acute>Mul_Proper n \<and> (\<forall>i<\<acute>ind. i\<in>Roots \<longrightarrow> \<acute>M!i=Black) \<and> \<acute>ind<length \<acute>M\<rbrace>
       IF \<acute>ind\<in>Roots THEN
     \<lbrace>\<acute>Mul_Proper n \<and> (\<forall>i<\<acute>ind. i\<in>Roots \<longrightarrow> \<acute>M!i=Black) \<and> \<acute>ind<length \<acute>M \<and> \<acute>ind\<in>Roots\<rbrace>
       \<acute>M:=\<acute>M[\<acute>ind:=Black] FI;;
     \<lbrace>\<acute>Mul_Proper n \<and> (\<forall>i<\<acute>ind+1. i\<in>Roots \<longrightarrow> \<acute>M!i=Black) \<and> \<acute>ind<length \<acute>M\<rbrace>
       \<acute>ind:=\<acute>ind+1
  OD"

lemma Mul_Blacken_Roots:
  "\<turnstile> Mul_Blacken_Roots n
  \<lbrace>\<acute>Mul_Proper n \<and> Roots \<subseteq> Blacks \<acute>M\<rbrace>"
apply (unfold Mul_Blacken_Roots_def)
apply annhoare
apply(simp_all add:mul_collector_defs Graph_defs)
apply safe
apply(simp_all add:nth_list_update)
  apply (erule less_SucE)
   apply simp+
 apply force
apply force
done

subsubsection \<open>Propagating Black\<close>

definition Mul_PBInv :: "mul_gar_coll_state \<Rightarrow> bool" where
  "Mul_PBInv \<equiv>  \<guillemotleft>\<acute>Safe \<or> \<acute>obc\<subset>Blacks \<acute>M \<or> \<acute>l<\<acute>Queue
                 \<or> (\<forall>i<\<acute>ind. \<not>BtoW(\<acute>E!i,\<acute>M)) \<and> \<acute>l\<le>\<acute>Queue\<guillemotright>"

definition Mul_Auxk :: "mul_gar_coll_state \<Rightarrow> bool" where
  "Mul_Auxk \<equiv> \<guillemotleft>\<acute>l<\<acute>Queue \<or> \<acute>M!\<acute>k\<noteq>Black \<or> \<not>BtoW(\<acute>E!\<acute>ind, \<acute>M) \<or> \<acute>obc\<subset>Blacks \<acute>M\<guillemotright>"

definition Mul_Propagate_Black :: "nat \<Rightarrow>  mul_gar_coll_state ann_com" where
  "Mul_Propagate_Black n \<equiv>
 \<lbrace>\<acute>Mul_Proper n \<and> Roots\<subseteq>Blacks \<acute>M \<and> \<acute>obc\<subseteq>Blacks \<acute>M \<and> \<acute>bc\<subseteq>Blacks \<acute>M
  \<and> (\<acute>Safe \<or> \<acute>l\<le>\<acute>Queue \<or> \<acute>obc\<subset>Blacks \<acute>M)\<rbrace>
 \<acute>ind:=0;;
 \<lbrace>\<acute>Mul_Proper n \<and> Roots\<subseteq>Blacks \<acute>M
   \<and> \<acute>obc\<subseteq>Blacks \<acute>M \<and> Blacks \<acute>M\<subseteq>Blacks \<acute>M \<and> \<acute>bc\<subseteq>Blacks \<acute>M
   \<and> (\<acute>Safe \<or> \<acute>l\<le>\<acute>Queue \<or> \<acute>obc\<subset>Blacks \<acute>M) \<and> \<acute>ind=0\<rbrace>
 WHILE \<acute>ind<length \<acute>E
  INV \<lbrace>\<acute>Mul_Proper n \<and> Roots\<subseteq>Blacks \<acute>M
        \<and> \<acute>obc\<subseteq>Blacks \<acute>M \<and> \<acute>bc\<subseteq>Blacks \<acute>M
        \<and> \<acute>Mul_PBInv \<and> \<acute>ind\<le>length \<acute>E\<rbrace>
 DO \<lbrace>\<acute>Mul_Proper n \<and> Roots\<subseteq>Blacks \<acute>M
     \<and> \<acute>obc\<subseteq>Blacks \<acute>M \<and> \<acute>bc\<subseteq>Blacks \<acute>M
     \<and> \<acute>Mul_PBInv \<and> \<acute>ind<length \<acute>E\<rbrace>
   IF \<acute>M!(fst (\<acute>E!\<acute>ind))=Black THEN
   \<lbrace>\<acute>Mul_Proper n \<and> Roots\<subseteq>Blacks \<acute>M
     \<and> \<acute>obc\<subseteq>Blacks \<acute>M \<and> \<acute>bc\<subseteq>Blacks \<acute>M
     \<and> \<acute>Mul_PBInv \<and> (\<acute>M!fst(\<acute>E!\<acute>ind))=Black \<and> \<acute>ind<length \<acute>E\<rbrace>
    \<acute>k:=snd(\<acute>E!\<acute>ind);;
   \<lbrace>\<acute>Mul_Proper n \<and> Roots\<subseteq>Blacks \<acute>M
     \<and> \<acute>obc\<subseteq>Blacks \<acute>M \<and> \<acute>bc\<subseteq>Blacks \<acute>M
     \<and> (\<acute>Safe \<or> \<acute>obc\<subset>Blacks \<acute>M \<or> \<acute>l<\<acute>Queue \<or> (\<forall>i<\<acute>ind. \<not>BtoW(\<acute>E!i,\<acute>M))
        \<and> \<acute>l\<le>\<acute>Queue \<and> \<acute>Mul_Auxk ) \<and> \<acute>k<length \<acute>M \<and> \<acute>M!fst(\<acute>E!\<acute>ind)=Black
     \<and> \<acute>ind<length \<acute>E\<rbrace>
   \<langle>\<acute>M:=\<acute>M[\<acute>k:=Black],,\<acute>ind:=\<acute>ind+1\<rangle>
   ELSE \<lbrace>\<acute>Mul_Proper n \<and> Roots\<subseteq>Blacks \<acute>M
         \<and> \<acute>obc\<subseteq>Blacks \<acute>M \<and> \<acute>bc\<subseteq>Blacks \<acute>M
         \<and> \<acute>Mul_PBInv \<and> \<acute>ind<length \<acute>E\<rbrace>
         \<langle>IF \<acute>M!(fst (\<acute>E!\<acute>ind))\<noteq>Black THEN \<acute>ind:=\<acute>ind+1 FI\<rangle> FI
 OD"

lemma Mul_Propagate_Black:
  "\<turnstile> Mul_Propagate_Black n
   \<lbrace>\<acute>Mul_Proper n \<and> Roots\<subseteq>Blacks \<acute>M \<and> \<acute>obc\<subseteq>Blacks \<acute>M \<and> \<acute>bc\<subseteq>Blacks \<acute>M
     \<and> (\<acute>Safe \<or> \<acute>obc\<subset>Blacks \<acute>M \<or> \<acute>l<\<acute>Queue \<and> (\<acute>l\<le>\<acute>Queue \<or> \<acute>obc\<subset>Blacks \<acute>M))\<rbrace>"
apply(unfold Mul_Propagate_Black_def)
apply annhoare
apply(simp_all add:Mul_PBInv_def mul_collector_defs Mul_Auxk_def Graph6 Graph7 Graph8 Graph12 mul_collector_defs Queue_def)
\<comment> \<open>8 subgoals left\<close>
apply force
apply force
apply force
apply(force simp add:BtoW_def Graph_defs)
\<comment> \<open>4 subgoals left\<close>
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
\<comment> \<open>2 subgoals left\<close>
apply clarify
apply(conjI_tac)
apply(disjE_tac)
 apply (simp_all)
apply clarify
apply(erule less_SucE)
 apply force
apply (simp add:BtoW_def)
\<comment> \<open>1 subgoal left\<close>
apply clarify
apply simp
apply(disjE_tac)
apply (simp_all)
apply(rule disjI1 , rule Graph1)
 apply simp_all
done

subsubsection \<open>Counting Black Nodes\<close>

definition Mul_CountInv :: "mul_gar_coll_state \<Rightarrow> nat \<Rightarrow> bool" where
  "Mul_CountInv \<equiv> \<guillemotleft> \<lambda>ind. {i. i<ind \<and> \<acute>Ma!i=Black}\<subseteq>\<acute>bc \<guillemotright>"

definition Mul_Count :: "nat \<Rightarrow>  mul_gar_coll_state ann_com" where
  "Mul_Count n \<equiv>
  \<lbrace>\<acute>Mul_Proper n \<and> Roots\<subseteq>Blacks \<acute>M
    \<and> \<acute>obc\<subseteq>Blacks \<acute>Ma \<and> Blacks \<acute>Ma\<subseteq>Blacks \<acute>M \<and> \<acute>bc\<subseteq>Blacks \<acute>M
    \<and> length \<acute>Ma=length \<acute>M
    \<and> (\<acute>Safe \<or> \<acute>obc\<subset>Blacks \<acute>Ma \<or> \<acute>l<\<acute>q \<and> (\<acute>q\<le>\<acute>Queue \<or> \<acute>obc\<subset>Blacks \<acute>M) )
    \<and> \<acute>q<n+1 \<and> \<acute>bc={}\<rbrace>
  \<acute>ind:=0;;
  \<lbrace>\<acute>Mul_Proper n \<and> Roots\<subseteq>Blacks \<acute>M
    \<and> \<acute>obc\<subseteq>Blacks \<acute>Ma \<and> Blacks \<acute>Ma\<subseteq>Blacks \<acute>M \<and> \<acute>bc\<subseteq>Blacks \<acute>M
    \<and> length \<acute>Ma=length \<acute>M
    \<and> (\<acute>Safe \<or> \<acute>obc\<subset>Blacks \<acute>Ma \<or> \<acute>l<\<acute>q \<and> (\<acute>q\<le>\<acute>Queue \<or> \<acute>obc\<subset>Blacks \<acute>M) )
    \<and> \<acute>q<n+1 \<and> \<acute>bc={} \<and> \<acute>ind=0\<rbrace>
  WHILE \<acute>ind<length \<acute>M
     INV \<lbrace>\<acute>Mul_Proper n \<and> Roots\<subseteq>Blacks \<acute>M
          \<and> \<acute>obc\<subseteq>Blacks \<acute>Ma \<and> Blacks \<acute>Ma\<subseteq>Blacks \<acute>M \<and> \<acute>bc\<subseteq>Blacks \<acute>M
          \<and> length \<acute>Ma=length \<acute>M \<and> \<acute>Mul_CountInv \<acute>ind
          \<and> (\<acute>Safe \<or> \<acute>obc\<subset>Blacks \<acute>Ma \<or> \<acute>l<\<acute>q \<and> (\<acute>q\<le>\<acute>Queue \<or> \<acute>obc\<subset>Blacks \<acute>M))
          \<and> \<acute>q<n+1 \<and> \<acute>ind\<le>length \<acute>M\<rbrace>
  DO \<lbrace>\<acute>Mul_Proper n \<and> Roots\<subseteq>Blacks \<acute>M
       \<and> \<acute>obc\<subseteq>Blacks \<acute>Ma \<and> Blacks \<acute>Ma\<subseteq>Blacks \<acute>M \<and> \<acute>bc\<subseteq>Blacks \<acute>M
       \<and> length \<acute>Ma=length \<acute>M \<and> \<acute>Mul_CountInv \<acute>ind
       \<and> (\<acute>Safe \<or> \<acute>obc\<subset>Blacks \<acute>Ma \<or> \<acute>l<\<acute>q \<and> (\<acute>q\<le>\<acute>Queue \<or> \<acute>obc\<subset>Blacks \<acute>M))
       \<and> \<acute>q<n+1 \<and> \<acute>ind<length \<acute>M\<rbrace>
     IF \<acute>M!\<acute>ind=Black
     THEN \<lbrace>\<acute>Mul_Proper n \<and> Roots\<subseteq>Blacks \<acute>M
            \<and> \<acute>obc\<subseteq>Blacks \<acute>Ma \<and> Blacks \<acute>Ma\<subseteq>Blacks \<acute>M \<and> \<acute>bc\<subseteq>Blacks \<acute>M
            \<and> length \<acute>Ma=length \<acute>M \<and> \<acute>Mul_CountInv \<acute>ind
            \<and> (\<acute>Safe \<or> \<acute>obc\<subset>Blacks \<acute>Ma \<or> \<acute>l<\<acute>q \<and> (\<acute>q\<le>\<acute>Queue \<or> \<acute>obc\<subset>Blacks \<acute>M))
            \<and> \<acute>q<n+1 \<and> \<acute>ind<length \<acute>M \<and> \<acute>M!\<acute>ind=Black\<rbrace>
          \<acute>bc:=insert \<acute>ind \<acute>bc
     FI;;
  \<lbrace>\<acute>Mul_Proper n \<and> Roots\<subseteq>Blacks \<acute>M
    \<and> \<acute>obc\<subseteq>Blacks \<acute>Ma \<and> Blacks \<acute>Ma\<subseteq>Blacks \<acute>M \<and> \<acute>bc\<subseteq>Blacks \<acute>M
    \<and> length \<acute>Ma=length \<acute>M \<and> \<acute>Mul_CountInv (\<acute>ind+1)
    \<and> (\<acute>Safe \<or> \<acute>obc\<subset>Blacks \<acute>Ma \<or> \<acute>l<\<acute>q \<and> (\<acute>q\<le>\<acute>Queue \<or> \<acute>obc\<subset>Blacks \<acute>M))
    \<and> \<acute>q<n+1 \<and> \<acute>ind<length \<acute>M\<rbrace>
  \<acute>ind:=\<acute>ind+1
  OD"

lemma Mul_Count:
  "\<turnstile> Mul_Count n
  \<lbrace>\<acute>Mul_Proper n \<and> Roots\<subseteq>Blacks \<acute>M
    \<and> \<acute>obc\<subseteq>Blacks \<acute>Ma \<and> Blacks \<acute>Ma\<subseteq>Blacks \<acute>M \<and> \<acute>bc\<subseteq>Blacks \<acute>M
    \<and> length \<acute>Ma=length \<acute>M \<and> Blacks \<acute>Ma\<subseteq>\<acute>bc
    \<and> (\<acute>Safe \<or> \<acute>obc\<subset>Blacks \<acute>Ma \<or> \<acute>l<\<acute>q \<and> (\<acute>q\<le>\<acute>Queue \<or> \<acute>obc\<subset>Blacks \<acute>M))
    \<and> \<acute>q<n+1\<rbrace>"
apply (unfold Mul_Count_def)
apply annhoare
apply(simp_all add:Mul_CountInv_def mul_collector_defs Mul_Auxk_def Graph6 Graph7 Graph8 Graph12 mul_collector_defs Queue_def)
\<comment> \<open>7 subgoals left\<close>
apply force
apply force
apply force
\<comment> \<open>4 subgoals left\<close>
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
\<comment> \<open>3 subgoals left\<close>
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
\<comment> \<open>2 subgoals left\<close>
apply force
\<comment> \<open>1 subgoal left\<close>
apply clarify
apply(drule_tac x = "ind x" in le_imp_less_or_eq)
apply (simp_all add:Blacks_def)
done

subsubsection \<open>Appending garbage nodes to the free list\<close>

axiomatization Append_to_free :: "nat \<times> edges \<Rightarrow> edges"
where
  Append_to_free0: "length (Append_to_free (i, e)) = length e" and
  Append_to_free1: "Proper_Edges (m, e)
                    \<Longrightarrow> Proper_Edges (m, Append_to_free(i, e))" and
  Append_to_free2: "i \<notin> Reach e
           \<Longrightarrow> n \<in> Reach (Append_to_free(i, e)) = ( n = i \<or> n \<in> Reach e)"

definition Mul_AppendInv :: "mul_gar_coll_state \<Rightarrow> nat \<Rightarrow> bool" where
  "Mul_AppendInv \<equiv> \<guillemotleft> \<lambda>ind. (\<forall>i. ind\<le>i \<longrightarrow> i<length \<acute>M \<longrightarrow> i\<in>Reach \<acute>E \<longrightarrow> \<acute>M!i=Black)\<guillemotright>"

definition Mul_Append :: "nat \<Rightarrow>  mul_gar_coll_state ann_com" where
  "Mul_Append n \<equiv>
  \<lbrace>\<acute>Mul_Proper n \<and> Roots\<subseteq>Blacks \<acute>M \<and> \<acute>Safe\<rbrace>
  \<acute>ind:=0;;
  \<lbrace>\<acute>Mul_Proper n \<and> Roots\<subseteq>Blacks \<acute>M \<and> \<acute>Safe \<and> \<acute>ind=0\<rbrace>
  WHILE \<acute>ind<length \<acute>M
    INV \<lbrace>\<acute>Mul_Proper n \<and> \<acute>Mul_AppendInv \<acute>ind \<and> \<acute>ind\<le>length \<acute>M\<rbrace>
  DO \<lbrace>\<acute>Mul_Proper n \<and> \<acute>Mul_AppendInv \<acute>ind \<and> \<acute>ind<length \<acute>M\<rbrace>
      IF \<acute>M!\<acute>ind=Black THEN
     \<lbrace>\<acute>Mul_Proper n \<and> \<acute>Mul_AppendInv \<acute>ind \<and> \<acute>ind<length \<acute>M \<and> \<acute>M!\<acute>ind=Black\<rbrace>
      \<acute>M:=\<acute>M[\<acute>ind:=White]
      ELSE
     \<lbrace>\<acute>Mul_Proper n \<and> \<acute>Mul_AppendInv \<acute>ind \<and> \<acute>ind<length \<acute>M \<and> \<acute>ind\<notin>Reach \<acute>E\<rbrace>
      \<acute>E:=Append_to_free(\<acute>ind,\<acute>E)
      FI;;
  \<lbrace>\<acute>Mul_Proper n \<and> \<acute>Mul_AppendInv (\<acute>ind+1) \<and> \<acute>ind<length \<acute>M\<rbrace>
   \<acute>ind:=\<acute>ind+1
  OD"

lemma Mul_Append:
  "\<turnstile> Mul_Append n
     \<lbrace>\<acute>Mul_Proper n\<rbrace>"
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

subsubsection \<open>Collector\<close>

definition Mul_Collector :: "nat \<Rightarrow>  mul_gar_coll_state ann_com" where
  "Mul_Collector n \<equiv>
\<lbrace>\<acute>Mul_Proper n\<rbrace>
WHILE True INV \<lbrace>\<acute>Mul_Proper n\<rbrace>
DO
Mul_Blacken_Roots n ;;
\<lbrace>\<acute>Mul_Proper n \<and> Roots\<subseteq>Blacks \<acute>M\<rbrace>
 \<acute>obc:={};;
\<lbrace>\<acute>Mul_Proper n \<and> Roots\<subseteq>Blacks \<acute>M \<and> \<acute>obc={}\<rbrace>
 \<acute>bc:=Roots;;
\<lbrace>\<acute>Mul_Proper n \<and> Roots\<subseteq>Blacks \<acute>M \<and> \<acute>obc={} \<and> \<acute>bc=Roots\<rbrace>
 \<acute>l:=0;;
\<lbrace>\<acute>Mul_Proper n \<and> Roots\<subseteq>Blacks \<acute>M \<and> \<acute>obc={} \<and> \<acute>bc=Roots \<and> \<acute>l=0\<rbrace>
 WHILE \<acute>l<n+1
   INV \<lbrace>\<acute>Mul_Proper n \<and> Roots\<subseteq>Blacks \<acute>M \<and> \<acute>bc\<subseteq>Blacks \<acute>M \<and>
         (\<acute>Safe \<or> (\<acute>l\<le>\<acute>Queue \<or> \<acute>bc\<subset>Blacks \<acute>M) \<and> \<acute>l<n+1)\<rbrace>
 DO \<lbrace>\<acute>Mul_Proper n \<and> Roots\<subseteq>Blacks \<acute>M \<and> \<acute>bc\<subseteq>Blacks \<acute>M
      \<and> (\<acute>Safe \<or> \<acute>l\<le>\<acute>Queue \<or> \<acute>bc\<subset>Blacks \<acute>M)\<rbrace>
    \<acute>obc:=\<acute>bc;;
    Mul_Propagate_Black n;;
    \<lbrace>\<acute>Mul_Proper n \<and> Roots\<subseteq>Blacks \<acute>M
      \<and> \<acute>obc\<subseteq>Blacks \<acute>M \<and> \<acute>bc\<subseteq>Blacks \<acute>M
      \<and> (\<acute>Safe \<or> \<acute>obc\<subset>Blacks \<acute>M \<or> \<acute>l<\<acute>Queue
      \<and> (\<acute>l\<le>\<acute>Queue \<or> \<acute>obc\<subset>Blacks \<acute>M))\<rbrace>
    \<acute>bc:={};;
    \<lbrace>\<acute>Mul_Proper n \<and> Roots\<subseteq>Blacks \<acute>M
      \<and> \<acute>obc\<subseteq>Blacks \<acute>M \<and> \<acute>bc\<subseteq>Blacks \<acute>M
      \<and> (\<acute>Safe \<or> \<acute>obc\<subset>Blacks \<acute>M \<or> \<acute>l<\<acute>Queue
      \<and> (\<acute>l\<le>\<acute>Queue \<or> \<acute>obc\<subset>Blacks \<acute>M)) \<and> \<acute>bc={}\<rbrace>
       \<langle> \<acute>Ma:=\<acute>M,, \<acute>q:=\<acute>Queue \<rangle>;;
    Mul_Count n;;
    \<lbrace>\<acute>Mul_Proper n \<and> Roots\<subseteq>Blacks \<acute>M
      \<and> \<acute>obc\<subseteq>Blacks \<acute>Ma \<and> Blacks \<acute>Ma\<subseteq>Blacks \<acute>M \<and> \<acute>bc\<subseteq>Blacks \<acute>M
      \<and> length \<acute>Ma=length \<acute>M \<and> Blacks \<acute>Ma\<subseteq>\<acute>bc
      \<and> (\<acute>Safe \<or> \<acute>obc\<subset>Blacks \<acute>Ma \<or> \<acute>l<\<acute>q \<and> (\<acute>q\<le>\<acute>Queue \<or> \<acute>obc\<subset>Blacks \<acute>M))
      \<and> \<acute>q<n+1\<rbrace>
    IF \<acute>obc=\<acute>bc THEN
    \<lbrace>\<acute>Mul_Proper n \<and> Roots\<subseteq>Blacks \<acute>M
      \<and> \<acute>obc\<subseteq>Blacks \<acute>Ma \<and> Blacks \<acute>Ma\<subseteq>Blacks \<acute>M \<and> \<acute>bc\<subseteq>Blacks \<acute>M
      \<and> length \<acute>Ma=length \<acute>M \<and> Blacks \<acute>Ma\<subseteq>\<acute>bc
      \<and> (\<acute>Safe \<or> \<acute>obc\<subset>Blacks \<acute>Ma \<or> \<acute>l<\<acute>q \<and> (\<acute>q\<le>\<acute>Queue \<or> \<acute>obc\<subset>Blacks \<acute>M))
      \<and> \<acute>q<n+1 \<and> \<acute>obc=\<acute>bc\<rbrace>
    \<acute>l:=\<acute>l+1
    ELSE \<lbrace>\<acute>Mul_Proper n \<and> Roots\<subseteq>Blacks \<acute>M
          \<and> \<acute>obc\<subseteq>Blacks \<acute>Ma \<and> Blacks \<acute>Ma\<subseteq>Blacks \<acute>M \<and> \<acute>bc\<subseteq>Blacks \<acute>M
          \<and> length \<acute>Ma=length \<acute>M \<and> Blacks \<acute>Ma\<subseteq>\<acute>bc
          \<and> (\<acute>Safe \<or> \<acute>obc\<subset>Blacks \<acute>Ma \<or> \<acute>l<\<acute>q \<and> (\<acute>q\<le>\<acute>Queue \<or> \<acute>obc\<subset>Blacks \<acute>M))
          \<and> \<acute>q<n+1 \<and> \<acute>obc\<noteq>\<acute>bc\<rbrace>
        \<acute>l:=0 FI
 OD;;
 Mul_Append n
OD"

lemmas mul_modules = Mul_Redirect_Edge_def Mul_Color_Target_def
 Mul_Blacken_Roots_def Mul_Propagate_Black_def
 Mul_Count_def Mul_Append_def

lemma Mul_Collector:
  "\<turnstile> Mul_Collector n
  \<lbrace>False\<rbrace>"
apply(unfold Mul_Collector_def)
apply annhoare
apply(simp_all only:pre.simps Mul_Blacken_Roots
       Mul_Propagate_Black Mul_Count Mul_Append)
apply(simp_all add:mul_modules)
apply(simp_all add:mul_collector_defs Queue_def)
apply force
apply force
apply force
apply (force simp add: less_Suc_eq_le)
apply force
apply (force dest:subset_antisym)
apply force
apply force
apply force
done

subsection \<open>Interference Freedom\<close>

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
\<comment> \<open>7 subgoals left\<close>
apply clarify
apply(disjE_tac)
  apply(simp_all add:Graph6)
 apply(rule impI,rule disjI1,rule subset_trans,erule Graph3,simp,simp)
apply(rule conjI)
 apply(rule impI,rule disjI2,rule disjI1,erule le_trans,force simp add:Queue_def less_Suc_eq_le le_length_filter_update)
apply(rule impI,rule disjI2,rule disjI1,erule le_trans,force simp add:Queue_def less_Suc_eq_le le_length_filter_update)
\<comment> \<open>6 subgoals left\<close>
apply clarify
apply(disjE_tac)
  apply(simp_all add:Graph6)
 apply(rule impI,rule disjI1,rule subset_trans,erule Graph3,simp,simp)
apply(rule conjI)
 apply(rule impI,rule disjI2,rule disjI1,erule le_trans,force simp add:Queue_def less_Suc_eq_le le_length_filter_update)
apply(rule impI,rule disjI2,rule disjI1,erule le_trans,force simp add:Queue_def less_Suc_eq_le le_length_filter_update)
\<comment> \<open>5 subgoals left\<close>
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
\<comment> \<open>4 subgoals left\<close>
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
\<comment> \<open>3 subgoals left\<close>
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
\<comment> \<open>2 subgoals left\<close>
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
\<comment> \<open>1 subgoal left\<close>
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
\<comment> \<open>7 subgoals left\<close>
apply clarify
apply (simp add:Graph7 Graph8 Graph12)
apply(disjE_tac)
  apply(simp add:Graph7 Graph8 Graph12)
 apply(case_tac "M x!(T (Muts x!j))=Black")
  apply(rule disjI2,rule disjI1, erule le_trans)
  apply(force simp add:Queue_def less_Suc_eq_le le_length_filter_update Graph10)
 apply((rule disjI2)+,erule subset_psubset_trans, erule Graph11, simp)
apply((rule disjI2)+,erule psubset_subset_trans, simp add: Graph9)
\<comment> \<open>6 subgoals left\<close>
apply clarify
apply (simp add:Graph7 Graph8 Graph12)
apply(disjE_tac)
  apply(simp add:Graph7 Graph8 Graph12)
 apply(case_tac "M x!(T (Muts x!j))=Black")
  apply(rule disjI2,rule disjI1, erule le_trans)
  apply(force simp add:Queue_def less_Suc_eq_le le_length_filter_update Graph10)
 apply((rule disjI2)+,erule subset_psubset_trans, erule Graph11, simp)
apply((rule disjI2)+,erule psubset_subset_trans, simp add: Graph9)
\<comment> \<open>5 subgoals left\<close>
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
\<comment> \<open>4 subgoals left\<close>
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
\<comment> \<open>3 subgoals left\<close>
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
\<comment> \<open>2 subgoals left\<close>
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
\<comment> \<open>1 subgoal left\<close>
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
\<comment> \<open>9 subgoals left\<close>
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
\<comment> \<open>8 subgoals left\<close>
apply(simp add:mul_mutator_defs nth_list_update)
\<comment> \<open>7 subgoals left\<close>
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
\<comment> \<open>6 subgoals left\<close>
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
\<comment> \<open>5 subgoals left\<close>
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
\<comment> \<open>4 subgoals left\<close>
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
\<comment> \<open>3 subgoals left\<close>
apply(simp add:mul_mutator_defs nth_list_update)
\<comment> \<open>2 subgoals left\<close>
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
\<comment> \<open>1 subgoal left\<close>
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
\<comment> \<open>6 subgoals left\<close>
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
\<comment> \<open>5 subgoals left\<close>
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
\<comment> \<open>4 subgoals left\<close>
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
\<comment> \<open>3 subgoals left\<close>
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
\<comment> \<open>2 subgoals left\<close>
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
\<comment> \<open>1 subgoal left\<close>
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
apply(tactic \<open>ALLGOALS (clarify_tac \<^context>)\<close>)
apply(simp_all add:Graph6 Append_to_free0 Append_to_free1 mul_collector_defs mul_mutator_defs Mul_AppendInv_def)
apply(erule_tac x=j in allE, force dest:Graph3)+
done

lemma Mul_interfree_Redirect_Edge_Append: "\<lbrakk>0\<le>j; j<n\<rbrakk>\<Longrightarrow>
  interfree_aux (Some(Mul_Redirect_Edge j n),{},Some(Mul_Append n))"
apply (unfold mul_modules)
apply interfree_aux
apply(tactic \<open>ALLGOALS (clarify_tac \<^context>)\<close>)
apply(simp_all add:mul_collector_defs Append_to_free0 Mul_AppendInv_def  mul_mutator_defs nth_list_update)
done

lemma Mul_interfree_Append_Color_Target: "\<lbrakk>0\<le>j; j<n\<rbrakk>\<Longrightarrow>
  interfree_aux (Some(Mul_Append n),{}, Some(Mul_Color_Target j n))"
apply (unfold mul_modules)
apply interfree_aux
apply(tactic \<open>ALLGOALS (clarify_tac \<^context>)\<close>)
apply(simp_all add:mul_mutator_defs mul_collector_defs Mul_AppendInv_def Graph7 Graph8 Append_to_free0 Append_to_free1
              Graph12 nth_list_update)
done

lemma Mul_interfree_Color_Target_Append: "\<lbrakk>0\<le>j; j<n\<rbrakk>\<Longrightarrow>
  interfree_aux (Some(Mul_Color_Target j n),{}, Some(Mul_Append n))"
apply (unfold mul_modules)
apply interfree_aux
apply(tactic \<open>ALLGOALS (clarify_tac \<^context>)\<close>)
apply(simp_all add: mul_mutator_defs nth_list_update)
apply(simp add:Mul_AppendInv_def Append_to_free0)
done

subsubsection \<open>Interference freedom Collector-Mutator\<close>

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
apply(tactic  \<open>TRYALL (interfree_aux_tac \<^context>)\<close>)
\<comment> \<open>42 subgoals left\<close>
apply (clarify,simp add:Graph6 Graph7 Graph8 Append_to_free0 Append_to_free1 Graph12)+
\<comment> \<open>24 subgoals left\<close>
apply(simp_all add:Graph6 Graph7 Graph8 Append_to_free0 Append_to_free1 Graph12)
\<comment> \<open>14 subgoals left\<close>
apply(tactic \<open>TRYALL (clarify_tac \<^context>)\<close>)
apply(simp_all add:Graph6 Graph7 Graph8 Append_to_free0 Append_to_free1 Graph12)
apply(tactic \<open>TRYALL (resolve_tac \<^context> [conjI])\<close>)
apply(tactic \<open>TRYALL (resolve_tac \<^context> [impI])\<close>)
apply(tactic \<open>TRYALL (eresolve_tac \<^context> [disjE])\<close>)
apply(tactic \<open>TRYALL (eresolve_tac \<^context> [conjE])\<close>)
apply(tactic \<open>TRYALL (eresolve_tac \<^context> [disjE])\<close>)
apply(tactic \<open>TRYALL (eresolve_tac \<^context> [disjE])\<close>)
\<comment> \<open>72 subgoals left\<close>
apply(simp_all add:Graph6 Graph7 Graph8 Append_to_free0 Append_to_free1 Graph12)
\<comment> \<open>35 subgoals left\<close>
apply(tactic \<open>TRYALL(EVERY'[resolve_tac \<^context> [disjI1],
    resolve_tac \<^context> @{thms subset_trans},
    eresolve_tac \<^context> @{thms Graph3},
    force_tac \<^context>,
    assume_tac \<^context>])\<close>)
\<comment> \<open>28 subgoals left\<close>
apply(tactic \<open>TRYALL (eresolve_tac \<^context> [conjE])\<close>)
apply(tactic \<open>TRYALL (eresolve_tac \<^context> [disjE])\<close>)
\<comment> \<open>34 subgoals left\<close>
apply(rule disjI2,rule disjI1,erule le_trans,force simp add:Queue_def less_Suc_eq_le le_length_filter_update)
apply(rule disjI2,rule disjI1,erule le_trans,force simp add:Queue_def less_Suc_eq_le le_length_filter_update)
apply(case_tac [!] "M x!(T (Muts x ! j))=Black")
apply(simp_all add:Graph10)
\<comment> \<open>47 subgoals left\<close>
apply(tactic \<open>TRYALL(EVERY'[REPEAT o resolve_tac \<^context> [disjI2],
    eresolve_tac \<^context> @{thms subset_psubset_trans},
    eresolve_tac \<^context> @{thms Graph11},
    force_tac \<^context>])\<close>)
\<comment> \<open>41 subgoals left\<close>
apply(tactic \<open>TRYALL(EVERY'[resolve_tac \<^context> [disjI2],
    resolve_tac \<^context> [disjI1],
    eresolve_tac \<^context> @{thms le_trans},
    force_tac (\<^context> addsimps @{thms Queue_def less_Suc_eq_le le_length_filter_update})])\<close>)
\<comment> \<open>35 subgoals left\<close>
apply(tactic \<open>TRYALL(EVERY'[resolve_tac \<^context> [disjI2],
    resolve_tac \<^context> [disjI1],
    eresolve_tac \<^context> @{thms psubset_subset_trans},
    resolve_tac \<^context> @{thms Graph9},
    force_tac \<^context>])\<close>)
\<comment> \<open>31 subgoals left\<close>
apply(tactic \<open>TRYALL(EVERY'[resolve_tac \<^context> [disjI2],
    resolve_tac \<^context> [disjI1],
    eresolve_tac \<^context> @{thms subset_psubset_trans},
    eresolve_tac \<^context> @{thms Graph11},
    force_tac \<^context>])\<close>)
\<comment> \<open>29 subgoals left\<close>
apply(tactic \<open>TRYALL(EVERY'[REPEAT o resolve_tac \<^context> [disjI2],
    eresolve_tac \<^context> @{thms subset_psubset_trans},
    eresolve_tac \<^context> @{thms subset_psubset_trans},
    eresolve_tac \<^context> @{thms Graph11},
    force_tac \<^context>])\<close>)
\<comment> \<open>25 subgoals left\<close>
apply(tactic \<open>TRYALL(EVERY'[resolve_tac \<^context> [disjI2],
    resolve_tac \<^context> [disjI2],
    resolve_tac \<^context> [disjI1],
    eresolve_tac \<^context> @{thms le_trans},
    force_tac (\<^context> addsimps @{thms Queue_def less_Suc_eq_le le_length_filter_update})])\<close>)
\<comment> \<open>10 subgoals left\<close>
apply(rule disjI2,rule disjI2,rule conjI,erule less_le_trans,force simp add:Queue_def less_Suc_eq_le le_length_filter_update, rule disjI1, rule less_imp_le, erule less_le_trans, force simp add:Queue_def less_Suc_eq_le le_length_filter_update)+
done

subsubsection \<open>Interference freedom Mutator-Collector\<close>

lemma Mul_interfree_Mutator_Collector: " j < n \<Longrightarrow>
  interfree_aux (Some (Mul_Mutator j n), {}, Some (Mul_Collector n))"
apply(unfold Mul_Collector_def Mul_Mutator_def)
apply interfree_aux
apply(simp_all add:mul_collector_mutator_interfree)
apply(unfold mul_modules mul_collector_defs mul_mutator_defs)
apply(tactic  \<open>TRYALL (interfree_aux_tac \<^context>)\<close>)
\<comment> \<open>76 subgoals left\<close>
apply (clarsimp simp add: nth_list_update)+
\<comment> \<open>56 subgoals left\<close>
apply (clarsimp simp add: Mul_AppendInv_def Append_to_free0 nth_list_update)+
done

subsubsection \<open>The Multi-Mutator Garbage Collection Algorithm\<close>

text \<open>The total number of verification conditions is 328\<close>

lemma Mul_Gar_Coll:
 "\<parallel>- \<lbrace>\<acute>Mul_Proper n \<and> \<acute>Mul_mut_init n \<and> (\<forall>i<n. Z (\<acute>Muts!i))\<rbrace>
 COBEGIN
  Mul_Collector n
 \<lbrace>False\<rbrace>
 \<parallel>
 SCHEME  [0\<le> j< n]
  Mul_Mutator j n
 \<lbrace>False\<rbrace>
 COEND
 \<lbrace>False\<rbrace>"
apply oghoare
\<comment> \<open>Strengthening the precondition\<close>
apply(rule Int_greatest)
 apply (case_tac n)
  apply(force simp add: Mul_Collector_def mul_mutator_defs mul_collector_defs nth_append)
 apply(simp add: Mul_Mutator_def mul_collector_defs mul_mutator_defs nth_append)
 apply force
apply clarify
apply(case_tac i)
 apply(simp add:Mul_Collector_def mul_mutator_defs mul_collector_defs nth_append)
apply(simp add: Mul_Mutator_def mul_mutator_defs mul_collector_defs nth_append nth_map_upt)
\<comment> \<open>Collector\<close>
apply(rule Mul_Collector)
\<comment> \<open>Mutator\<close>
apply(erule Mul_Mutator)
\<comment> \<open>Interference freedom\<close>
apply(simp add:Mul_interfree_Collector_Mutator)
apply(simp add:Mul_interfree_Mutator_Collector)
apply(simp add:Mul_interfree_Mutator_Mutator)
\<comment> \<open>Weakening of the postcondition\<close>
apply(case_tac n)
 apply(simp add:Mul_Collector_def mul_mutator_defs mul_collector_defs nth_append)
apply(simp add:Mul_Mutator_def mul_mutator_defs mul_collector_defs nth_append)
done

end
