header {* \section{The Single Mutator Case} *}

theory Gar_Coll imports Graph OG_Syntax begin

declare psubsetE [rule del]

text {* Declaration of variables: *}

record gar_coll_state =
  M :: nodes
  E :: edges
  bc :: "nat set"
  obc :: "nat set"
  Ma :: nodes
  ind :: nat 
  k :: nat
  z :: bool

subsection {* The Mutator *}

text {* The mutator first redirects an arbitrary edge @{text "R"} from
an arbitrary accessible node towards an arbitrary accessible node
@{text "T"}.  It then colors the new target @{text "T"} black. 

We declare the arbitrarily selected node and edge as constants:*}

consts R :: nat  T :: nat

text {* \noindent The following predicate states, given a list of
nodes @{text "m"} and a list of edges @{text "e"}, the conditions
under which the selected edge @{text "R"} and node @{text "T"} are
valid: *}

definition Mut_init :: "gar_coll_state \<Rightarrow> bool" where
  "Mut_init \<equiv> \<guillemotleft> T \<in> Reach \<acute>E \<and> R < length \<acute>E \<and> T < length \<acute>M \<guillemotright>"

text {* \noindent For the mutator we
consider two modules, one for each action.  An auxiliary variable
@{text "\<acute>z"} is set to false if the mutator has already redirected an
edge but has not yet colored the new target.   *}

definition Redirect_Edge :: "gar_coll_state ann_com" where
  "Redirect_Edge \<equiv> .{\<acute>Mut_init \<and> \<acute>z}. \<langle>\<acute>E:=\<acute>E[R:=(fst(\<acute>E!R), T)],, \<acute>z:= (\<not>\<acute>z)\<rangle>"

definition Color_Target :: "gar_coll_state ann_com" where
  "Color_Target \<equiv> .{\<acute>Mut_init \<and> \<not>\<acute>z}. \<langle>\<acute>M:=\<acute>M[T:=Black],, \<acute>z:= (\<not>\<acute>z)\<rangle>"

definition Mutator :: "gar_coll_state ann_com" where
  "Mutator \<equiv>
  .{\<acute>Mut_init \<and> \<acute>z}. 
  WHILE True INV .{\<acute>Mut_init \<and> \<acute>z}. 
  DO  Redirect_Edge ;; Color_Target  OD"

subsubsection {* Correctness of the mutator *}

lemmas mutator_defs = Mut_init_def Redirect_Edge_def Color_Target_def

lemma Redirect_Edge: 
  "\<turnstile> Redirect_Edge pre(Color_Target)"
apply (unfold mutator_defs)
apply annhoare
apply(simp_all)
apply(force elim:Graph2)
done

lemma Color_Target:
  "\<turnstile> Color_Target .{\<acute>Mut_init \<and> \<acute>z}."
apply (unfold mutator_defs)
apply annhoare
apply(simp_all)
done

lemma Mutator: 
 "\<turnstile> Mutator .{False}."
apply(unfold Mutator_def)
apply annhoare
apply(simp_all add:Redirect_Edge Color_Target)
apply(simp add:mutator_defs Redirect_Edge_def)
done

subsection {* The Collector *}

text {* \noindent A constant @{text "M_init"} is used to give @{text "\<acute>Ma"} a
suitable first value, defined as a list of nodes where only the @{text
"Roots"} are black. *}

consts  M_init :: nodes

definition Proper_M_init :: "gar_coll_state \<Rightarrow> bool" where
  "Proper_M_init \<equiv>  \<guillemotleft> Blacks M_init=Roots \<and> length M_init=length \<acute>M \<guillemotright>"
 
definition Proper :: "gar_coll_state \<Rightarrow> bool" where
  "Proper \<equiv> \<guillemotleft> Proper_Roots \<acute>M \<and> Proper_Edges(\<acute>M, \<acute>E) \<and> \<acute>Proper_M_init \<guillemotright>"

definition Safe :: "gar_coll_state \<Rightarrow> bool" where
  "Safe \<equiv> \<guillemotleft> Reach \<acute>E \<subseteq> Blacks \<acute>M \<guillemotright>"

lemmas collector_defs = Proper_M_init_def Proper_def Safe_def

subsubsection {* Blackening the roots *}

definition Blacken_Roots :: " gar_coll_state ann_com" where
  "Blacken_Roots \<equiv> 
  .{\<acute>Proper}.
  \<acute>ind:=0;;
  .{\<acute>Proper \<and> \<acute>ind=0}.
  WHILE \<acute>ind<length \<acute>M 
   INV .{\<acute>Proper \<and> (\<forall>i<\<acute>ind. i \<in> Roots \<longrightarrow> \<acute>M!i=Black) \<and> \<acute>ind\<le>length \<acute>M}.
  DO .{\<acute>Proper \<and> (\<forall>i<\<acute>ind. i \<in> Roots \<longrightarrow> \<acute>M!i=Black) \<and> \<acute>ind<length \<acute>M}.
   IF \<acute>ind\<in>Roots THEN 
   .{\<acute>Proper \<and> (\<forall>i<\<acute>ind. i \<in> Roots \<longrightarrow> \<acute>M!i=Black) \<and> \<acute>ind<length \<acute>M \<and> \<acute>ind\<in>Roots}. 
    \<acute>M:=\<acute>M[\<acute>ind:=Black] FI;;
   .{\<acute>Proper \<and> (\<forall>i<\<acute>ind+1. i \<in> Roots \<longrightarrow> \<acute>M!i=Black) \<and> \<acute>ind<length \<acute>M}.
    \<acute>ind:=\<acute>ind+1 
  OD"

lemma Blacken_Roots: 
 "\<turnstile> Blacken_Roots .{\<acute>Proper \<and> Roots\<subseteq>Blacks \<acute>M}."
apply (unfold Blacken_Roots_def)
apply annhoare
apply(simp_all add:collector_defs Graph_defs)
apply safe
apply(simp_all add:nth_list_update)
  apply (erule less_SucE)
   apply simp+
 apply force
apply force
done

subsubsection {* Propagating black *}

definition PBInv :: "gar_coll_state \<Rightarrow> nat \<Rightarrow> bool" where
  "PBInv \<equiv> \<guillemotleft> \<lambda>ind. \<acute>obc < Blacks \<acute>M \<or> (\<forall>i <ind. \<not>BtoW (\<acute>E!i, \<acute>M) \<or>
   (\<not>\<acute>z \<and> i=R \<and> (snd(\<acute>E!R)) = T \<and> (\<exists>r. ind \<le> r \<and> r < length \<acute>E \<and> BtoW(\<acute>E!r,\<acute>M))))\<guillemotright>"

definition Propagate_Black_aux :: "gar_coll_state ann_com" where
  "Propagate_Black_aux \<equiv>
  .{\<acute>Proper \<and> Roots\<subseteq>Blacks \<acute>M \<and> \<acute>obc\<subseteq>Blacks \<acute>M \<and> \<acute>bc\<subseteq>Blacks \<acute>M}.
  \<acute>ind:=0;;
  .{\<acute>Proper \<and> Roots\<subseteq>Blacks \<acute>M \<and> \<acute>obc\<subseteq>Blacks \<acute>M \<and> \<acute>bc\<subseteq>Blacks \<acute>M \<and> \<acute>ind=0}. 
  WHILE \<acute>ind<length \<acute>E 
   INV .{\<acute>Proper \<and> Roots\<subseteq>Blacks \<acute>M \<and> \<acute>obc\<subseteq>Blacks \<acute>M \<and> \<acute>bc\<subseteq>Blacks \<acute>M 
         \<and> \<acute>PBInv \<acute>ind \<and> \<acute>ind\<le>length \<acute>E}.
  DO .{\<acute>Proper \<and> Roots\<subseteq>Blacks \<acute>M \<and> \<acute>obc\<subseteq>Blacks \<acute>M \<and> \<acute>bc\<subseteq>Blacks \<acute>M 
       \<and> \<acute>PBInv \<acute>ind \<and> \<acute>ind<length \<acute>E}. 
   IF \<acute>M!(fst (\<acute>E!\<acute>ind)) = Black THEN 
    .{\<acute>Proper \<and> Roots\<subseteq>Blacks \<acute>M \<and> \<acute>obc\<subseteq>Blacks \<acute>M \<and> \<acute>bc\<subseteq>Blacks \<acute>M 
       \<and> \<acute>PBInv \<acute>ind \<and> \<acute>ind<length \<acute>E \<and> \<acute>M!fst(\<acute>E!\<acute>ind)=Black}.
     \<acute>M:=\<acute>M[snd(\<acute>E!\<acute>ind):=Black];;
    .{\<acute>Proper \<and> Roots\<subseteq>Blacks \<acute>M \<and> \<acute>obc\<subseteq>Blacks \<acute>M \<and> \<acute>bc\<subseteq>Blacks \<acute>M 
       \<and> \<acute>PBInv (\<acute>ind + 1) \<and> \<acute>ind<length \<acute>E}.
     \<acute>ind:=\<acute>ind+1
   FI
  OD"

lemma Propagate_Black_aux: 
  "\<turnstile>  Propagate_Black_aux
  .{\<acute>Proper \<and> Roots\<subseteq>Blacks \<acute>M \<and> \<acute>obc\<subseteq>Blacks \<acute>M \<and> \<acute>bc\<subseteq>Blacks \<acute>M 
    \<and> ( \<acute>obc < Blacks \<acute>M \<or> \<acute>Safe)}."
apply (unfold Propagate_Black_aux_def  PBInv_def collector_defs)
apply annhoare
apply(simp_all add:Graph6 Graph7 Graph8 Graph12)
      apply force
     apply force
    apply force
--{* 4 subgoals left *}
apply clarify
apply(simp add:Proper_Edges_def Proper_Roots_def Graph6 Graph7 Graph8 Graph12)
apply (erule disjE)
 apply(rule disjI1)
 apply(erule Graph13)
 apply force
apply (case_tac "M x ! snd (E x ! ind x)=Black")
 apply (simp add: Graph10 BtoW_def)
 apply (rule disjI2)
 apply clarify
 apply (erule less_SucE)
  apply (erule_tac x=i in allE , erule (1) notE impE)
  apply simp
  apply clarify
  apply (drule_tac y = r in le_imp_less_or_eq)
  apply (erule disjE)
   apply (subgoal_tac "Suc (ind x)\<le>r")
    apply fast
   apply arith
  apply fast
 apply fast
apply(rule disjI1)
apply(erule subset_psubset_trans)
apply(erule Graph11)
apply fast
--{* 3 subgoals left *}
apply force
apply force
--{* last *}
apply clarify
apply simp
apply(subgoal_tac "ind x = length (E x)")
 apply (simp)
 apply(drule Graph1)
   apply simp
  apply clarify
  apply(erule allE, erule impE, assumption)
  apply force
 apply force
apply arith
done

subsubsection {* Refining propagating black *}

definition Auxk :: "gar_coll_state \<Rightarrow> bool" where
  "Auxk \<equiv> \<guillemotleft>\<acute>k<length \<acute>M \<and> (\<acute>M!\<acute>k\<noteq>Black \<or> \<not>BtoW(\<acute>E!\<acute>ind, \<acute>M) \<or> 
          \<acute>obc<Blacks \<acute>M \<or> (\<not>\<acute>z \<and> \<acute>ind=R \<and> snd(\<acute>E!R)=T  
          \<and> (\<exists>r. \<acute>ind<r \<and> r<length \<acute>E \<and> BtoW(\<acute>E!r, \<acute>M))))\<guillemotright>"

definition Propagate_Black :: " gar_coll_state ann_com" where
  "Propagate_Black \<equiv>
  .{\<acute>Proper \<and> Roots\<subseteq>Blacks \<acute>M \<and> \<acute>obc\<subseteq>Blacks \<acute>M \<and> \<acute>bc\<subseteq>Blacks \<acute>M}.
  \<acute>ind:=0;;
  .{\<acute>Proper \<and> Roots\<subseteq>Blacks \<acute>M \<and> \<acute>obc\<subseteq>Blacks \<acute>M \<and> \<acute>bc\<subseteq>Blacks \<acute>M \<and> \<acute>ind=0}.
  WHILE \<acute>ind<length \<acute>E 
   INV .{\<acute>Proper \<and> Roots\<subseteq>Blacks \<acute>M \<and> \<acute>obc\<subseteq>Blacks \<acute>M \<and> \<acute>bc\<subseteq>Blacks \<acute>M 
         \<and> \<acute>PBInv \<acute>ind \<and> \<acute>ind\<le>length \<acute>E}.
  DO .{\<acute>Proper \<and> Roots\<subseteq>Blacks \<acute>M \<and> \<acute>obc\<subseteq>Blacks \<acute>M \<and> \<acute>bc\<subseteq>Blacks \<acute>M 
       \<and> \<acute>PBInv \<acute>ind \<and> \<acute>ind<length \<acute>E}. 
   IF (\<acute>M!(fst (\<acute>E!\<acute>ind)))=Black THEN 
    .{\<acute>Proper \<and> Roots\<subseteq>Blacks \<acute>M \<and> \<acute>obc\<subseteq>Blacks \<acute>M \<and> \<acute>bc\<subseteq>Blacks \<acute>M 
      \<and> \<acute>PBInv \<acute>ind \<and> \<acute>ind<length \<acute>E \<and> (\<acute>M!fst(\<acute>E!\<acute>ind))=Black}.
     \<acute>k:=(snd(\<acute>E!\<acute>ind));;
    .{\<acute>Proper \<and> Roots\<subseteq>Blacks \<acute>M \<and> \<acute>obc\<subseteq>Blacks \<acute>M \<and> \<acute>bc\<subseteq>Blacks \<acute>M 
      \<and> \<acute>PBInv \<acute>ind \<and> \<acute>ind<length \<acute>E \<and> (\<acute>M!fst(\<acute>E!\<acute>ind))=Black 
      \<and> \<acute>Auxk}.
     \<langle>\<acute>M:=\<acute>M[\<acute>k:=Black],, \<acute>ind:=\<acute>ind+1\<rangle>
   ELSE .{\<acute>Proper \<and> Roots\<subseteq>Blacks \<acute>M \<and> \<acute>obc\<subseteq>Blacks \<acute>M \<and> \<acute>bc\<subseteq>Blacks \<acute>M 
          \<and> \<acute>PBInv \<acute>ind \<and> \<acute>ind<length \<acute>E}. 
         \<langle>IF (\<acute>M!(fst (\<acute>E!\<acute>ind)))\<noteq>Black THEN \<acute>ind:=\<acute>ind+1 FI\<rangle> 
   FI
  OD"

lemma Propagate_Black: 
  "\<turnstile>  Propagate_Black
  .{\<acute>Proper \<and> Roots\<subseteq>Blacks \<acute>M \<and> \<acute>obc\<subseteq>Blacks \<acute>M \<and> \<acute>bc\<subseteq>Blacks \<acute>M 
    \<and> ( \<acute>obc < Blacks \<acute>M \<or> \<acute>Safe)}."
apply (unfold Propagate_Black_def  PBInv_def Auxk_def collector_defs)
apply annhoare
apply(simp_all add: Graph6 Graph7 Graph8 Graph12)
       apply force
      apply force
     apply force
--{* 5 subgoals left *}
apply clarify
apply(simp add:BtoW_def Proper_Edges_def)
--{* 4 subgoals left *}
apply clarify
apply(simp add:Proper_Edges_def Graph6 Graph7 Graph8 Graph12)
apply (erule disjE)
 apply (rule disjI1)
 apply (erule psubset_subset_trans)
 apply (erule Graph9)
apply (case_tac "M x!k x=Black")
 apply (case_tac "M x ! snd (E x ! ind x)=Black")
  apply (simp add: Graph10 BtoW_def)
  apply (rule disjI2)
  apply clarify
  apply (erule less_SucE)
   apply (erule_tac x=i in allE , erule (1) notE impE)
   apply simp
   apply clarify
   apply (drule_tac y = r in le_imp_less_or_eq)
   apply (erule disjE)
    apply (subgoal_tac "Suc (ind x)\<le>r")
     apply fast
    apply arith
   apply fast
  apply fast
 apply (simp add: Graph10 BtoW_def)
 apply (erule disjE)
  apply (erule disjI1)
 apply clarify
 apply (erule less_SucE)
  apply force
 apply simp
 apply (subgoal_tac "Suc R\<le>r")
  apply fast
 apply arith
apply(rule disjI1)
apply(erule subset_psubset_trans)
apply(erule Graph11)
apply fast
--{* 2 subgoals left *}
apply clarify
apply(simp add:Proper_Edges_def Graph6 Graph7 Graph8 Graph12)
apply (erule disjE)
 apply fast
apply clarify
apply (erule less_SucE)
 apply (erule_tac x=i in allE , erule (1) notE impE)
 apply simp
 apply clarify
 apply (drule_tac y = r in le_imp_less_or_eq)
 apply (erule disjE)
  apply (subgoal_tac "Suc (ind x)\<le>r")
   apply fast
  apply arith
 apply (simp add: BtoW_def)
apply (simp add: BtoW_def)
--{* last *}
apply clarify
apply simp
apply(subgoal_tac "ind x = length (E x)")
 apply (simp)
 apply(drule Graph1)
   apply simp
  apply clarify  
  apply(erule allE, erule impE, assumption)
  apply force
 apply force
apply arith
done

subsubsection {* Counting black nodes *}

definition CountInv :: "gar_coll_state \<Rightarrow> nat \<Rightarrow> bool" where
  "CountInv \<equiv> \<guillemotleft> \<lambda>ind. {i. i<ind \<and> \<acute>Ma!i=Black}\<subseteq>\<acute>bc \<guillemotright>"

definition Count :: " gar_coll_state ann_com" where
  "Count \<equiv>
  .{\<acute>Proper \<and> Roots\<subseteq>Blacks \<acute>M 
    \<and> \<acute>obc\<subseteq>Blacks \<acute>Ma \<and> Blacks \<acute>Ma\<subseteq>Blacks \<acute>M \<and> \<acute>bc\<subseteq>Blacks \<acute>M 
    \<and> length \<acute>Ma=length \<acute>M \<and> (\<acute>obc < Blacks \<acute>Ma \<or> \<acute>Safe) \<and> \<acute>bc={}}.
  \<acute>ind:=0;;
  .{\<acute>Proper \<and> Roots\<subseteq>Blacks \<acute>M 
    \<and> \<acute>obc\<subseteq>Blacks \<acute>Ma \<and> Blacks \<acute>Ma\<subseteq>Blacks \<acute>M \<and> \<acute>bc\<subseteq>Blacks \<acute>M 
   \<and> length \<acute>Ma=length \<acute>M \<and> (\<acute>obc < Blacks \<acute>Ma \<or> \<acute>Safe) \<and> \<acute>bc={} 
   \<and> \<acute>ind=0}.
   WHILE \<acute>ind<length \<acute>M 
     INV .{\<acute>Proper \<and> Roots\<subseteq>Blacks \<acute>M 
           \<and> \<acute>obc\<subseteq>Blacks \<acute>Ma \<and> Blacks \<acute>Ma\<subseteq>Blacks \<acute>M \<and> \<acute>bc\<subseteq>Blacks \<acute>M 
           \<and> length \<acute>Ma=length \<acute>M \<and> \<acute>CountInv \<acute>ind
           \<and> ( \<acute>obc < Blacks \<acute>Ma \<or> \<acute>Safe) \<and> \<acute>ind\<le>length \<acute>M}.
   DO .{\<acute>Proper \<and> Roots\<subseteq>Blacks \<acute>M 
         \<and> \<acute>obc\<subseteq>Blacks \<acute>Ma \<and> Blacks \<acute>Ma\<subseteq>Blacks \<acute>M \<and> \<acute>bc\<subseteq>Blacks \<acute>M 
         \<and> length \<acute>Ma=length \<acute>M \<and> \<acute>CountInv \<acute>ind 
         \<and> ( \<acute>obc < Blacks \<acute>Ma \<or> \<acute>Safe) \<and> \<acute>ind<length \<acute>M}. 
       IF \<acute>M!\<acute>ind=Black 
          THEN .{\<acute>Proper \<and> Roots\<subseteq>Blacks \<acute>M 
                 \<and> \<acute>obc\<subseteq>Blacks \<acute>Ma \<and> Blacks \<acute>Ma\<subseteq>Blacks \<acute>M \<and> \<acute>bc\<subseteq>Blacks \<acute>M 
                 \<and> length \<acute>Ma=length \<acute>M \<and> \<acute>CountInv \<acute>ind
                 \<and> ( \<acute>obc < Blacks \<acute>Ma \<or> \<acute>Safe) \<and> \<acute>ind<length \<acute>M \<and> \<acute>M!\<acute>ind=Black}.
          \<acute>bc:=insert \<acute>ind \<acute>bc
       FI;;
      .{\<acute>Proper \<and> Roots\<subseteq>Blacks \<acute>M 
        \<and> \<acute>obc\<subseteq>Blacks \<acute>Ma \<and> Blacks \<acute>Ma\<subseteq>Blacks \<acute>M \<and> \<acute>bc\<subseteq>Blacks \<acute>M 
        \<and> length \<acute>Ma=length \<acute>M \<and> \<acute>CountInv (\<acute>ind+1)
        \<and> ( \<acute>obc < Blacks \<acute>Ma \<or> \<acute>Safe) \<and> \<acute>ind<length \<acute>M}.
      \<acute>ind:=\<acute>ind+1
   OD"

lemma Count: 
  "\<turnstile> Count 
  .{\<acute>Proper \<and> Roots\<subseteq>Blacks \<acute>M 
   \<and> \<acute>obc\<subseteq>Blacks \<acute>Ma \<and> Blacks \<acute>Ma\<subseteq>\<acute>bc \<and> \<acute>bc\<subseteq>Blacks \<acute>M \<and> length \<acute>Ma=length \<acute>M
   \<and> (\<acute>obc < Blacks \<acute>Ma \<or> \<acute>Safe)}."
apply(unfold Count_def)
apply annhoare
apply(simp_all add:CountInv_def Graph6 Graph7 Graph8 Graph12 Blacks_def collector_defs)
      apply force
     apply force
    apply force
   apply clarify
   apply simp
   apply(fast elim:less_SucE)
  apply clarify
  apply simp
  apply(fast elim:less_SucE)
 apply force
apply force
done

subsubsection {* Appending garbage nodes to the free list *}

axiomatization Append_to_free :: "nat \<times> edges \<Rightarrow> edges"
where
  Append_to_free0: "length (Append_to_free (i, e)) = length e" and
  Append_to_free1: "Proper_Edges (m, e) 
                   \<Longrightarrow> Proper_Edges (m, Append_to_free(i, e))" and
  Append_to_free2: "i \<notin> Reach e 
     \<Longrightarrow> n \<in> Reach (Append_to_free(i, e)) = ( n = i \<or> n \<in> Reach e)"

definition AppendInv :: "gar_coll_state \<Rightarrow> nat \<Rightarrow> bool" where
  "AppendInv \<equiv> \<guillemotleft>\<lambda>ind. \<forall>i<length \<acute>M. ind\<le>i \<longrightarrow> i\<in>Reach \<acute>E \<longrightarrow> \<acute>M!i=Black\<guillemotright>"

definition Append :: "gar_coll_state ann_com" where
   "Append \<equiv>
  .{\<acute>Proper \<and> Roots\<subseteq>Blacks \<acute>M \<and> \<acute>Safe}.
  \<acute>ind:=0;;
  .{\<acute>Proper \<and> Roots\<subseteq>Blacks \<acute>M \<and> \<acute>Safe \<and> \<acute>ind=0}.
    WHILE \<acute>ind<length \<acute>M 
      INV .{\<acute>Proper \<and> \<acute>AppendInv \<acute>ind \<and> \<acute>ind\<le>length \<acute>M}.
    DO .{\<acute>Proper \<and> \<acute>AppendInv \<acute>ind \<and> \<acute>ind<length \<acute>M}.
       IF \<acute>M!\<acute>ind=Black THEN 
          .{\<acute>Proper \<and> \<acute>AppendInv \<acute>ind \<and> \<acute>ind<length \<acute>M \<and> \<acute>M!\<acute>ind=Black}. 
          \<acute>M:=\<acute>M[\<acute>ind:=White] 
       ELSE .{\<acute>Proper \<and> \<acute>AppendInv \<acute>ind \<and> \<acute>ind<length \<acute>M \<and> \<acute>ind\<notin>Reach \<acute>E}.
              \<acute>E:=Append_to_free(\<acute>ind,\<acute>E)
       FI;;
     .{\<acute>Proper \<and> \<acute>AppendInv (\<acute>ind+1) \<and> \<acute>ind<length \<acute>M}. 
       \<acute>ind:=\<acute>ind+1
    OD"

lemma Append: 
  "\<turnstile> Append .{\<acute>Proper}."
apply(unfold Append_def AppendInv_def)
apply annhoare
apply(simp_all add:collector_defs Graph6 Graph7 Graph8 Append_to_free0 Append_to_free1 Graph12)
       apply(force simp:Blacks_def nth_list_update)
      apply force
     apply force
    apply(force simp add:Graph_defs)
   apply force
  apply clarify
  apply simp
  apply(rule conjI)
   apply (erule Append_to_free1)
  apply clarify
  apply (drule_tac n = "i" in Append_to_free2)
  apply force
 apply force
apply force
done

subsubsection {* Correctness of the Collector *}

definition Collector :: " gar_coll_state ann_com" where
  "Collector \<equiv>
.{\<acute>Proper}.  
 WHILE True INV .{\<acute>Proper}. 
 DO  
  Blacken_Roots;; 
  .{\<acute>Proper \<and> Roots\<subseteq>Blacks \<acute>M}.  
   \<acute>obc:={};; 
  .{\<acute>Proper \<and> Roots\<subseteq>Blacks \<acute>M \<and> \<acute>obc={}}. 
   \<acute>bc:=Roots;; 
  .{\<acute>Proper \<and> Roots\<subseteq>Blacks \<acute>M \<and> \<acute>obc={} \<and> \<acute>bc=Roots}. 
   \<acute>Ma:=M_init;;  
  .{\<acute>Proper \<and> Roots\<subseteq>Blacks \<acute>M \<and> \<acute>obc={} \<and> \<acute>bc=Roots \<and> \<acute>Ma=M_init}. 
   WHILE \<acute>obc\<noteq>\<acute>bc  
     INV .{\<acute>Proper \<and> Roots\<subseteq>Blacks \<acute>M 
           \<and> \<acute>obc\<subseteq>Blacks \<acute>Ma \<and> Blacks \<acute>Ma\<subseteq>\<acute>bc \<and> \<acute>bc\<subseteq>Blacks \<acute>M 
           \<and> length \<acute>Ma=length \<acute>M \<and> (\<acute>obc < Blacks \<acute>Ma \<or> \<acute>Safe)}. 
   DO .{\<acute>Proper \<and> Roots\<subseteq>Blacks \<acute>M \<and> \<acute>bc\<subseteq>Blacks \<acute>M}.
       \<acute>obc:=\<acute>bc;;
       Propagate_Black;; 
      .{\<acute>Proper \<and> Roots\<subseteq>Blacks \<acute>M \<and> \<acute>obc\<subseteq>Blacks \<acute>M \<and> \<acute>bc\<subseteq>Blacks \<acute>M 
        \<and> (\<acute>obc < Blacks \<acute>M \<or> \<acute>Safe)}. 
       \<acute>Ma:=\<acute>M;;
      .{\<acute>Proper \<and> Roots\<subseteq>Blacks \<acute>M \<and> \<acute>obc\<subseteq>Blacks \<acute>Ma 
        \<and> Blacks \<acute>Ma\<subseteq>Blacks \<acute>M \<and> \<acute>bc\<subseteq>Blacks \<acute>M \<and> length \<acute>Ma=length \<acute>M 
        \<and> ( \<acute>obc < Blacks \<acute>Ma \<or> \<acute>Safe)}.
       \<acute>bc:={};;
       Count 
   OD;; 
  Append  
 OD"

lemma Collector: 
  "\<turnstile> Collector .{False}."
apply(unfold Collector_def)
apply annhoare
apply(simp_all add: Blacken_Roots Propagate_Black Count Append)
apply(simp_all add:Blacken_Roots_def Propagate_Black_def Count_def Append_def collector_defs)
   apply (force simp add: Proper_Roots_def)
  apply force
 apply force
apply clarify
apply (erule disjE)
apply(simp add:psubsetI)
 apply(force dest:subset_antisym)
done

subsection {* Interference Freedom *}

lemmas modules = Redirect_Edge_def Color_Target_def Blacken_Roots_def 
                 Propagate_Black_def Count_def Append_def
lemmas Invariants = PBInv_def Auxk_def CountInv_def AppendInv_def
lemmas abbrev = collector_defs mutator_defs Invariants

lemma interfree_Blacken_Roots_Redirect_Edge: 
 "interfree_aux (Some Blacken_Roots, {}, Some Redirect_Edge)"
apply (unfold modules)
apply interfree_aux
apply safe
apply (simp_all add:Graph6 Graph12 abbrev)
done

lemma interfree_Redirect_Edge_Blacken_Roots: 
  "interfree_aux (Some Redirect_Edge, {}, Some Blacken_Roots)"
apply (unfold modules)
apply interfree_aux
apply safe
apply(simp add:abbrev)+
done

lemma interfree_Blacken_Roots_Color_Target: 
  "interfree_aux (Some Blacken_Roots, {}, Some Color_Target)"
apply (unfold modules)
apply interfree_aux
apply safe
apply(simp_all add:Graph7 Graph8 nth_list_update abbrev)
done

lemma interfree_Color_Target_Blacken_Roots: 
  "interfree_aux (Some Color_Target, {}, Some Blacken_Roots)"
apply (unfold modules )
apply interfree_aux
apply safe
apply(simp add:abbrev)+
done

lemma interfree_Propagate_Black_Redirect_Edge: 
  "interfree_aux (Some Propagate_Black, {}, Some Redirect_Edge)"
apply (unfold modules )
apply interfree_aux
--{* 11 subgoals left *}
apply(clarify, simp add:abbrev Graph6 Graph12)
apply(clarify, simp add:abbrev Graph6 Graph12)
apply(clarify, simp add:abbrev Graph6 Graph12)
apply(clarify, simp add:abbrev Graph6 Graph12)
apply(erule conjE)+
apply(erule disjE, erule disjI1, rule disjI2, rule allI, (rule impI)+, case_tac "R=i", rule conjI, erule sym)
 apply(erule Graph4) 
   apply(simp)+
  apply (simp add:BtoW_def)
 apply (simp add:BtoW_def)
apply(rule conjI)
 apply (force simp add:BtoW_def)
apply(erule Graph4)
   apply simp+
--{* 7 subgoals left *}
apply(clarify, simp add:abbrev Graph6 Graph12)
apply(erule conjE)+
apply(erule disjE, erule disjI1, rule disjI2, rule allI, (rule impI)+, case_tac "R=i", rule conjI, erule sym)
 apply(erule Graph4) 
   apply(simp)+
  apply (simp add:BtoW_def)
 apply (simp add:BtoW_def)
apply(rule conjI)
 apply (force simp add:BtoW_def)
apply(erule Graph4)
   apply simp+
--{* 6 subgoals left *}
apply(clarify, simp add:abbrev Graph6 Graph12)
apply(erule conjE)+
apply(rule conjI)
 apply(erule disjE, erule disjI1, rule disjI2, rule allI, (rule impI)+, case_tac "R=i", rule conjI, erule sym)
  apply(erule Graph4) 
    apply(simp)+
   apply (simp add:BtoW_def)
  apply (simp add:BtoW_def)
 apply(rule conjI)
  apply (force simp add:BtoW_def)
 apply(erule Graph4)
    apply simp+
apply(simp add:BtoW_def nth_list_update) 
apply force
--{* 5 subgoals left *}
apply(clarify, simp add:abbrev Graph6 Graph12)
--{* 4 subgoals left *}
apply(clarify, simp add:abbrev Graph6 Graph12)
apply(rule conjI)
 apply(erule disjE, erule disjI1, rule disjI2, rule allI, (rule impI)+, case_tac "R=i", rule conjI, erule sym)
  apply(erule Graph4) 
    apply(simp)+
   apply (simp add:BtoW_def)
  apply (simp add:BtoW_def)
 apply(rule conjI)
  apply (force simp add:BtoW_def)
 apply(erule Graph4)
    apply simp+
apply(rule conjI)
 apply(simp add:nth_list_update)
 apply force
apply(rule impI, rule impI, erule disjE, erule disjI1, case_tac "R = (ind x)" ,case_tac "M x ! T = Black")
  apply(force simp add:BtoW_def)
 apply(case_tac "M x !snd (E x ! ind x)=Black")
  apply(rule disjI2)
  apply simp
  apply (erule Graph5)
  apply simp+
 apply(force simp add:BtoW_def)
apply(force simp add:BtoW_def)
--{* 3 subgoals left *}
apply(clarify, simp add:abbrev Graph6 Graph12)
--{* 2 subgoals left *}
apply(clarify, simp add:abbrev Graph6 Graph12)
apply(erule disjE, erule disjI1, rule disjI2, rule allI, (rule impI)+, case_tac "R=i", rule conjI, erule sym)
 apply clarify
 apply(erule Graph4) 
   apply(simp)+
  apply (simp add:BtoW_def)
 apply (simp add:BtoW_def)
apply(rule conjI)
 apply (force simp add:BtoW_def)
apply(erule Graph4)
   apply simp+
done

lemma interfree_Redirect_Edge_Propagate_Black: 
  "interfree_aux (Some Redirect_Edge, {}, Some Propagate_Black)"
apply (unfold modules )
apply interfree_aux
apply(clarify, simp add:abbrev)+
done

lemma interfree_Propagate_Black_Color_Target: 
  "interfree_aux (Some Propagate_Black, {}, Some Color_Target)"
apply (unfold modules )
apply interfree_aux
--{* 11 subgoals left *}
apply(clarify, simp add:abbrev Graph7 Graph8 Graph12)+
apply(erule conjE)+
apply(erule disjE,rule disjI1,erule psubset_subset_trans,erule Graph9, 
      case_tac "M x!T=Black", rule disjI2,rotate_tac -1, simp add: Graph10, clarify,
      erule allE, erule impE, assumption, erule impE, assumption, 
      simp add:BtoW_def, rule disjI1, erule subset_psubset_trans, erule Graph11, force) 
--{* 7 subgoals left *}
apply(clarify, simp add:abbrev Graph7 Graph8 Graph12)
apply(erule conjE)+
apply(erule disjE,rule disjI1,erule psubset_subset_trans,erule Graph9, 
      case_tac "M x!T=Black", rule disjI2,rotate_tac -1, simp add: Graph10, clarify,
      erule allE, erule impE, assumption, erule impE, assumption, 
      simp add:BtoW_def, rule disjI1, erule subset_psubset_trans, erule Graph11, force) 
--{* 6 subgoals left *}
apply(clarify, simp add:abbrev Graph7 Graph8 Graph12)
apply clarify
apply (rule conjI)
 apply(erule disjE,rule disjI1,erule psubset_subset_trans,erule Graph9, 
      case_tac "M x!T=Black", rule disjI2,rotate_tac -1, simp add: Graph10, clarify,
      erule allE, erule impE, assumption, erule impE, assumption, 
      simp add:BtoW_def, rule disjI1, erule subset_psubset_trans, erule Graph11, force) 
apply(simp add:nth_list_update)
--{* 5 subgoals left *}
apply(clarify, simp add:abbrev Graph7 Graph8 Graph12)
--{* 4 subgoals left *}
apply(clarify, simp add:abbrev Graph7 Graph8 Graph12)
apply (rule conjI)
 apply(erule disjE,rule disjI1,erule psubset_subset_trans,erule Graph9, 
      case_tac "M x!T=Black", rule disjI2,rotate_tac -1, simp add: Graph10, clarify,
      erule allE, erule impE, assumption, erule impE, assumption, 
      simp add:BtoW_def, rule disjI1, erule subset_psubset_trans, erule Graph11, force) 
apply(rule conjI)
apply(simp add:nth_list_update)
apply(rule impI,rule impI, case_tac "M x!T=Black",rotate_tac -1, force simp add: BtoW_def Graph10, 
      erule subset_psubset_trans, erule Graph11, force)
--{* 3 subgoals left *}
apply(clarify, simp add:abbrev Graph7 Graph8 Graph12)
--{* 2 subgoals left *}
apply(clarify, simp add:abbrev Graph7 Graph8 Graph12)
apply(erule disjE,rule disjI1,erule psubset_subset_trans,erule Graph9, 
      case_tac "M x!T=Black", rule disjI2,rotate_tac -1, simp add: Graph10, clarify,
      erule allE, erule impE, assumption, erule impE, assumption, 
      simp add:BtoW_def, rule disjI1, erule subset_psubset_trans, erule Graph11, force) 
--{* 3 subgoals left *}
apply(simp add:abbrev)
done

lemma interfree_Color_Target_Propagate_Black: 
  "interfree_aux (Some Color_Target, {}, Some Propagate_Black)"
apply (unfold modules )
apply interfree_aux
apply(clarify, simp add:abbrev)+
done

lemma interfree_Count_Redirect_Edge: 
  "interfree_aux (Some Count, {}, Some Redirect_Edge)"
apply (unfold modules)
apply interfree_aux
--{* 9 subgoals left *}
apply(simp_all add:abbrev Graph6 Graph12)
--{* 6 subgoals left *}
apply(clarify, simp add:abbrev Graph6 Graph12,
      erule disjE,erule disjI1,rule disjI2,rule subset_trans, erule Graph3,force,force)+
done

lemma interfree_Redirect_Edge_Count: 
  "interfree_aux (Some Redirect_Edge, {}, Some Count)"
apply (unfold modules )
apply interfree_aux
apply(clarify,simp add:abbrev)+
apply(simp add:abbrev)
done

lemma interfree_Count_Color_Target: 
  "interfree_aux (Some Count, {}, Some Color_Target)"
apply (unfold modules )
apply interfree_aux
--{* 9 subgoals left *}
apply(simp_all add:abbrev Graph7 Graph8 Graph12)
--{* 6 subgoals left *}
apply(clarify,simp add:abbrev Graph7 Graph8 Graph12,
      erule disjE, erule disjI1, rule disjI2,erule subset_trans, erule Graph9)+
--{* 2 subgoals left *}
apply(clarify, simp add:abbrev Graph7 Graph8 Graph12)
apply(rule conjI)
 apply(erule disjE, erule disjI1, rule disjI2,erule subset_trans, erule Graph9) 
apply(simp add:nth_list_update)
--{* 1 subgoal left *}
apply(clarify, simp add:abbrev Graph7 Graph8 Graph12,
      erule disjE, erule disjI1, rule disjI2,erule subset_trans, erule Graph9)
done

lemma interfree_Color_Target_Count: 
  "interfree_aux (Some Color_Target, {}, Some Count)"
apply (unfold modules )
apply interfree_aux
apply(clarify, simp add:abbrev)+
apply(simp add:abbrev)
done

lemma interfree_Append_Redirect_Edge: 
  "interfree_aux (Some Append, {}, Some Redirect_Edge)"
apply (unfold modules )
apply interfree_aux
apply( simp_all add:abbrev Graph6 Append_to_free0 Append_to_free1 Graph12)
apply(clarify, simp add:abbrev Graph6 Append_to_free0 Append_to_free1 Graph12, force dest:Graph3)+
done

lemma interfree_Redirect_Edge_Append: 
  "interfree_aux (Some Redirect_Edge, {}, Some Append)"
apply (unfold modules )
apply interfree_aux
apply(clarify, simp add:abbrev Append_to_free0)+
apply (force simp add: Append_to_free2)
apply(clarify, simp add:abbrev Append_to_free0)+
done

lemma interfree_Append_Color_Target: 
  "interfree_aux (Some Append, {}, Some Color_Target)"
apply (unfold modules )
apply interfree_aux
apply(clarify, simp add:abbrev Graph7 Graph8 Append_to_free0 Append_to_free1 Graph12 nth_list_update)+
apply(simp add:abbrev Graph7 Graph8 Append_to_free0 Append_to_free1 Graph12 nth_list_update)
done

lemma interfree_Color_Target_Append: 
  "interfree_aux (Some Color_Target, {}, Some Append)"
apply (unfold modules )
apply interfree_aux
apply(clarify, simp add:abbrev Append_to_free0)+
apply (force simp add: Append_to_free2)
apply(clarify,simp add:abbrev Append_to_free0)+
done

lemmas collector_mutator_interfree = 
 interfree_Blacken_Roots_Redirect_Edge interfree_Blacken_Roots_Color_Target 
 interfree_Propagate_Black_Redirect_Edge interfree_Propagate_Black_Color_Target  
 interfree_Count_Redirect_Edge interfree_Count_Color_Target 
 interfree_Append_Redirect_Edge interfree_Append_Color_Target 
 interfree_Redirect_Edge_Blacken_Roots interfree_Color_Target_Blacken_Roots 
 interfree_Redirect_Edge_Propagate_Black interfree_Color_Target_Propagate_Black  
 interfree_Redirect_Edge_Count interfree_Color_Target_Count 
 interfree_Redirect_Edge_Append interfree_Color_Target_Append

subsubsection {* Interference freedom Collector-Mutator *}

lemma interfree_Collector_Mutator:
 "interfree_aux (Some Collector, {}, Some Mutator)"
apply(unfold Collector_def Mutator_def)
apply interfree_aux
apply(simp_all add:collector_mutator_interfree)
apply(unfold modules collector_defs mutator_defs)
apply(tactic  {* TRYALL (interfree_aux_tac) *})
--{* 32 subgoals left *}
apply(simp_all add:Graph6 Graph7 Graph8 Append_to_free0 Append_to_free1 Graph12)
--{* 20 subgoals left *}
apply(tactic{* TRYALL (clarify_tac @{context}) *})
apply(simp_all add:Graph6 Graph7 Graph8 Append_to_free0 Append_to_free1 Graph12)
apply(tactic {* TRYALL (etac disjE) *})
apply simp_all
apply(tactic {* TRYALL(EVERY'[rtac disjI2,rtac subset_trans,etac @{thm Graph3},force_tac @{context}, assume_tac]) *})
apply(tactic {* TRYALL(EVERY'[rtac disjI2,etac subset_trans,rtac @{thm Graph9},force_tac @{context}]) *})
apply(tactic {* TRYALL(EVERY'[rtac disjI1,etac @{thm psubset_subset_trans},rtac @{thm Graph9},force_tac @{context}]) *})
done

subsubsection {* Interference freedom Mutator-Collector *}

lemma interfree_Mutator_Collector:
 "interfree_aux (Some Mutator, {}, Some Collector)"
apply(unfold Collector_def Mutator_def)
apply interfree_aux
apply(simp_all add:collector_mutator_interfree)
apply(unfold modules collector_defs mutator_defs)
apply(tactic  {* TRYALL (interfree_aux_tac) *})
--{* 64 subgoals left *}
apply(simp_all add:nth_list_update Invariants Append_to_free0)+
apply(tactic{* TRYALL (clarify_tac @{context}) *})
--{* 4 subgoals left *}
apply force
apply(simp add:Append_to_free2)
apply force
apply(simp add:Append_to_free2)
done

subsubsection {* The Garbage Collection algorithm *}

text {* In total there are 289 verification conditions.  *}

lemma Gar_Coll: 
  "\<parallel>- .{\<acute>Proper \<and> \<acute>Mut_init \<and> \<acute>z}.  
  COBEGIN  
   Collector
  .{False}.
 \<parallel>  
   Mutator
  .{False}. 
 COEND 
  .{False}."
apply oghoare
apply(force simp add: Mutator_def Collector_def modules)
apply(rule Collector)
apply(rule Mutator)
apply(simp add:interfree_Collector_Mutator)
apply(simp add:interfree_Mutator_Collector)
apply force
done

end
