(*  Title:      isabelle/Bali/TypeRel.thy
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   1997 Technische Universitaet Muenchen
*)
header {* The relations between Java types *}

theory TypeRel = Decl:

text {*
simplifications:
\begin{itemize}
\item subinterface, subclass and widening relation includes identity
\end{itemize}
improvements over Java Specification 1.0:
\begin{itemize}
\item narrowing reference conversion also in cases where the return types of a 
      pair of methods common to both types are in widening (rather identity) 
      relation
\item one could add similar constraints also for other cases
\end{itemize}
design issues:
\begin{itemize}
\item the type relations do not require @{text is_type} for their arguments
\item the subint1 and subcls1 relations imply @{text is_iface}/@{text is_class}
      for their first arguments, which is required for their finiteness
\end{itemize}
*}

consts

(*subint1, in Decl.thy*)                     (* direct subinterface       *)
(*subint , by translation*)                  (* subinterface (+ identity) *)
(*subcls1, in Decl.thy*)                     (* direct subclass           *)
(*subcls , by translation*)                  (*        subclass           *)
(*subclseq, by translation*)                 (* subclass + identity       *)
  implmt1   :: "prog \<Rightarrow> (qtname \<times> qtname) set" (* direct implementation *)
  implmt    :: "prog \<Rightarrow> (qtname \<times> qtname) set" (*        implementation *)
  widen     :: "prog \<Rightarrow> (ty    \<times> ty   ) set" (*        widening       *)
  narrow    :: "prog \<Rightarrow> (ty    \<times> ty   ) set" (*        narrowing      *)
  cast     :: "prog \<Rightarrow> (ty    \<times> ty   ) set"  (*        casting        *)

syntax

 "@subint1" :: "prog => [qtname, qtname] => bool" ("_|-_<:I1_" [71,71,71] 70)
 "@subint"  :: "prog => [qtname, qtname] => bool" ("_|-_<=:I _"[71,71,71] 70)
 (* Defined in Decl.thy:
 "@subcls1" :: "prog => [qtname, qtname] => bool" ("_|-_<:C1_" [71,71,71] 70)
 "@subclseq":: "prog => [qtname, qtname] => bool" ("_|-_<=:C _"[71,71,71] 70)
 "@subcls"  :: "prog => [qtname, qtname] => bool" ("_|-_<:C _"[71,71,71] 70)
 *)
 "@implmt1" :: "prog => [qtname, qtname] => bool" ("_|-_~>1_"  [71,71,71] 70)
 "@implmt"  :: "prog => [qtname, qtname] => bool" ("_|-_~>_"   [71,71,71] 70)
 "@widen"   :: "prog => [ty   , ty   ] => bool" ("_|-_<=:_"  [71,71,71] 70)
 "@narrow"  :: "prog => [ty   , ty   ] => bool" ("_|-_:>_"   [71,71,71] 70)
 "@cast"    :: "prog => [ty   , ty   ] => bool" ("_|-_<=:? _"[71,71,71] 70)

syntax (symbols)

  "@subint1" :: "prog \<Rightarrow> [qtname, qtname] \<Rightarrow> bool" ("_\<turnstile>_\<prec>I1_"  [71,71,71] 70)
  "@subint"  :: "prog \<Rightarrow> [qtname, qtname] \<Rightarrow> bool" ("_\<turnstile>_\<preceq>I _"  [71,71,71] 70)
  (* Defined in Decl.thy:
\  "@subcls1" :: "prog \<Rightarrow> [qtname, qtname] \<Rightarrow> bool" ("_\<turnstile>_\<prec>\<^sub>C\<^sub>1_"  [71,71,71] 70)
  "@subclseq":: "prog \<Rightarrow> [qtname, qtname] \<Rightarrow> bool" ("_\<turnstile>_\<preceq>\<^sub>C _"  [71,71,71] 70)
  "@subcls"  :: "prog \<Rightarrow> [qtname, qtname] \<Rightarrow> bool" ("_\<turnstile>_\<prec>\<^sub>C _"  [71,71,71] 70)
  *)
  "@implmt1" :: "prog \<Rightarrow> [qtname, qtname] \<Rightarrow> bool" ("_\<turnstile>_\<leadsto>1_"  [71,71,71] 70)
  "@implmt"  :: "prog \<Rightarrow> [qtname, qtname] \<Rightarrow> bool" ("_\<turnstile>_\<leadsto>_"   [71,71,71] 70)
  "@widen"   :: "prog \<Rightarrow> [ty   , ty   ] \<Rightarrow> bool" ("_\<turnstile>_\<preceq>_"    [71,71,71] 70)
  "@narrow"  :: "prog \<Rightarrow> [ty   , ty   ] \<Rightarrow> bool" ("_\<turnstile>_\<succ>_"    [71,71,71] 70)
  "@cast"    :: "prog \<Rightarrow> [ty   , ty   ] \<Rightarrow> bool" ("_\<turnstile>_\<preceq>? _"  [71,71,71] 70)

translations

	"G\<turnstile>I \<prec>I1 J" == "(I,J) \<in> subint1 G"
	"G\<turnstile>I \<preceq>I  J" == "(I,J) \<in>(subint1 G)^*" (* cf. 9.1.3 *)
  	(* Defined in Decl.thy:
        "G\<turnstile>C \<prec>\<^sub>C\<^sub>1 D" == "(C,D) \<in> subcls1 G"
	"G\<turnstile>C \<preceq>\<^sub>C  D" == "(C,D) \<in>(subcls1 G)^*" 
	*)
        "G\<turnstile>C \<leadsto>1 I" == "(C,I) \<in> implmt1 G"
	"G\<turnstile>C \<leadsto>  I" == "(C,I) \<in> implmt  G"
	"G\<turnstile>S \<preceq>   T" == "(S,T) \<in> widen   G"
	"G\<turnstile>S \<succ>   T" == "(S,T) \<in> narrow  G"
	"G\<turnstile>S \<preceq>?  T" == "(S,T) \<in> cast    G"


section "subclass and subinterface relations"

  (* direct subinterface in Decl.thy, cf. 9.1.3 *)
  (* direct subclass     in Decl.thy, cf. 8.1.3 *)

lemmas subcls_direct = subcls1I [THEN r_into_rtrancl, standard]

lemma subcls_direct1:
 "\<lbrakk>class G C = Some c; C \<noteq> Object;D=super c\<rbrakk> \<Longrightarrow> G\<turnstile>C\<preceq>\<^sub>C D"
apply (auto dest: subcls_direct)
done

lemma subcls1I1:
 "\<lbrakk>class G C = Some c; C \<noteq> Object;D=super c\<rbrakk> \<Longrightarrow> G\<turnstile>C\<prec>\<^sub>C\<^sub>1 D"
apply (auto dest: subcls1I)
done

lemma subcls_direct2:
 "\<lbrakk>class G C = Some c; C \<noteq> Object;D=super c\<rbrakk> \<Longrightarrow> G\<turnstile>C\<prec>\<^sub>C D"
apply (auto dest: subcls1I1)
done

lemma subclseq_trans: "\<lbrakk>G\<turnstile>A \<preceq>\<^sub>C B; G\<turnstile>B \<preceq>\<^sub>C C\<rbrakk> \<Longrightarrow> G\<turnstile>A \<preceq>\<^sub>C C"
by (blast intro: rtrancl_trans)

lemma subcls_trans: "\<lbrakk>G\<turnstile>A \<prec>\<^sub>C B; G\<turnstile>B \<prec>\<^sub>C C\<rbrakk> \<Longrightarrow> G\<turnstile>A \<prec>\<^sub>C C"
by (blast intro: trancl_trans)

lemma SXcpt_subcls_Throwable_lemma: 
"\<lbrakk>class G (SXcpt xn) = Some xc;
  super xc = (if xn = Throwable then Object else  SXcpt Throwable)\<rbrakk> 
\<Longrightarrow> G\<turnstile>SXcpt xn\<preceq>\<^sub>C SXcpt Throwable"
apply (case_tac "xn = Throwable")
apply  simp_all
apply (drule subcls_direct)
apply (auto dest: sym)
done

lemma subcls_ObjectI: "\<lbrakk>is_class G C; ws_prog G\<rbrakk> \<Longrightarrow> G\<turnstile>C\<preceq>\<^sub>C Object"
apply (erule ws_subcls1_induct)
apply clarsimp
apply (case_tac "C = Object")
apply  (fast intro: r_into_rtrancl [THEN rtrancl_trans])+
done

lemma subclseq_ObjectD [dest!]: "G\<turnstile>Object\<preceq>\<^sub>C C \<Longrightarrow> C = Object"
apply (erule rtrancl_induct)
apply  (auto dest: subcls1D)
done

lemma subcls_ObjectD [dest!]: "G\<turnstile>Object\<prec>\<^sub>C C \<Longrightarrow> False"
apply (erule trancl_induct)
apply  (auto dest: subcls1D)
done

lemma subcls_ObjectI1 [intro!]: 
 "\<lbrakk>C \<noteq> Object;is_class G C;ws_prog G\<rbrakk> \<Longrightarrow> G\<turnstile>C \<prec>\<^sub>C Object" 
apply (drule (1) subcls_ObjectI)
apply (auto intro: rtrancl_into_trancl3)
done

lemma subcls_is_class: "(C,D) \<in> (subcls1 G)^+ \<Longrightarrow> is_class G C"
apply (erule trancl_trans_induct)
apply (auto dest!: subcls1D)
done

lemma subcls_is_class2 [rule_format (no_asm)]: 
 "G\<turnstile>C\<preceq>\<^sub>C D \<Longrightarrow> is_class G D \<longrightarrow> is_class G C"
apply (erule rtrancl_induct)
apply (drule_tac [2] subcls1D)
apply  auto
done

lemma single_inheritance: 
"\<lbrakk>G\<turnstile>A \<prec>\<^sub>C\<^sub>1 B; G\<turnstile>A \<prec>\<^sub>C\<^sub>1 C\<rbrakk> \<Longrightarrow> B = C"
by (auto simp add: subcls1_def)
  
lemma subcls_compareable:
"\<lbrakk>G\<turnstile>A \<preceq>\<^sub>C X; G\<turnstile>A \<preceq>\<^sub>C Y 
 \<rbrakk> \<Longrightarrow> G\<turnstile>X \<preceq>\<^sub>C Y \<or> G\<turnstile>Y \<preceq>\<^sub>C X"
by (rule triangle_lemma)  (auto intro: single_inheritance) 

lemma subcls1_irrefl: "\<lbrakk>G\<turnstile>C \<prec>\<^sub>C\<^sub>1 D; ws_prog G \<rbrakk>
 \<Longrightarrow> C \<noteq> D"
proof 
  assume ws: "ws_prog G" and
    subcls1: "G\<turnstile>C \<prec>\<^sub>C\<^sub>1 D" and
     eq_C_D: "C=D"
  from subcls1 obtain c 
    where
      neq_C_Object: "C\<noteq>Object" and
              clsC: "class G C = Some c" and
           super_c: "super c = D"
    by (auto simp add: subcls1_def)
  with super_c subcls1 eq_C_D 
  have subcls_super_c_C: "G\<turnstile>super c \<prec>\<^sub>C C"
    by auto
  from ws clsC neq_C_Object 
  have "\<not> G\<turnstile>super c \<prec>\<^sub>C C"
    by (auto dest: ws_prog_cdeclD)
  from this subcls_super_c_C 
  show "False"
    by (rule notE)
qed

lemma no_subcls_Object: "G\<turnstile>C \<prec>\<^sub>C D \<Longrightarrow> C \<noteq> Object"
by (erule converse_trancl_induct) (auto dest: subcls1D)

lemma subcls_acyclic: "\<lbrakk>G\<turnstile>C \<prec>\<^sub>C D; ws_prog G\<rbrakk> \<Longrightarrow> \<not> G\<turnstile>D \<prec>\<^sub>C C"
proof -
  assume         ws: "ws_prog G"
  assume subcls_C_D: "G\<turnstile>C \<prec>\<^sub>C D"
  then show ?thesis
  proof (induct rule: converse_trancl_induct)
    fix C
    assume subcls1_C_D: "G\<turnstile>C \<prec>\<^sub>C\<^sub>1 D"
    then obtain c  where
        "C\<noteq>Object" and
        "class G C = Some c" and
        "super c = D"
      by (auto simp add: subcls1_def)
    with ws 
    show "\<not> G\<turnstile>D \<prec>\<^sub>C C"
      by (auto dest: ws_prog_cdeclD)
  next
    fix C Z
    assume subcls1_C_Z: "G\<turnstile>C \<prec>\<^sub>C\<^sub>1 Z" and
            subcls_Z_D: "G\<turnstile>Z \<prec>\<^sub>C D" and
           nsubcls_D_Z: "\<not> G\<turnstile>D \<prec>\<^sub>C Z"
    show "\<not> G\<turnstile>D \<prec>\<^sub>C C"
    proof
      assume subcls_D_C: "G\<turnstile>D \<prec>\<^sub>C C"
      show "False"
      proof -
	from subcls_D_C subcls1_C_Z
	have "G\<turnstile>D \<prec>\<^sub>C Z"
	  by (auto dest: r_into_trancl trancl_trans)
	with nsubcls_D_Z
	show ?thesis
	  by (rule notE)
      qed
    qed
  qed  
qed

lemma subclseq_cases [consumes 1, case_names Eq Subcls]:
 "\<lbrakk>G\<turnstile>C \<preceq>\<^sub>C D; C = D \<Longrightarrow> P; G\<turnstile>C \<prec>\<^sub>C D \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
by (blast intro: rtrancl_cases)

lemma subclseq_acyclic: 
 "\<lbrakk>G\<turnstile>C \<preceq>\<^sub>C D; G\<turnstile>D \<preceq>\<^sub>C C; ws_prog G\<rbrakk> \<Longrightarrow> C=D"
by (auto elim: subclseq_cases dest: subcls_acyclic)

lemma subcls_irrefl: "\<lbrakk>G\<turnstile>C \<prec>\<^sub>C D; ws_prog G\<rbrakk>
 \<Longrightarrow> C \<noteq> D"
proof -
  assume     ws: "ws_prog G"
  assume subcls: "G\<turnstile>C \<prec>\<^sub>C D"
  then show ?thesis
  proof (induct rule: converse_trancl_induct)
    fix C
    assume "G\<turnstile>C \<prec>\<^sub>C\<^sub>1 D"
    with ws 
    show "C\<noteq>D" 
      by (blast dest: subcls1_irrefl)
  next
    fix C Z
    assume subcls1_C_Z: "G\<turnstile>C \<prec>\<^sub>C\<^sub>1 Z" and
            subcls_Z_D: "G\<turnstile>Z \<prec>\<^sub>C D" and
               neq_Z_D: "Z \<noteq> D"
    show "C\<noteq>D"
    proof
      assume eq_C_D: "C=D"
      show "False"
      proof -
	from subcls1_C_Z eq_C_D 
	have "G\<turnstile>D \<prec>\<^sub>C Z"
	  by (auto)
	also
	from subcls_Z_D ws   
	have "\<not> G\<turnstile>D \<prec>\<^sub>C Z"
	  by (rule subcls_acyclic)
	ultimately 
	show ?thesis 
	  by - (rule notE)
      qed
    qed
  qed
qed

lemma invert_subclseq:
"\<lbrakk>G\<turnstile>C \<preceq>\<^sub>C D; ws_prog G\<rbrakk>
 \<Longrightarrow> \<not> G\<turnstile>D \<prec>\<^sub>C C"
proof -
  assume       ws: "ws_prog G" and
     subclseq_C_D: "G\<turnstile>C \<preceq>\<^sub>C D"
  show ?thesis
  proof (cases "D=C")
    case True
    with ws 
    show ?thesis 
      by (auto dest: subcls_irrefl)
  next
    case False
    with subclseq_C_D 
    have "G\<turnstile>C \<prec>\<^sub>C D"
      by (blast intro: rtrancl_into_trancl3) 
    with ws 
    show ?thesis 
      by (blast dest: subcls_acyclic)
  qed
qed

lemma invert_subcls:
"\<lbrakk>G\<turnstile>C \<prec>\<^sub>C D; ws_prog G\<rbrakk>
 \<Longrightarrow> \<not> G\<turnstile>D \<preceq>\<^sub>C C"
proof -
  assume        ws: "ws_prog G" and
        subcls_C_D: "G\<turnstile>C \<prec>\<^sub>C D"
  then 
  have nsubcls_D_C: "\<not> G\<turnstile>D \<prec>\<^sub>C C"
    by (blast dest: subcls_acyclic)
  show ?thesis
  proof
    assume "G\<turnstile>D \<preceq>\<^sub>C C"
    then show "False"
    proof (cases rule: subclseq_cases)
      case Eq
      with ws subcls_C_D
      show ?thesis 
	by (auto dest: subcls_irrefl)
    next
      case Subcls
      with nsubcls_D_C
      show ?thesis
	by blast
    qed
  qed
qed

lemma subcls_superD:
 "\<lbrakk>G\<turnstile>C \<prec>\<^sub>C D; class G C = Some c\<rbrakk> \<Longrightarrow> G\<turnstile>(super c) \<preceq>\<^sub>C D"
proof -
  assume       clsC: "class G C = Some c"
  assume subcls_C_C: "G\<turnstile>C \<prec>\<^sub>C D"
  then obtain S where 
                  "G\<turnstile>C \<prec>\<^sub>C\<^sub>1 S" and
    subclseq_S_D: "G\<turnstile>S \<preceq>\<^sub>C D"
    by (blast dest: tranclD)
  with clsC 
  have "S=super c" 
    by (auto dest: subcls1D)
  with subclseq_S_D show ?thesis by simp
qed
 

lemma subclseq_superD:
 "\<lbrakk>G\<turnstile>C \<preceq>\<^sub>C D; C\<noteq>D;class G C = Some c\<rbrakk> \<Longrightarrow> G\<turnstile>(super c) \<preceq>\<^sub>C D"
proof -
  assume neq_C_D: "C\<noteq>D"
  assume    clsC: "class G C = Some c"
  assume subclseq_C_D: "G\<turnstile>C \<preceq>\<^sub>C D" 
  then show ?thesis
  proof (cases rule: subclseq_cases)
    case Eq with neq_C_D show ?thesis by contradiction
  next
    case Subcls
    with clsC show ?thesis by (blast dest: subcls_superD)
  qed
qed

section "implementation relation"

defs
  (* direct implementation, cf. 8.1.3 *)
implmt1_def:"implmt1 G\<equiv>{(C,I). C\<noteq>Object \<and> (\<exists>c\<in>class G C: I\<in>set (superIfs c))}"

lemma implmt1D: "G\<turnstile>C\<leadsto>1I \<Longrightarrow> C\<noteq>Object \<and> (\<exists>c\<in>class G C: I\<in>set (superIfs c))"
apply (unfold implmt1_def)
apply auto
done


inductive "implmt G" intros                    (* cf. 8.1.4 *)

  direct:         "G\<turnstile>C\<leadsto>1J     \<spacespace>\<spacespace>     \<Longrightarrow> G\<turnstile>C\<leadsto>J"
  subint:        "\<lbrakk>G\<turnstile>C\<leadsto>1I; G\<turnstile>I\<preceq>I J\<rbrakk>  \<Longrightarrow> G\<turnstile>C\<leadsto>J"
  subcls1:       "\<lbrakk>G\<turnstile>C\<prec>\<^sub>C\<^sub>1D; G\<turnstile>D\<leadsto>J \<rbrakk>  \<Longrightarrow> G\<turnstile>C\<leadsto>J"

lemma implmtD: "G\<turnstile>C\<leadsto>J \<Longrightarrow> (\<exists>I. G\<turnstile>C\<leadsto>1I \<and> G\<turnstile>I\<preceq>I J) \<or> (\<exists>D. G\<turnstile>C\<prec>\<^sub>C\<^sub>1D \<and> G\<turnstile>D\<leadsto>J)" 
apply (erule implmt.induct)
apply fast+
done

lemma implmt_ObjectE [elim!]: "G\<turnstile>Object\<leadsto>I \<Longrightarrow> R"
by (auto dest!: implmtD implmt1D subcls1D)

lemma subcls_implmt [rule_format (no_asm)]: "G\<turnstile>A\<preceq>\<^sub>C B \<Longrightarrow> G\<turnstile>B\<leadsto>K \<longrightarrow> G\<turnstile>A\<leadsto>K"
apply (erule rtrancl_induct)
apply  (auto intro: implmt.subcls1)
done

lemma implmt_subint2: "\<lbrakk> G\<turnstile>A\<leadsto>J; G\<turnstile>J\<preceq>I K\<rbrakk> \<Longrightarrow> G\<turnstile>A\<leadsto>K"
apply (erule make_imp, erule implmt.induct)
apply (auto dest: implmt.subint rtrancl_trans implmt.subcls1)
done

lemma implmt_is_class: "G\<turnstile>C\<leadsto>I \<Longrightarrow> is_class G C"
apply (erule implmt.induct)
apply (blast dest: implmt1D subcls1D)+
done


section "widening relation"

inductive "widen G" intros(*widening, viz. method invocation conversion, cf. 5.3
			    i.e. kind of syntactic subtyping *)
  refl:    "G\<turnstile>T\<preceq>T"(*identity conversion, cf. 5.1.1 *)
  subint:  "G\<turnstile>I\<preceq>I J  \<Longrightarrow> G\<turnstile>Iface I\<preceq> Iface J"(*wid.ref.conv.,cf. 5.1.4 *)
  int_obj: "G\<turnstile>Iface I\<preceq> Class Object"
  subcls:  "G\<turnstile>C\<preceq>\<^sub>C D  \<Longrightarrow> G\<turnstile>Class C\<preceq> Class D"
  implmt:  "G\<turnstile>C\<leadsto>I   \<Longrightarrow> G\<turnstile>Class C\<preceq> Iface I"
  null:    "G\<turnstile>NT\<preceq> RefT R"
  arr_obj: "G\<turnstile>T.[]\<preceq> Class Object"
  array:   "G\<turnstile>RefT S\<preceq>RefT T \<Longrightarrow> G\<turnstile>RefT S.[]\<preceq> RefT T.[]"

declare widen.refl [intro!]
declare widen.intros [simp]

(* too strong in general:
lemma widen_PrimT: "G\<turnstile>PrimT x\<preceq>T \<Longrightarrow> T = PrimT x"
*)
lemma widen_PrimT: "G\<turnstile>PrimT x\<preceq>T \<Longrightarrow> (\<exists>y. T = PrimT y)"
apply (ind_cases "G\<turnstile>S\<preceq>T")
by auto

(* too strong in general:
lemma widen_PrimT2: "G\<turnstile>S\<preceq>PrimT x \<Longrightarrow> S = PrimT x"
*)
lemma widen_PrimT2: "G\<turnstile>S\<preceq>PrimT x \<Longrightarrow> \<exists>y. S = PrimT y"
apply (ind_cases "G\<turnstile>S\<preceq>T")
by auto

lemma widen_RefT: "G\<turnstile>RefT R\<preceq>T \<Longrightarrow> \<exists>t. T=RefT t"
apply (ind_cases "G\<turnstile>S\<preceq>T")
by auto

lemma widen_RefT2: "G\<turnstile>S\<preceq>RefT R \<Longrightarrow> \<exists>t. S=RefT t"
apply (ind_cases "G\<turnstile>S\<preceq>T")
by auto

lemma widen_Iface: "G\<turnstile>Iface I\<preceq>T \<Longrightarrow> T=Class Object \<or> (\<exists>J. T=Iface J)"
apply (ind_cases "G\<turnstile>S\<preceq>T")
by auto

lemma widen_Iface2: "G\<turnstile>S\<preceq> Iface J \<Longrightarrow> S = NT \<or> (\<exists>I. S = Iface I) \<or> (\<exists>D. S = Class D)"
apply (ind_cases "G\<turnstile>S\<preceq>T")
by auto

lemma widen_Iface_Iface: "G\<turnstile>Iface I\<preceq> Iface J \<Longrightarrow> G\<turnstile>I\<preceq>I J"
apply (ind_cases "G\<turnstile>S\<preceq>T")
by auto

lemma widen_Iface_Iface_eq [simp]: "G\<turnstile>Iface I\<preceq> Iface J = G\<turnstile>I\<preceq>I J"
apply (rule iffI)
apply  (erule widen_Iface_Iface)
apply (erule widen.subint)
done

lemma widen_Class: "G\<turnstile>Class C\<preceq>T \<Longrightarrow>  (\<exists>D. T=Class D) \<or> (\<exists>I. T=Iface I)"
apply (ind_cases "G\<turnstile>S\<preceq>T")
by auto

lemma widen_Class2: "G\<turnstile>S\<preceq> Class C \<Longrightarrow> C = Object \<or> S = NT \<or> (\<exists>D. S = Class D)"
apply (ind_cases "G\<turnstile>S\<preceq>T")
by auto

lemma widen_Class_Class: "G\<turnstile>Class C\<preceq> Class cm \<Longrightarrow> G\<turnstile>C\<preceq>\<^sub>C cm"
apply (ind_cases "G\<turnstile>S\<preceq>T")
by auto

lemma widen_Class_Class_eq [simp]: "G\<turnstile>Class C\<preceq> Class cm = G\<turnstile>C\<preceq>\<^sub>C cm"
apply (rule iffI)
apply  (erule widen_Class_Class)
apply (erule widen.subcls)
done

lemma widen_Class_Iface: "G\<turnstile>Class C\<preceq> Iface I \<Longrightarrow> G\<turnstile>C\<leadsto>I"
apply (ind_cases "G\<turnstile>S\<preceq>T")
by auto

lemma widen_Class_Iface_eq [simp]: "G\<turnstile>Class C\<preceq> Iface I = G\<turnstile>C\<leadsto>I"
apply (rule iffI)
apply  (erule widen_Class_Iface)
apply (erule widen.implmt)
done

lemma widen_Array: "G\<turnstile>S.[]\<preceq>T \<Longrightarrow> T=Class Object \<or> (\<exists>T'. T=T'.[] \<and> G\<turnstile>S\<preceq>T')"
apply (ind_cases "G\<turnstile>S\<preceq>T")
by auto

lemma widen_Array2: "G\<turnstile>S\<preceq>T.[] \<Longrightarrow> S = NT \<or> (\<exists>S'. S=S'.[] \<and> G\<turnstile>S'\<preceq>T)"
apply (ind_cases "G\<turnstile>S\<preceq>T")
by auto


lemma widen_ArrayPrimT: "G\<turnstile>PrimT t.[]\<preceq>T \<Longrightarrow> T=Class Object \<or> T=PrimT t.[]"
apply (ind_cases "G\<turnstile>S\<preceq>T")
by auto

lemma widen_ArrayRefT: 
  "G\<turnstile>RefT t.[]\<preceq>T \<Longrightarrow> T=Class Object \<or> (\<exists>s. T=RefT s.[] \<and> G\<turnstile>RefT t\<preceq>RefT s)"
apply (ind_cases "G\<turnstile>S\<preceq>T")
by auto

lemma widen_ArrayRefT_ArrayRefT_eq [simp]: 
  "G\<turnstile>RefT T.[]\<preceq>RefT T'.[] = G\<turnstile>RefT T\<preceq>RefT T'"
apply (rule iffI)
apply (drule widen_ArrayRefT)
apply simp
apply (erule widen.array)
done

lemma widen_Array_Array: "G\<turnstile>T.[]\<preceq>T'.[] \<Longrightarrow> G\<turnstile>T\<preceq>T'"
apply (drule widen_Array)
apply auto
done

lemma widen_Array_Class: "G\<turnstile>S.[] \<preceq> Class C \<Longrightarrow> C=Object"
by (auto dest: widen_Array)

(*
qed_typerel "widen_NT2" "G\<turnstile>S\<preceq>NT \<Longrightarrow> S = NT"
 [prove_widen_lemma "G\<turnstile>S\<preceq>T \<Longrightarrow> T = NT \<longrightarrow> S = NT"]
*)
lemma widen_NT2: "G\<turnstile>S\<preceq>NT \<Longrightarrow> S = NT"
apply (ind_cases "G\<turnstile>S\<preceq>T")
by auto

lemma widen_Object:"\<lbrakk>isrtype G T;ws_prog G\<rbrakk> \<Longrightarrow> G\<turnstile>RefT T \<preceq> Class Object"
apply (case_tac T)
apply (auto)
apply (subgoal_tac "G\<turnstile>pid_field_type\<preceq>\<^sub>C Object")
apply (auto intro: subcls_ObjectI)
done

lemma widen_trans_lemma [rule_format (no_asm)]: 
  "\<lbrakk>G\<turnstile>S\<preceq>U; \<forall>C. is_class G C \<longrightarrow> G\<turnstile>C\<preceq>\<^sub>C Object\<rbrakk> \<Longrightarrow> \<forall>T. G\<turnstile>U\<preceq>T \<longrightarrow> G\<turnstile>S\<preceq>T"
apply (erule widen.induct)
apply        safe
prefer      5 apply (drule widen_RefT) apply clarsimp
apply      (frule_tac [1] widen_Iface)
apply      (frule_tac [2] widen_Class)
apply      (frule_tac [3] widen_Class)
apply      (frule_tac [4] widen_Iface)
apply      (frule_tac [5] widen_Class)
apply      (frule_tac [6] widen_Array)
apply      safe
apply            (rule widen.int_obj)
prefer          6 apply (drule implmt_is_class) apply simp
apply (tactic "ALLGOALS (etac thin_rl)")
prefer         6 apply simp
apply          (rule_tac [9] widen.arr_obj)
apply         (rotate_tac [9] -1)
apply         (frule_tac [9] widen_RefT)
apply         (auto elim!: rtrancl_trans subcls_implmt implmt_subint2)
done

lemma ws_widen_trans: "\<lbrakk>G\<turnstile>S\<preceq>U; G\<turnstile>U\<preceq>T; ws_prog G\<rbrakk> \<Longrightarrow> G\<turnstile>S\<preceq>T"
by (auto intro: widen_trans_lemma subcls_ObjectI)

lemma widen_antisym_lemma [rule_format (no_asm)]: "\<lbrakk>G\<turnstile>S\<preceq>T;  
 \<forall>I J. G\<turnstile>I\<preceq>I J \<and> G\<turnstile>J\<preceq>I I \<longrightarrow> I = J;  
 \<forall>C D. G\<turnstile>C\<preceq>\<^sub>C D \<and> G\<turnstile>D\<preceq>\<^sub>C C \<longrightarrow> C = D;  
 \<forall>I  . G\<turnstile>Object\<leadsto>I        \<longrightarrow> False\<rbrakk> \<Longrightarrow> G\<turnstile>T\<preceq>S \<longrightarrow> S = T"
apply (erule widen.induct)
apply (auto dest: widen_Iface widen_NT2 widen_Class)
done

lemmas subint_antisym = 
       subint1_acyclic [THEN acyclic_impl_antisym_rtrancl, standard]
lemmas subcls_antisym = 
       subcls1_acyclic [THEN acyclic_impl_antisym_rtrancl, standard]

lemma widen_antisym: "\<lbrakk>G\<turnstile>S\<preceq>T; G\<turnstile>T\<preceq>S; ws_prog G\<rbrakk> \<Longrightarrow> S=T"
by (fast elim: widen_antisym_lemma subint_antisym [THEN antisymD] 
                                   subcls_antisym [THEN antisymD])

lemma widen_ObjectD [dest!]: "G\<turnstile>Class Object\<preceq>T \<Longrightarrow> T=Class Object"
apply (frule widen_Class)
apply (fast dest: widen_Class_Class widen_Class_Iface)
done

constdefs
  widens :: "prog \<Rightarrow> [ty list, ty list] \<Rightarrow> bool" ("_\<turnstile>_[\<preceq>]_" [71,71,71] 70)
 "G\<turnstile>Ts[\<preceq>]Ts' \<equiv> list_all2 (\<lambda>T T'. G\<turnstile>T\<preceq>T') Ts Ts'"

lemma widens_Nil [simp]: "G\<turnstile>[][\<preceq>][]"
apply (unfold widens_def)
apply auto
done

lemma widens_Cons [simp]: "G\<turnstile>(S#Ss)[\<preceq>](T#Ts) = (G\<turnstile>S\<preceq>T \<and> G\<turnstile>Ss[\<preceq>]Ts)"
apply (unfold widens_def)
apply auto
done


section "narrowing relation"

(* all properties of narrowing and casting conversions we actually need *)
(* these can easily be proven from the definitions below *)
(*
rules
  cast_RefT2   "G\<turnstile>S\<preceq>? RefT R   \<Longrightarrow> \<exists>t. S=RefT t" 
  cast_PrimT2  "G\<turnstile>S\<preceq>? PrimT pt \<Longrightarrow> \<exists>t. S=PrimT t \<and> G\<turnstile>PrimT t\<preceq>PrimT pt"
*)

(* more detailed than necessary for type-safety, see above rules. *)
inductive "narrow G" intros (* narrowing reference conversion, cf. 5.1.5 *)

  subcls:  "G\<turnstile>C\<preceq>\<^sub>C D \<Longrightarrow> G\<turnstile>     Class D\<succ>Class C"
  implmt:  "\<not>G\<turnstile>C\<leadsto>I \<Longrightarrow> G\<turnstile>     Class C\<succ>Iface I"
  obj_arr: "G\<turnstile>Class Object\<succ>T.[]"
  int_cls: "G\<turnstile>     Iface I\<succ>Class C"
  subint:  "imethds G I hidings imethds G J entails 
	   (\<lambda>(md, mh   ) (md',mh').\<spacespace>G\<turnstile>mrt mh\<preceq>mrt mh') \<Longrightarrow>
	   \<not>G\<turnstile>I\<preceq>I J         \<spacespace>\<spacespace>\<spacespace>\<Longrightarrow> G\<turnstile>     Iface I\<succ>Iface J"
  array:   "G\<turnstile>RefT S\<succ>RefT T   \<spacespace>\<Longrightarrow> G\<turnstile>   RefT S.[]\<succ>RefT T.[]"

(*unused*)
lemma narrow_RefT: "G\<turnstile>RefT R\<succ>T \<Longrightarrow> \<exists>t. T=RefT t"
apply (ind_cases "G\<turnstile>S\<succ>T")
by auto

lemma narrow_RefT2: "G\<turnstile>S\<succ>RefT R \<Longrightarrow> \<exists>t. S=RefT t"
apply (ind_cases "G\<turnstile>S\<succ>T")
by auto

(*unused*)
lemma narrow_PrimT: "G\<turnstile>PrimT pt\<succ>T \<Longrightarrow> \<exists>t. T=PrimT t"
apply (ind_cases "G\<turnstile>S\<succ>T")
by auto

lemma narrow_PrimT2: "G\<turnstile>S\<succ>PrimT pt \<Longrightarrow>  
				  \<exists>t. S=PrimT t \<and> G\<turnstile>PrimT t\<preceq>PrimT pt"
apply (ind_cases "G\<turnstile>S\<succ>T")
by auto


section "casting relation"

inductive "cast G" intros (* casting conversion, cf. 5.5 *)

  widen:   "G\<turnstile>S\<preceq>T \<Longrightarrow> G\<turnstile>S\<preceq>? T"
  narrow:  "G\<turnstile>S\<succ>T \<Longrightarrow> G\<turnstile>S\<preceq>? T"

(*
lemma ??unknown??: "\<lbrakk>G\<turnstile>S\<preceq>T; G\<turnstile>S\<succ>T\<rbrakk> \<Longrightarrow> R"
 deferred *)

(*unused*)
lemma cast_RefT: "G\<turnstile>RefT R\<preceq>? T \<Longrightarrow> \<exists>t. T=RefT t"
apply (ind_cases "G\<turnstile>S\<preceq>? T")
by (auto dest: widen_RefT narrow_RefT)

lemma cast_RefT2: "G\<turnstile>S\<preceq>? RefT R \<Longrightarrow> \<exists>t. S=RefT t"
apply (ind_cases "G\<turnstile>S\<preceq>? T")
by (auto dest: widen_RefT2 narrow_RefT2)

(*unused*)
lemma cast_PrimT: "G\<turnstile>PrimT pt\<preceq>? T \<Longrightarrow> \<exists>t. T=PrimT t"
apply (ind_cases "G\<turnstile>S\<preceq>? T")
by (auto dest: widen_PrimT narrow_PrimT)

lemma cast_PrimT2: "G\<turnstile>S\<preceq>? PrimT pt \<Longrightarrow> \<exists>t. S=PrimT t \<and> G\<turnstile>PrimT t\<preceq>PrimT pt"
apply (ind_cases "G\<turnstile>S\<preceq>? T")
by (auto dest: widen_PrimT2 narrow_PrimT2)

end
