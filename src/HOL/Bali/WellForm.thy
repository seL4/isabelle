(*  Title:      HOL/Bali/WellForm.thy
    ID:         $Id$
    Author:     David von Oheimb and Norbert Schirmer
    License:    GPL (GNU GENERAL PUBLIC LICENSE)
*)

header {* Well-formedness of Java programs *}
theory WellForm = DefiniteAssignment:

text {*
For static checks on expressions and statements, see WellType.thy

improvements over Java Specification 1.0 (cf. 8.4.6.3, 8.4.6.4, 9.4.1):
\begin{itemize}
\item a method implementing or overwriting another method may have a result 
      type that widens to the result type of the other method 
      (instead of identical type)
\item if a method hides another method (both methods have to be static!)
  there are no restrictions to the result type 
  since the methods have to be static and there is no dynamic binding of 
  static methods
\item if an interface inherits more than one method with the same signature, the
  methods need not have identical return types
\end{itemize}
simplifications:
\begin{itemize}
\item Object and standard exceptions are assumed to be declared like normal 
      classes
\end{itemize}
*}

section "well-formed field declarations"
text  {* well-formed field declaration (common part for classes and interfaces),
        cf. 8.3 and (9.3) *}

constdefs
  wf_fdecl :: "prog \<Rightarrow> pname \<Rightarrow> fdecl \<Rightarrow> bool"
 "wf_fdecl G P \<equiv> \<lambda>(fn,f). is_acc_type G P (type f)"

lemma wf_fdecl_def2: "\<And>fd. wf_fdecl G P fd = is_acc_type G P (type (snd fd))"
apply (unfold wf_fdecl_def)
apply simp
done



section "well-formed method declarations"
  (*well-formed method declaration,cf. 8.4, 8.4.1, 8.4.3, 8.4.5, 14.3.2, (9.4)*)
  (* cf. 14.15, 15.7.2, for scope issues cf. 8.4.1 and 14.3.2 *)

text {*
A method head is wellformed if:
\begin{itemize}
\item the signature and the method head agree in the number of parameters
\item all types of the parameters are visible
\item the result type is visible
\item the parameter names are unique
\end{itemize} 
*}
constdefs
  wf_mhead :: "prog \<Rightarrow> pname \<Rightarrow> sig \<Rightarrow> mhead \<Rightarrow> bool"
 "wf_mhead G P \<equiv> \<lambda> sig mh. length (parTs sig) = length (pars mh) \<and>
			    \<spacespace> ( \<forall>T\<in>set (parTs sig). is_acc_type G P T) \<and> 
                            is_acc_type G P (resTy mh) \<and>
			    \<spacespace> distinct (pars mh)"


text {*
A method declaration is wellformed if:
\begin{itemize}
\item the method head is wellformed
\item the names of the local variables are unique
\item the types of the local variables must be accessible
\item the local variables don't shadow the parameters
\item the class of the method is defined
\item the body statement is welltyped with respect to the
      modified environment of local names, were the local variables, 
      the parameters the special result variable (Res) and This are assoziated
      with there types. 
\end{itemize}
*}

constdefs callee_lcl:: "qtname \<Rightarrow> sig \<Rightarrow> methd \<Rightarrow> lenv"
"callee_lcl C sig m 
 \<equiv> \<lambda> k. (case k of
            EName e 
            \<Rightarrow> (case e of 
                  VNam v 
                  \<Rightarrow>(table_of (lcls (mbody m))((pars m)[\<mapsto>](parTs sig))) v
                | Res \<Rightarrow> Some (resTy m))
	  | This \<Rightarrow> if is_static m then None else Some (Class C))"

constdefs parameters :: "methd \<Rightarrow> lname set"
"parameters m \<equiv>  set (map (EName \<circ> VNam) (pars m)) 
                  \<union> (if (static m) then {} else {This})"

constdefs
  wf_mdecl :: "prog \<Rightarrow> qtname \<Rightarrow> mdecl \<Rightarrow> bool"
 "wf_mdecl G C \<equiv> 
      \<lambda>(sig,m).
	  wf_mhead G (pid C) sig (mhead m) \<and> 
          unique (lcls (mbody m)) \<and> 
          (\<forall>(vn,T)\<in>set (lcls (mbody m)). is_acc_type G (pid C) T) \<and> 
	  (\<forall>pn\<in>set (pars m). table_of (lcls (mbody m)) pn = None) \<and>
          jumpNestingOkS {Ret} (stmt (mbody m)) \<and> 
          is_class G C \<and>
          \<lparr>prg=G,cls=C,lcl=callee_lcl C sig m\<rparr>\<turnstile>(stmt (mbody m))\<Colon>\<surd> \<and>
          (\<exists> A. \<lparr>prg=G,cls=C,lcl=callee_lcl C sig m\<rparr> 
                \<turnstile> parameters m \<guillemotright>\<langle>stmt (mbody m)\<rangle>\<guillemotright> A 
               \<and> Result \<in> nrm A)"

lemma callee_lcl_VNam_simp [simp]:
"callee_lcl C sig m (EName (VNam v)) 
  = (table_of (lcls (mbody m))((pars m)[\<mapsto>](parTs sig))) v"
by (simp add: callee_lcl_def)
 
lemma callee_lcl_Res_simp [simp]:
"callee_lcl C sig m (EName Res) = Some (resTy m)" 
by (simp add: callee_lcl_def)

lemma callee_lcl_This_simp [simp]:
"callee_lcl C sig m (This) = (if is_static m then None else Some (Class C))" 
by (simp add: callee_lcl_def)

lemma callee_lcl_This_static_simp:
"is_static m \<Longrightarrow> callee_lcl C sig m (This) = None"
by simp

lemma callee_lcl_This_not_static_simp:
"\<not> is_static m \<Longrightarrow> callee_lcl C sig m (This) = Some (Class C)"
by simp

lemma wf_mheadI: 
"\<lbrakk>length (parTs sig) = length (pars m); \<forall>T\<in>set (parTs sig). is_acc_type G P T;
  is_acc_type G P (resTy m); distinct (pars m)\<rbrakk> \<Longrightarrow>  
  wf_mhead G P sig m"
apply (unfold wf_mhead_def)
apply (simp (no_asm_simp))
done

lemma wf_mdeclI: "\<lbrakk>  
  wf_mhead G (pid C) sig (mhead m); unique (lcls (mbody m));  
  (\<forall>pn\<in>set (pars m). table_of (lcls (mbody m)) pn = None); 
  \<forall>(vn,T)\<in>set (lcls (mbody m)). is_acc_type G (pid C) T;
  jumpNestingOkS {Ret} (stmt (mbody m));
  is_class G C;
  \<lparr>prg=G,cls=C,lcl=callee_lcl C sig m\<rparr>\<turnstile>(stmt (mbody m))\<Colon>\<surd>;
  (\<exists> A. \<lparr>prg=G,cls=C,lcl=callee_lcl C sig m\<rparr> \<turnstile> parameters m \<guillemotright>\<langle>stmt (mbody m)\<rangle>\<guillemotright> A
        \<and> Result \<in> nrm A)
  \<rbrakk> \<Longrightarrow>  
  wf_mdecl G C (sig,m)"
apply (unfold wf_mdecl_def)
apply simp
done

lemma wf_mdeclE [consumes 1]:  
  "\<lbrakk>wf_mdecl G C (sig,m); 
    \<lbrakk>wf_mhead G (pid C) sig (mhead m); unique (lcls (mbody m));  
     \<forall>pn\<in>set (pars m). table_of (lcls (mbody m)) pn = None; 
     \<forall>(vn,T)\<in>set (lcls (mbody m)). is_acc_type G (pid C) T;
     jumpNestingOkS {Ret} (stmt (mbody m));
     is_class G C;
     \<lparr>prg=G,cls=C,lcl=callee_lcl C sig m\<rparr>\<turnstile>(stmt (mbody m))\<Colon>\<surd>;
   (\<exists> A. \<lparr>prg=G,cls=C,lcl=callee_lcl C sig m\<rparr>\<turnstile> parameters m \<guillemotright>\<langle>stmt (mbody m)\<rangle>\<guillemotright> A
        \<and> Result \<in> nrm A)
    \<rbrakk> \<Longrightarrow> P
  \<rbrakk> \<Longrightarrow> P"
by (unfold wf_mdecl_def) simp


lemma wf_mdeclD1: 
"wf_mdecl G C (sig,m) \<Longrightarrow>  
   wf_mhead G (pid C) sig (mhead m) \<and> unique (lcls (mbody m)) \<and>  
  (\<forall>pn\<in>set (pars m). table_of (lcls (mbody m)) pn = None) \<and> 
  (\<forall>(vn,T)\<in>set (lcls (mbody m)). is_acc_type G (pid C) T)"
apply (unfold wf_mdecl_def)
apply simp
done

lemma wf_mdecl_bodyD: 
"wf_mdecl G C (sig,m) \<Longrightarrow>  
 (\<exists>T. \<lparr>prg=G,cls=C,lcl=callee_lcl C sig m\<rparr>\<turnstile>Body C (stmt (mbody m))\<Colon>-T \<and> 
      G\<turnstile>T\<preceq>(resTy m))"
apply (unfold wf_mdecl_def)
apply clarify
apply (rule_tac x="(resTy m)" in exI)
apply (unfold wf_mhead_def)
apply (auto simp add: wf_mhead_def is_acc_type_def intro: wt.Body )
done


(*
lemma static_Object_methodsE [elim!]: 
 "\<lbrakk>wf_mdecl G Object (sig, m);static m\<rbrakk> \<Longrightarrow> R"
apply (unfold wf_mdecl_def)
apply auto
done
*)

lemma rT_is_acc_type: 
  "wf_mhead G P sig m \<Longrightarrow> is_acc_type G P (resTy m)"
apply (unfold wf_mhead_def)
apply auto
done

section "well-formed interface declarations"
  (* well-formed interface declaration, cf. 9.1, 9.1.2.1, 9.1.3, 9.4 *)

text {*
A interface declaration is wellformed if:
\begin{itemize}
\item the interface hierarchy is wellstructured
\item there is no class with the same name
\item the method heads are wellformed and not static and have Public access
\item the methods are uniquely named
\item all superinterfaces are accessible
\item the result type of a method overriding a method of Object widens to the
      result type of the overridden method.
      Shadowing static methods is forbidden.
\item the result type of a method overriding a set of methods defined in the
      superinterfaces widens to each of the corresponding result types
\end{itemize}
*}
constdefs
  wf_idecl :: "prog  \<Rightarrow> idecl \<Rightarrow> bool"
 "wf_idecl G \<equiv> 
    \<lambda>(I,i). 
        ws_idecl G I (isuperIfs i) \<and> 
	\<not>is_class G I \<and>
	(\<forall>(sig,mh)\<in>set (imethods i). wf_mhead G (pid I) sig mh \<and> 
                                     \<not>is_static mh \<and>
                                      accmodi mh = Public) \<and>
	unique (imethods i) \<and>
        (\<forall> J\<in>set (isuperIfs i). is_acc_iface G (pid I) J) \<and>
        (table_of (imethods i)
          hiding (methd G Object)
          under  (\<lambda> new old. accmodi old \<noteq> Private)
          entails (\<lambda>new old. G\<turnstile>resTy new\<preceq>resTy old \<and> 
                             is_static new = is_static old)) \<and> 
        (o2s \<circ> table_of (imethods i) 
               hidings Un_tables((\<lambda>J.(imethds G J))`set (isuperIfs i))
	       entails (\<lambda>new old. G\<turnstile>resTy new\<preceq>resTy old))"

lemma wf_idecl_mhead: "\<lbrakk>wf_idecl G (I,i); (sig,mh)\<in>set (imethods i)\<rbrakk> \<Longrightarrow>  
  wf_mhead G (pid I) sig mh \<and> \<not>is_static mh \<and> accmodi mh = Public"
apply (unfold wf_idecl_def)
apply auto
done

lemma wf_idecl_hidings: 
"wf_idecl G (I, i) \<Longrightarrow> 
  (\<lambda>s. o2s (table_of (imethods i) s)) 
  hidings Un_tables ((\<lambda>J. imethds G J) ` set (isuperIfs i))  
  entails \<lambda>new old. G\<turnstile>resTy new\<preceq>resTy old"
apply (unfold wf_idecl_def o_def)
apply simp
done

lemma wf_idecl_hiding:
"wf_idecl G (I, i) \<Longrightarrow> 
 (table_of (imethods i)
           hiding (methd G Object)
           under  (\<lambda> new old. accmodi old \<noteq> Private)
           entails (\<lambda>new old. G\<turnstile>resTy new\<preceq>resTy old \<and> 
                              is_static new = is_static old))"
apply (unfold wf_idecl_def)
apply simp
done

lemma wf_idecl_supD: 
"\<lbrakk>wf_idecl G (I,i); J \<in> set (isuperIfs i)\<rbrakk> 
 \<Longrightarrow> is_acc_iface G (pid I) J \<and> (J, I) \<notin> (subint1 G)^+"
apply (unfold wf_idecl_def ws_idecl_def)
apply auto
done

section "well-formed class declarations"
  (* well-formed class declaration, cf. 8.1, 8.1.2.1, 8.1.2.2, 8.1.3, 8.1.4 and
   class method declaration, cf. 8.4.3.3, 8.4.6.1, 8.4.6.2, 8.4.6.3, 8.4.6.4 *)

text {*
A class declaration is wellformed if:
\begin{itemize}
\item there is no interface with the same name
\item all superinterfaces are accessible and for all methods implementing 
      an interface method the result type widens to the result type of 
      the interface method, the method is not static and offers at least 
      as much access 
      (this actually means that the method has Public access, since all 
      interface methods have public access)
\item all field declarations are wellformed and the field names are unique
\item all method declarations are wellformed and the method names are unique
\item the initialization statement is welltyped
\item the classhierarchy is wellstructured
\item Unless the class is Object:
      \begin{itemize}
      \item the superclass is accessible
      \item for all methods overriding another method (of a superclass )the
            result type widens to the result type of the overridden method,
            the access modifier of the new method provides at least as much
            access as the overwritten one.
      \item for all methods hiding a method (of a superclass) the hidden 
            method must be static and offer at least as much access rights.
            Remark: In contrast to the Java Language Specification we don't
            restrict the result types of the method
            (as in case of overriding), because there seems to be no reason,
            since there is no dynamic binding of static methods.
            (cf. 8.4.6.3 vs. 15.12.1).
            Stricly speaking the restrictions on the access rights aren't 
            necessary to, since the static type and the access rights 
            together determine which method is to be called statically. 
            But if a class gains more then one static method with the 
            same signature due to inheritance, it is confusing when the 
            method selection depends on the access rights only: 
            e.g.
              Class C declares static public method foo().
              Class D is subclass of C and declares static method foo()
              with default package access.
              D.foo() ? if this call is in the same package as D then
                        foo of class D is called, otherwise foo of class C.
      \end{itemize}

\end{itemize}
*}
(* to Table *)
constdefs entails:: "('a,'b) table \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> bool"
                                 ("_ entails _" 20)
"t entails P \<equiv> \<forall>k. \<forall> x \<in> t k: P x"

lemma entailsD:
 "\<lbrakk>t entails P; t k = Some x\<rbrakk> \<Longrightarrow> P x"
by (simp add: entails_def)

lemma empty_entails[simp]: "empty entails P"
by (simp add: entails_def)

constdefs
 wf_cdecl :: "prog \<Rightarrow> cdecl \<Rightarrow> bool"
"wf_cdecl G \<equiv> 
   \<lambda>(C,c).
      \<not>is_iface G C \<and>
      (\<forall>I\<in>set (superIfs c). is_acc_iface G (pid C) I \<and>
        (\<forall>s. \<forall> im \<in> imethds G I s.
      	    (\<exists> cm \<in> methd  G C s: G\<turnstile>resTy cm\<preceq>resTy im \<and>
      	                             \<not> is_static cm \<and>
                                     accmodi im \<le> accmodi cm))) \<and>
      (\<forall>f\<in>set (cfields c). wf_fdecl G (pid C) f) \<and> unique (cfields c) \<and> 
      (\<forall>m\<in>set (methods c). wf_mdecl G C m) \<and> unique (methods c) \<and>
      jumpNestingOkS {} (init c) \<and>
      (\<exists> A. \<lparr>prg=G,cls=C,lcl=empty\<rparr>\<turnstile> {} \<guillemotright>\<langle>init c\<rangle>\<guillemotright> A) \<and>
      \<lparr>prg=G,cls=C,lcl=empty\<rparr>\<turnstile>(init c)\<Colon>\<surd> \<and> ws_cdecl G C (super c) \<and>
      (C \<noteq> Object \<longrightarrow> 
            (is_acc_class G (pid C) (super c) \<and>
            (table_of (map (\<lambda> (s,m). (s,C,m)) (methods c)) 
             entails (\<lambda> new. \<forall> old sig. 
                       (G,sig\<turnstile>new overrides\<^sub>S old 
                        \<longrightarrow> (G\<turnstile>resTy new\<preceq>resTy old \<and>
                             accmodi old \<le> accmodi new \<and>
      	                     \<not>is_static old)) \<and>
                       (G,sig\<turnstile>new hides old 
                         \<longrightarrow> (accmodi old \<le> accmodi new \<and>
      	                      is_static old)))) 
            ))"

(*
constdefs
 wf_cdecl :: "prog \<Rightarrow> cdecl \<Rightarrow> bool"
"wf_cdecl G \<equiv> 
   \<lambda>(C,c).
      \<not>is_iface G C \<and>
      (\<forall>I\<in>set (superIfs c). is_acc_iface G (pid C) I \<and>
        (\<forall>s. \<forall> im \<in> imethds G I s.
      	    (\<exists> cm \<in> methd  G C s: G\<turnstile>resTy (mthd cm)\<preceq>resTy (mthd im) \<and>
      	                             \<not> is_static cm \<and>
                                     accmodi im \<le> accmodi cm))) \<and>
      (\<forall>f\<in>set (cfields c). wf_fdecl G (pid C) f) \<and> unique (cfields c) \<and> 
      (\<forall>m\<in>set (methods c). wf_mdecl G C m) \<and> unique (methods c) \<and> 
      \<lparr>prg=G,cls=C,lcl=empty\<rparr>\<turnstile>(init c)\<Colon>\<surd> \<and> ws_cdecl G C (super c) \<and>
      (C \<noteq> Object \<longrightarrow> 
            (is_acc_class G (pid C) (super c) \<and>
            (table_of (map (\<lambda> (s,m). (s,C,m)) (methods c)) 
              hiding methd G (super c)
              under (\<lambda> new old. G\<turnstile>new overrides old)
              entails (\<lambda> new old. 
                           (G\<turnstile>resTy (mthd new)\<preceq>resTy (mthd old) \<and>
                            accmodi old \<le> accmodi new \<and>
      	                   \<not> is_static old)))  \<and>
            (table_of (map (\<lambda> (s,m). (s,C,m)) (methods c)) 
              hiding methd G (super c)
              under (\<lambda> new old. G\<turnstile>new hides old)
              entails (\<lambda> new old. is_static old \<and> 
                                  accmodi old \<le> accmodi new))  \<and>
            (table_of (cfields c) hiding accfield G C (super c)
              entails (\<lambda> newF oldF. accmodi oldF \<le> access newF))))"
*)

lemma wf_cdeclE [consumes 1]: 
 "\<lbrakk>wf_cdecl G (C,c);
   \<lbrakk>\<not>is_iface G C;
    (\<forall>I\<in>set (superIfs c). is_acc_iface G (pid C) I \<and>
        (\<forall>s. \<forall> im \<in> imethds G I s.
      	    (\<exists> cm \<in> methd  G C s: G\<turnstile>resTy cm\<preceq>resTy im \<and>
      	                             \<not> is_static cm \<and>
                                     accmodi im \<le> accmodi cm))); 
      \<forall>f\<in>set (cfields c). wf_fdecl G (pid C) f; unique (cfields c); 
      \<forall>m\<in>set (methods c). wf_mdecl G C m; unique (methods c);
      jumpNestingOkS {} (init c);
      \<exists> A. \<lparr>prg=G,cls=C,lcl=empty\<rparr>\<turnstile> {} \<guillemotright>\<langle>init c\<rangle>\<guillemotright> A;
      \<lparr>prg=G,cls=C,lcl=empty\<rparr>\<turnstile>(init c)\<Colon>\<surd>; 
      ws_cdecl G C (super c); 
      (C \<noteq> Object \<longrightarrow> 
            (is_acc_class G (pid C) (super c) \<and>
            (table_of (map (\<lambda> (s,m). (s,C,m)) (methods c)) 
             entails (\<lambda> new. \<forall> old sig. 
                       (G,sig\<turnstile>new overrides\<^sub>S old 
                        \<longrightarrow> (G\<turnstile>resTy new\<preceq>resTy old \<and>
                             accmodi old \<le> accmodi new \<and>
      	                     \<not>is_static old)) \<and>
                       (G,sig\<turnstile>new hides old 
                         \<longrightarrow> (accmodi old \<le> accmodi new \<and>
      	                      is_static old)))) 
            ))\<rbrakk> \<Longrightarrow> P
  \<rbrakk> \<Longrightarrow> P"
by (unfold wf_cdecl_def) simp

lemma wf_cdecl_unique: 
"wf_cdecl G (C,c) \<Longrightarrow> unique (cfields c) \<and> unique (methods c)"
apply (unfold wf_cdecl_def)
apply auto
done

lemma wf_cdecl_fdecl: 
"\<lbrakk>wf_cdecl G (C,c); f\<in>set (cfields c)\<rbrakk> \<Longrightarrow> wf_fdecl G (pid C) f"
apply (unfold wf_cdecl_def)
apply auto
done

lemma wf_cdecl_mdecl: 
"\<lbrakk>wf_cdecl G (C,c); m\<in>set (methods c)\<rbrakk> \<Longrightarrow> wf_mdecl G C m"
apply (unfold wf_cdecl_def)
apply auto
done

lemma wf_cdecl_impD: 
"\<lbrakk>wf_cdecl G (C,c); I\<in>set (superIfs c)\<rbrakk> 
\<Longrightarrow> is_acc_iface G (pid C) I \<and>  
    (\<forall>s. \<forall>im \<in> imethds G I s.  
        (\<exists>cm \<in> methd G C s: G\<turnstile>resTy cm\<preceq>resTy im \<and> \<not>is_static cm \<and>
                                   accmodi im \<le> accmodi cm))"
apply (unfold wf_cdecl_def)
apply auto
done

lemma wf_cdecl_supD: 
"\<lbrakk>wf_cdecl G (C,c); C \<noteq> Object\<rbrakk> \<Longrightarrow>  
  is_acc_class G (pid C) (super c) \<and> (super c,C) \<notin> (subcls1 G)^+ \<and> 
   (table_of (map (\<lambda> (s,m). (s,C,m)) (methods c)) 
    entails (\<lambda> new. \<forall> old sig. 
                 (G,sig\<turnstile>new overrides\<^sub>S old 
                  \<longrightarrow> (G\<turnstile>resTy new\<preceq>resTy old \<and>
                       accmodi old \<le> accmodi new \<and>
                       \<not>is_static old)) \<and>
                 (G,sig\<turnstile>new hides old 
                   \<longrightarrow> (accmodi old \<le> accmodi new \<and>
                        is_static old))))"
apply (unfold wf_cdecl_def ws_cdecl_def)
apply auto
done


lemma wf_cdecl_overrides_SomeD:
"\<lbrakk>wf_cdecl G (C,c); C \<noteq> Object; table_of (methods c) sig = Some newM;
  G,sig\<turnstile>(C,newM) overrides\<^sub>S old
\<rbrakk> \<Longrightarrow>  G\<turnstile>resTy newM\<preceq>resTy old \<and>
       accmodi old \<le> accmodi newM \<and>
       \<not> is_static old" 
apply (drule (1) wf_cdecl_supD)
apply (clarify)
apply (drule entailsD)
apply   (blast intro: table_of_map_SomeI)
apply (drule_tac x="old" in spec)
apply (auto dest: overrides_eq_sigD simp add: msig_def)
done

lemma wf_cdecl_hides_SomeD:
"\<lbrakk>wf_cdecl G (C,c); C \<noteq> Object; table_of (methods c) sig = Some newM;
  G,sig\<turnstile>(C,newM) hides old
\<rbrakk> \<Longrightarrow>  accmodi old \<le> access newM \<and>
       is_static old" 
apply (drule (1) wf_cdecl_supD)
apply (clarify)
apply (drule entailsD)
apply   (blast intro: table_of_map_SomeI)
apply (drule_tac x="old" in spec)
apply (auto dest: hides_eq_sigD simp add: msig_def)
done

lemma wf_cdecl_wt_init: 
 "wf_cdecl G (C, c) \<Longrightarrow> \<lparr>prg=G,cls=C,lcl=empty\<rparr>\<turnstile>init c\<Colon>\<surd>"
apply (unfold wf_cdecl_def)
apply auto
done


section "well-formed programs"
  (* well-formed program, cf. 8.1, 9.1 *)

text {*
A program declaration is wellformed if:
\begin{itemize}
\item the class ObjectC of Object is defined
\item every method of has an access modifier distinct from Package. This is
      necessary since every interface automatically inherits from Object.  
      We must know, that every time a Object method is "overriden" by an 
      interface method this is also overriden by the class implementing the
      the interface (see @{text "implement_dynmethd and class_mheadsD"})
\item all standard Exceptions are defined
\item all defined interfaces are wellformed
\item all defined classes are wellformed
\end{itemize}
*}
constdefs
  wf_prog  :: "prog \<Rightarrow> bool"
 "wf_prog G \<equiv> let is = ifaces G; cs = classes G in
	         ObjectC \<in> set cs \<and> 
                (\<forall> m\<in>set Object_mdecls. accmodi m \<noteq> Package) \<and>
                (\<forall>xn. SXcptC xn \<in> set cs) \<and>
		(\<forall>i\<in>set is. wf_idecl G i) \<and> unique is \<and>
		(\<forall>c\<in>set cs. wf_cdecl G c) \<and> unique cs"

lemma wf_prog_idecl: "\<lbrakk>iface G I = Some i; wf_prog G\<rbrakk> \<Longrightarrow> wf_idecl G (I,i)"
apply (unfold wf_prog_def Let_def)
apply simp
apply (fast dest: map_of_SomeD)
done

lemma wf_prog_cdecl: "\<lbrakk>class G C = Some c; wf_prog G\<rbrakk> \<Longrightarrow> wf_cdecl G (C,c)"
apply (unfold wf_prog_def Let_def)
apply simp
apply (fast dest: map_of_SomeD)
done

lemma wf_prog_Object_mdecls:
"wf_prog G \<Longrightarrow> (\<forall> m\<in>set Object_mdecls. accmodi m \<noteq> Package)"
apply (unfold wf_prog_def Let_def)
apply simp
done

lemma wf_prog_acc_superD:
 "\<lbrakk>wf_prog G; class G C = Some c; C \<noteq> Object \<rbrakk> 
  \<Longrightarrow> is_acc_class G (pid C) (super c)"
by (auto dest: wf_prog_cdecl wf_cdecl_supD)

lemma wf_ws_prog [elim!,simp]: "wf_prog G \<Longrightarrow> ws_prog G"
apply (unfold wf_prog_def Let_def)
apply (rule ws_progI)
apply  (simp_all (no_asm))
apply  (auto simp add: is_acc_class_def is_acc_iface_def 
             dest!: wf_idecl_supD wf_cdecl_supD )+
done

lemma class_Object [simp]: 
"wf_prog G \<Longrightarrow> 
  class G Object = Some \<lparr>access=Public,cfields=[],methods=Object_mdecls,
                                  init=Skip,super=arbitrary,superIfs=[]\<rparr>"
apply (unfold wf_prog_def Let_def ObjectC_def)
apply (fast dest!: map_of_SomeI)
done

lemma methd_Object[simp]: "wf_prog G \<Longrightarrow> methd G Object =  
  table_of (map (\<lambda>(s,m). (s, Object, m)) Object_mdecls)"
apply (subst methd_rec)
apply (auto simp add: Let_def)
done

lemma wf_prog_Object_methd:
"\<lbrakk>wf_prog G; methd G Object sig = Some m\<rbrakk> \<Longrightarrow> accmodi m \<noteq> Package"
by (auto dest!: wf_prog_Object_mdecls) (auto dest!: map_of_SomeD) 

lemma wf_prog_Object_is_public[intro]:
 "wf_prog G \<Longrightarrow> is_public G Object"
by (auto simp add: is_public_def dest: class_Object)

lemma class_SXcpt [simp]: 
"wf_prog G \<Longrightarrow> 
  class G (SXcpt xn) = Some \<lparr>access=Public,cfields=[],methods=SXcpt_mdecls,
                                   init=Skip,
                                   super=if xn = Throwable then Object 
                                                           else SXcpt Throwable,
                                   superIfs=[]\<rparr>"
apply (unfold wf_prog_def Let_def SXcptC_def)
apply (fast dest!: map_of_SomeI)
done

lemma wf_ObjectC [simp]: 
	"wf_cdecl G ObjectC = (\<not>is_iface G Object \<and> Ball (set Object_mdecls)
  (wf_mdecl G Object) \<and> unique Object_mdecls)"
apply (unfold wf_cdecl_def ws_cdecl_def ObjectC_def)
apply (auto intro: da.Skip)
done

lemma Object_is_class [simp,elim!]: "wf_prog G \<Longrightarrow> is_class G Object"
apply (simp (no_asm_simp))
done
 
lemma Object_is_acc_class [simp,elim!]: "wf_prog G \<Longrightarrow> is_acc_class G S Object"
apply (simp (no_asm_simp) add: is_acc_class_def is_public_def
                               accessible_in_RefT_simp)
done

lemma SXcpt_is_class [simp,elim!]: "wf_prog G \<Longrightarrow> is_class G (SXcpt xn)"
apply (simp (no_asm_simp))
done

lemma SXcpt_is_acc_class [simp,elim!]: 
"wf_prog G \<Longrightarrow> is_acc_class G S (SXcpt xn)"
apply (simp (no_asm_simp) add: is_acc_class_def is_public_def
                               accessible_in_RefT_simp)
done

lemma fields_Object [simp]: "wf_prog G \<Longrightarrow> DeclConcepts.fields G Object = []"
by (force intro: fields_emptyI)

lemma accfield_Object [simp]: 
 "wf_prog G \<Longrightarrow> accfield G S Object = empty"
apply (unfold accfield_def)
apply (simp (no_asm_simp) add: Let_def)
done

lemma fields_Throwable [simp]: 
 "wf_prog G \<Longrightarrow> DeclConcepts.fields G (SXcpt Throwable) = []"
by (force intro: fields_emptyI)

lemma fields_SXcpt [simp]: "wf_prog G \<Longrightarrow> DeclConcepts.fields G (SXcpt xn) = []"
apply (case_tac "xn = Throwable")
apply  (simp (no_asm_simp))
by (force intro: fields_emptyI)

lemmas widen_trans = ws_widen_trans [OF _ _ wf_ws_prog, elim]
lemma widen_trans2 [elim]: "\<lbrakk>G\<turnstile>U\<preceq>T; G\<turnstile>S\<preceq>U; wf_prog G\<rbrakk> \<Longrightarrow> G\<turnstile>S\<preceq>T"
apply (erule (2) widen_trans)
done

lemma Xcpt_subcls_Throwable [simp]: 
"wf_prog G \<Longrightarrow> G\<turnstile>SXcpt xn\<preceq>\<^sub>C SXcpt Throwable"
apply (rule SXcpt_subcls_Throwable_lemma)
apply auto
done

lemma unique_fields: 
 "\<lbrakk>is_class G C; wf_prog G\<rbrakk> \<Longrightarrow> unique (DeclConcepts.fields G C)"
apply (erule ws_unique_fields)
apply  (erule wf_ws_prog)
apply (erule (1) wf_prog_cdecl [THEN wf_cdecl_unique [THEN conjunct1]])
done

lemma fields_mono: 
"\<lbrakk>table_of (DeclConcepts.fields G C) fn = Some f; G\<turnstile>D\<preceq>\<^sub>C C; 
  is_class G D; wf_prog G\<rbrakk> 
   \<Longrightarrow> table_of (DeclConcepts.fields G D) fn = Some f"
apply (rule map_of_SomeI)
apply  (erule (1) unique_fields)
apply (erule (1) map_of_SomeD [THEN fields_mono_lemma])
apply (erule wf_ws_prog)
done


lemma fields_is_type [elim]: 
"\<lbrakk>table_of (DeclConcepts.fields G C) m = Some f; wf_prog G; is_class G C\<rbrakk> \<Longrightarrow> 
      is_type G (type f)"
apply (frule wf_ws_prog)
apply (force dest: fields_declC [THEN conjunct1] 
                   wf_prog_cdecl [THEN wf_cdecl_fdecl]
             simp add: wf_fdecl_def2 is_acc_type_def)
done

lemma imethds_wf_mhead [rule_format (no_asm)]: 
"\<lbrakk>m \<in> imethds G I sig; wf_prog G; is_iface G I\<rbrakk> \<Longrightarrow>  
  wf_mhead G (pid (decliface m)) sig (mthd m) \<and> 
  \<not> is_static m \<and> accmodi m = Public"
apply (frule wf_ws_prog)
apply (drule (2) imethds_declI [THEN conjunct1])
apply clarify
apply (frule_tac I="(decliface m)" in wf_prog_idecl,assumption)
apply (drule wf_idecl_mhead)
apply (erule map_of_SomeD)
apply (cases m, simp)
done

lemma methd_wf_mdecl: 
 "\<lbrakk>methd G C sig = Some m; wf_prog G; class G C = Some y\<rbrakk> \<Longrightarrow>  
  G\<turnstile>C\<preceq>\<^sub>C (declclass m) \<and> is_class G (declclass m) \<and> 
  wf_mdecl G (declclass m) (sig,(mthd m))"
apply (frule wf_ws_prog)
apply (drule (1) methd_declC)
apply  fast
apply clarsimp
apply (frule (1) wf_prog_cdecl, erule wf_cdecl_mdecl, erule map_of_SomeD)
done

(*
This lemma doesn't hold!
lemma methd_rT_is_acc_type: 
"\<lbrakk>wf_prog G;methd G C C sig = Some (D,m);
    class G C = Some y\<rbrakk>
\<Longrightarrow> is_acc_type G (pid C) (resTy m)"
The result Type is only visible in the scope of defining class D 
"is_vis_type G (pid D) (resTy m)" but not necessarily in scope of class C!
(The same is true for the type of pramaters of a method)
*)


lemma methd_rT_is_type: 
"\<lbrakk>wf_prog G;methd G C sig = Some m;
    class G C = Some y\<rbrakk>
\<Longrightarrow> is_type G (resTy m)"
apply (drule (2) methd_wf_mdecl)
apply clarify
apply (drule wf_mdeclD1)
apply clarify
apply (drule rT_is_acc_type)
apply (cases m, simp add: is_acc_type_def)
done

lemma accmethd_rT_is_type:
"\<lbrakk>wf_prog G;accmethd G S C sig = Some m;
    class G C = Some y\<rbrakk>
\<Longrightarrow> is_type G (resTy m)"
by (auto simp add: accmethd_def  
         intro: methd_rT_is_type)

lemma methd_Object_SomeD:
"\<lbrakk>wf_prog G;methd G Object sig = Some m\<rbrakk> 
 \<Longrightarrow> declclass m = Object"
by (auto dest: class_Object simp add: methd_rec )

lemma wf_imethdsD: 
 "\<lbrakk>im \<in> imethds G I sig;wf_prog G; is_iface G I\<rbrakk> 
 \<Longrightarrow> \<not>is_static im \<and> accmodi im = Public"
proof -
  assume asm: "wf_prog G" "is_iface G I" "im \<in> imethds G I sig"
  have "wf_prog G \<longrightarrow> 
         (\<forall> i im. iface G I = Some i \<longrightarrow> im \<in> imethds G I sig
                  \<longrightarrow> \<not>is_static im \<and> accmodi im = Public)" (is "?P G I")
  proof (rule iface_rec.induct,intro allI impI)
    fix G I i im
    assume hyp: "\<forall> J i. J \<in> set (isuperIfs i) \<and> ws_prog G \<and> iface G I = Some i
                 \<longrightarrow> ?P G J"
    assume wf: "wf_prog G" and if_I: "iface G I = Some i" and 
           im: "im \<in> imethds G I sig" 
    show "\<not>is_static im \<and> accmodi im = Public" 
    proof -
      let ?inherited = "Un_tables (imethds G ` set (isuperIfs i))"
      let ?new = "(o2s \<circ> table_of (map (\<lambda>(s, mh). (s, I, mh)) (imethods i)))"
      from if_I wf im have imethds:"im \<in> (?inherited \<oplus>\<oplus> ?new) sig"
	by (simp add: imethds_rec)
      from wf if_I have 
	wf_supI: "\<forall> J. J \<in> set (isuperIfs i) \<longrightarrow> (\<exists> j. iface G J = Some j)"
	by (blast dest: wf_prog_idecl wf_idecl_supD is_acc_ifaceD)
      from wf if_I have
	"\<forall> im \<in> set (imethods i). \<not> is_static im \<and> accmodi im = Public"
	by (auto dest!: wf_prog_idecl wf_idecl_mhead)
      then have new_ok: "\<forall> im. table_of (imethods i) sig = Some im 
                         \<longrightarrow>  \<not> is_static im \<and> accmodi im = Public"
	by (auto dest!: table_of_Some_in_set)
      show ?thesis
	proof (cases "?new sig = {}")
	  case True
	  from True wf wf_supI if_I imethds hyp 
	  show ?thesis by (auto simp del:  split_paired_All)  
	next
	  case False
	  from False wf wf_supI if_I imethds new_ok hyp 
	  show ?thesis by (auto dest: wf_idecl_hidings hidings_entailsD)
	qed
      qed
    qed
  with asm show ?thesis by (auto simp del: split_paired_All)
qed

lemma wf_prog_hidesD:
  assumes hides: "G \<turnstile>new hides old" and wf: "wf_prog G"
  shows
   "accmodi old \<le> accmodi new \<and>
    is_static old"
proof -
  from hides 
  obtain c where 
    clsNew: "class G (declclass new) = Some c" and
    neqObj: "declclass new \<noteq> Object"
    by (auto dest: hidesD declared_in_classD)
  with hides obtain newM oldM where
    newM: "table_of (methods c) (msig new) = Some newM" and 
     new: "new = (declclass new,(msig new),newM)" and
     old: "old = (declclass old,(msig old),oldM)" and
          "msig new = msig old"
    by (cases new,cases old) 
       (auto dest: hidesD 
         simp add: cdeclaredmethd_def declared_in_def)
  with hides 
  have hides':
        "G,(msig new)\<turnstile>(declclass new,newM) hides (declclass old,oldM)"
    by auto
  from clsNew wf 
  have "wf_cdecl G (declclass new,c)" by (blast intro: wf_prog_cdecl)
  note wf_cdecl_hides_SomeD [OF this neqObj newM hides']
  with new old 
  show ?thesis
    by (cases new, cases old) auto
qed

text {* Compare this lemma about static  
overriding @{term "G \<turnstile>new overrides\<^sub>S old"} with the definition of 
dynamic overriding @{term "G \<turnstile>new overrides old"}. 
Conforming result types and restrictions on the access modifiers of the old 
and the new method are not part of the predicate for static overriding. But
they are enshured in a wellfromed program.  Dynamic overriding has 
no restrictions on the access modifiers but enforces confrom result types 
as precondition. But with some efford we can guarantee the access modifier
restriction for dynamic overriding, too. See lemma 
@{text wf_prog_dyn_override_prop}.
*}
lemma wf_prog_stat_overridesD:
  assumes stat_override: "G \<turnstile>new overrides\<^sub>S old" and wf: "wf_prog G"
  shows
   "G\<turnstile>resTy new\<preceq>resTy old \<and>
    accmodi old \<le> accmodi new \<and>
    \<not> is_static old"
proof -
  from stat_override 
  obtain c where 
    clsNew: "class G (declclass new) = Some c" and
    neqObj: "declclass new \<noteq> Object"
    by (auto dest: stat_overrides_commonD declared_in_classD)
  with stat_override obtain newM oldM where
    newM: "table_of (methods c) (msig new) = Some newM" and 
     new: "new = (declclass new,(msig new),newM)" and
     old: "old = (declclass old,(msig old),oldM)" and
          "msig new = msig old"
    by (cases new,cases old) 
       (auto dest: stat_overrides_commonD 
         simp add: cdeclaredmethd_def declared_in_def)
  with stat_override 
  have stat_override':
        "G,(msig new)\<turnstile>(declclass new,newM) overrides\<^sub>S (declclass old,oldM)"
    by auto
  from clsNew wf 
  have "wf_cdecl G (declclass new,c)" by (blast intro: wf_prog_cdecl)
  note wf_cdecl_overrides_SomeD [OF this neqObj newM stat_override']
  with new old 
  show ?thesis
    by (cases new, cases old) auto
qed
    
lemma static_to_dynamic_overriding: 
  assumes stat_override: "G\<turnstile>new overrides\<^sub>S old" and wf : "wf_prog G"
  shows "G\<turnstile>new overrides old"
proof -
  from stat_override 
  show ?thesis (is "?Overrides new old")
  proof (induct)
    case (Direct new old superNew)
    then have stat_override:"G\<turnstile>new overrides\<^sub>S old" 
      by (rule stat_overridesR.Direct)
    from stat_override wf
    have resTy_widen: "G\<turnstile>resTy new\<preceq>resTy old" and
      not_static_old: "\<not> is_static old" 
      by (auto dest: wf_prog_stat_overridesD)  
    have not_private_new: "accmodi new \<noteq> Private"
    proof -
      from stat_override 
      have "accmodi old \<noteq> Private"
	by (rule no_Private_stat_override)
      moreover
      from stat_override wf
      have "accmodi old \<le> accmodi new"
	by (auto dest: wf_prog_stat_overridesD)
      ultimately
      show ?thesis
	by (auto dest: acc_modi_bottom)
    qed
    with Direct resTy_widen not_static_old 
    show "?Overrides new old" 
      by (auto intro: overridesR.Direct stat_override_declclasses_relation) 
  next
    case (Indirect inter new old)
    then show "?Overrides new old" 
      by (blast intro: overridesR.Indirect) 
  qed
qed

lemma non_Package_instance_method_inheritance:
  assumes old_inheritable: "G\<turnstile>Method old inheritable_in (pid C)" and
              accmodi_old: "accmodi old \<noteq> Package" and 
          instance_method: "\<not> is_static old" and
                   subcls: "G\<turnstile>C \<prec>\<^sub>C declclass old" and
             old_declared: "G\<turnstile>Method old declared_in (declclass old)" and
                       wf: "wf_prog G"
  shows "G\<turnstile>Method old member_of C \<or>
   (\<exists> new. G\<turnstile> new overrides\<^sub>S old \<and> G\<turnstile>Method new member_of C)"
proof -
  from wf have ws: "ws_prog G" by auto
  from old_declared have iscls_declC_old: "is_class G (declclass old)"
    by (auto simp add: declared_in_def cdeclaredmethd_def)
  from subcls have  iscls_C: "is_class G C"
    by (blast dest:  subcls_is_class)
  from iscls_C ws old_inheritable subcls 
  show ?thesis (is "?P C old")
  proof (induct rule: ws_class_induct')
    case Object
    assume "G\<turnstile>Object\<prec>\<^sub>C declclass old"
    then show "?P Object old"
      by blast
  next
    case (Subcls C c)
    assume cls_C: "class G C = Some c" and 
       neq_C_Obj: "C \<noteq> Object" and
             hyp: "\<lbrakk>G \<turnstile>Method old inheritable_in pid (super c); 
                   G\<turnstile>super c\<prec>\<^sub>C declclass old\<rbrakk> \<Longrightarrow> ?P (super c) old" and
     inheritable: "G \<turnstile>Method old inheritable_in pid C" and
         subclsC: "G\<turnstile>C\<prec>\<^sub>C declclass old"
    from cls_C neq_C_Obj  
    have super: "G\<turnstile>C \<prec>\<^sub>C\<^sub>1 super c" 
      by (rule subcls1I)
    from wf cls_C neq_C_Obj
    have accessible_super: "G\<turnstile>(Class (super c)) accessible_in (pid C)" 
      by (auto dest: wf_prog_cdecl wf_cdecl_supD is_acc_classD)
    {
      fix old
      assume    member_super: "G\<turnstile>Method old member_of (super c)"
      assume     inheritable: "G \<turnstile>Method old inheritable_in pid C"
      assume instance_method: "\<not> is_static old"
      from member_super
      have old_declared: "G\<turnstile>Method old declared_in (declclass old)"
       by (cases old) (auto dest: member_of_declC)
      have "?P C old"
      proof (cases "G\<turnstile>mid (msig old) undeclared_in C")
	case True
	with inheritable super accessible_super member_super
	have "G\<turnstile>Method old member_of C"
	  by (cases old) (auto intro: members.Inherited)
	then show ?thesis
	  by auto
      next
	case False
	then obtain new_member where
	     "G\<turnstile>new_member declared_in C" and
             "mid (msig old) = memberid new_member"
          by (auto dest: not_undeclared_declared)
	then obtain new where
	          new: "G\<turnstile>Method new declared_in C" and
               eq_sig: "msig old = msig new" and
	    declC_new: "declclass new = C" 
	  by (cases new_member) auto
	then have member_new: "G\<turnstile>Method new member_of C"
	  by (cases new) (auto intro: members.Immediate)
	from declC_new super member_super
	have subcls_new_old: "G\<turnstile>declclass new \<prec>\<^sub>C declclass old"
	  by (auto dest!: member_of_subclseq_declC
	            dest: r_into_trancl intro: trancl_rtrancl_trancl)
	show ?thesis
	proof (cases "is_static new")
	  case False
	  with eq_sig declC_new new old_declared inheritable
	       super member_super subcls_new_old
	  have "G\<turnstile>new overrides\<^sub>S old"
	    by (auto intro!: stat_overridesR.Direct)
	  with member_new show ?thesis
	    by blast
	next
	  case True
	  with eq_sig declC_new subcls_new_old new old_declared inheritable
	  have "G\<turnstile>new hides old"
	    by (auto intro: hidesI)    
	  with wf 
	  have "is_static old"
	    by (blast dest: wf_prog_hidesD)
	  with instance_method
	  show ?thesis
	    by (contradiction)
	qed
      qed
    } note hyp_member_super = this
    from subclsC cls_C 
    have "G\<turnstile>(super c)\<preceq>\<^sub>C declclass old"
      by (rule subcls_superD)
    then
    show "?P C old"
    proof (cases rule: subclseq_cases) 
      case Eq
      assume "super c = declclass old"
      with old_declared 
      have "G\<turnstile>Method old member_of (super c)" 
	by (cases old) (auto intro: members.Immediate)
      with inheritable instance_method 
      show ?thesis
	by (blast dest: hyp_member_super)
    next
      case Subcls
      assume "G\<turnstile>super c\<prec>\<^sub>C declclass old"
      moreover
      from inheritable accmodi_old
      have "G \<turnstile>Method old inheritable_in pid (super c)"
	by (cases "accmodi old") (auto simp add: inheritable_in_def)
      ultimately
      have "?P (super c) old"
	by (blast dest: hyp)
      then show ?thesis
      proof
	assume "G \<turnstile>Method old member_of super c"
	with inheritable instance_method
	show ?thesis
	  by (blast dest: hyp_member_super)
      next
	assume "\<exists>new. G \<turnstile> new overrides\<^sub>S old \<and> G \<turnstile>Method new member_of super c"
	then obtain super_new where
	  super_new_override:  "G \<turnstile> super_new overrides\<^sub>S old" and
            super_new_member:  "G \<turnstile>Method super_new member_of super c"
	  by blast
	from super_new_override wf
	have "accmodi old \<le> accmodi super_new"
	  by (auto dest: wf_prog_stat_overridesD)
	with inheritable accmodi_old
	have "G \<turnstile>Method super_new inheritable_in pid C"
	  by (auto simp add: inheritable_in_def 
	              split: acc_modi.splits
                       dest: acc_modi_le_Dests)
	moreover
	from super_new_override 
	have "\<not> is_static super_new"
	  by (auto dest: stat_overrides_commonD)
	moreover
	note super_new_member
	ultimately have "?P C super_new"
	  by (auto dest: hyp_member_super)
	then show ?thesis
	proof 
	  assume "G \<turnstile>Method super_new member_of C"
	  with super_new_override
	  show ?thesis
	    by blast
	next
	  assume "\<exists>new. G \<turnstile> new overrides\<^sub>S super_new \<and> 
                  G \<turnstile>Method new member_of C"
	  with super_new_override show ?thesis
	    by (blast intro: stat_overridesR.Indirect) 
	qed
      qed
    qed
  qed
qed

lemma non_Package_instance_method_inheritance_cases [consumes 6,
         case_names Inheritance Overriding]:
  assumes old_inheritable: "G\<turnstile>Method old inheritable_in (pid C)" and
              accmodi_old: "accmodi old \<noteq> Package" and 
          instance_method: "\<not> is_static old" and
                   subcls: "G\<turnstile>C \<prec>\<^sub>C declclass old" and
             old_declared: "G\<turnstile>Method old declared_in (declclass old)" and
                       wf: "wf_prog G" and
              inheritance: "G\<turnstile>Method old member_of C \<Longrightarrow> P" and
               overriding: "\<And> new.
                           \<lbrakk>G\<turnstile> new overrides\<^sub>S old;G\<turnstile>Method new member_of C\<rbrakk>
                           \<Longrightarrow> P"
  shows P
proof -
  from old_inheritable accmodi_old instance_method subcls old_declared wf 
       inheritance overriding
  show ?thesis
    by (auto dest: non_Package_instance_method_inheritance)
qed

lemma dynamic_to_static_overriding:
  assumes dyn_override: "G\<turnstile> new overrides old" and
           accmodi_old: "accmodi old \<noteq> Package" and
                    wf: "wf_prog G"
  shows "G\<turnstile> new overrides\<^sub>S old"  
proof - 
  from dyn_override accmodi_old
  show ?thesis (is "?Overrides new old")
  proof (induct rule: overridesR.induct)
    case (Direct new old)
    assume   new_declared: "G\<turnstile>Method new declared_in declclass new"
    assume eq_sig_new_old: "msig new = msig old"
    assume subcls_new_old: "G\<turnstile>declclass new \<prec>\<^sub>C declclass old"
    assume "G \<turnstile>Method old inheritable_in pid (declclass new)" and
           "accmodi old \<noteq> Package" and
           "\<not> is_static old" and
           "G\<turnstile>declclass new\<prec>\<^sub>C declclass old" and
           "G\<turnstile>Method old declared_in declclass old" 
    from this wf
    show "?Overrides new old"
    proof (cases rule: non_Package_instance_method_inheritance_cases)
      case Inheritance
      assume "G \<turnstile>Method old member_of declclass new"
      then have "G\<turnstile>mid (msig old) undeclared_in declclass new"
      proof cases
	case Immediate 
	with subcls_new_old wf show ?thesis 	
	  by (auto dest: subcls_irrefl)
      next
	case Inherited
	then show ?thesis
	  by (cases old) auto
      qed
      with eq_sig_new_old new_declared
      show ?thesis
	by (cases old,cases new) (auto dest!: declared_not_undeclared)
    next
      case (Overriding new') 
      assume stat_override_new': "G \<turnstile> new' overrides\<^sub>S old"
      then have "msig new' = msig old"
	by (auto dest: stat_overrides_commonD)
      with eq_sig_new_old have eq_sig_new_new': "msig new=msig new'"
	by simp
      assume "G \<turnstile>Method new' member_of declclass new"
      then show ?thesis
      proof (cases)
	case Immediate
	then have declC_new: "declclass new' = declclass new" 
	  by auto
	from Immediate 
	have "G\<turnstile>Method new' declared_in declclass new"
	  by (cases new') auto
	with new_declared eq_sig_new_new' declC_new 
	have "new=new'"
	  by (cases new, cases new') (auto dest: unique_declared_in) 
	with stat_override_new'
	show ?thesis
	  by simp
      next
	case Inherited
	then have "G\<turnstile>mid (msig new') undeclared_in declclass new"
	  by (cases new') (auto)
	with eq_sig_new_new' new_declared
	show ?thesis
	  by (cases new,cases new') (auto dest!: declared_not_undeclared)
      qed
    qed
  next
    case (Indirect inter new old)
    assume accmodi_old: "accmodi old \<noteq> Package"
    assume "accmodi old \<noteq> Package \<Longrightarrow> G \<turnstile> inter overrides\<^sub>S old"
    with accmodi_old 
    have stat_override_inter_old: "G \<turnstile> inter overrides\<^sub>S old"
      by blast
    moreover 
    assume hyp_inter: "accmodi inter \<noteq> Package \<Longrightarrow> G \<turnstile> new overrides\<^sub>S inter"
    moreover
    have "accmodi inter \<noteq> Package"
    proof -
      from stat_override_inter_old wf 
      have "accmodi old \<le> accmodi inter"
	by (auto dest: wf_prog_stat_overridesD)
      with stat_override_inter_old accmodi_old
      show ?thesis
	by (auto dest!: no_Private_stat_override
                 split: acc_modi.splits 
	         dest: acc_modi_le_Dests)
    qed
    ultimately show "?Overrides new old"
      by (blast intro: stat_overridesR.Indirect)
  qed
qed

lemma wf_prog_dyn_override_prop:
  assumes dyn_override: "G \<turnstile> new overrides old" and
                    wf: "wf_prog G"
  shows "accmodi old \<le> accmodi new"
proof (cases "accmodi old = Package")
  case True
  note old_Package = this
  show ?thesis
  proof (cases "accmodi old \<le> accmodi new")
    case True then show ?thesis .
  next
    case False
    with old_Package 
    have "accmodi new = Private"
      by (cases "accmodi new") (auto simp add: le_acc_def less_acc_def)
    with dyn_override 
    show ?thesis
      by (auto dest: overrides_commonD)
  qed    
next
  case False
  with dyn_override wf
  have "G \<turnstile> new overrides\<^sub>S old"
    by (blast intro: dynamic_to_static_overriding)
  with wf 
  show ?thesis
   by (blast dest: wf_prog_stat_overridesD)
qed 

lemma overrides_Package_old: 
  assumes dyn_override: "G \<turnstile> new overrides old" and 
           accmodi_new: "accmodi new = Package" and
                    wf: "wf_prog G "
  shows "accmodi old = Package"
proof (cases "accmodi old")
  case Private
  with dyn_override show ?thesis
    by (simp add: no_Private_override)
next
  case Package
  then show ?thesis .
next
  case Protected
  with dyn_override wf
  have "G \<turnstile> new overrides\<^sub>S old"
    by (auto intro: dynamic_to_static_overriding)
  with wf 
  have "accmodi old \<le> accmodi new"
    by (auto dest: wf_prog_stat_overridesD)
  with Protected accmodi_new
  show ?thesis
    by (simp add: less_acc_def le_acc_def)
next
  case Public
  with dyn_override wf
  have "G \<turnstile> new overrides\<^sub>S old"
    by (auto intro: dynamic_to_static_overriding)
  with wf 
  have "accmodi old \<le> accmodi new"
    by (auto dest: wf_prog_stat_overridesD)
  with Public accmodi_new
  show ?thesis
    by (simp add: less_acc_def le_acc_def)
qed

lemma dyn_override_Package:
  assumes dyn_override: "G \<turnstile> new overrides old" and
           accmodi_old: "accmodi old = Package" and 
           accmodi_new: "accmodi new = Package" and
                    wf: "wf_prog G"
  shows "pid (declclass old) = pid (declclass new)"
proof - 
  from dyn_override accmodi_old accmodi_new
  show ?thesis (is "?EqPid old new")
  proof (induct rule: overridesR.induct)
    case (Direct new old)
    assume "accmodi old = Package"
           "G \<turnstile>Method old inheritable_in pid (declclass new)"
    then show "pid (declclass old) =  pid (declclass new)"
      by (auto simp add: inheritable_in_def)
  next
    case (Indirect inter new old)
    assume accmodi_old: "accmodi old = Package" and
           accmodi_new: "accmodi new = Package" 
    assume "G \<turnstile> new overrides inter"
    with accmodi_new wf
    have "accmodi inter = Package"
      by  (auto intro: overrides_Package_old)
    with Indirect
    show "pid (declclass old) =  pid (declclass new)"
      by auto
  qed
qed

lemma dyn_override_Package_escape:
  assumes dyn_override: "G \<turnstile> new overrides old" and
           accmodi_old: "accmodi old = Package" and 
          outside_pack: "pid (declclass old) \<noteq> pid (declclass new)" and
                    wf: "wf_prog G"
  shows "\<exists> inter. G \<turnstile> new overrides inter \<and> G \<turnstile> inter overrides old \<and>
             pid (declclass old) = pid (declclass inter) \<and>
             Protected \<le> accmodi inter"
proof -
  from dyn_override accmodi_old outside_pack
  show ?thesis (is "?P new old")
  proof (induct rule: overridesR.induct)
    case (Direct new old)
    assume accmodi_old: "accmodi old = Package"
    assume outside_pack: "pid (declclass old) \<noteq> pid (declclass new)"
    assume "G \<turnstile>Method old inheritable_in pid (declclass new)"
    with accmodi_old 
    have "pid (declclass old) = pid (declclass new)"
      by (simp add: inheritable_in_def)
    with outside_pack 
    show "?P new old"
      by (contradiction)
  next
    case (Indirect inter new old)
    assume accmodi_old: "accmodi old = Package"
    assume outside_pack: "pid (declclass old) \<noteq> pid (declclass new)"
    assume override_new_inter: "G \<turnstile> new overrides inter"
    assume override_inter_old: "G \<turnstile> inter overrides old"
    assume hyp_new_inter: "\<lbrakk>accmodi inter = Package; 
                           pid (declclass inter) \<noteq> pid (declclass new)\<rbrakk>
                           \<Longrightarrow> ?P new inter"
    assume hyp_inter_old: "\<lbrakk>accmodi old = Package; 
                           pid (declclass old) \<noteq> pid (declclass inter)\<rbrakk>
                           \<Longrightarrow> ?P inter old"
    show "?P new old"
    proof (cases "pid (declclass old) = pid (declclass inter)")
      case True
      note same_pack_old_inter = this
      show ?thesis
      proof (cases "pid (declclass inter) = pid (declclass new)")
	case True
	with same_pack_old_inter outside_pack
	show ?thesis
	  by auto
      next
	case False
	note diff_pack_inter_new = this
	show ?thesis
	proof (cases "accmodi inter = Package")
	  case True
	  with diff_pack_inter_new hyp_new_inter  
	  obtain newinter where
	    over_new_newinter: "G \<turnstile> new overrides newinter" and
            over_newinter_inter: "G \<turnstile> newinter overrides inter" and 
            eq_pid: "pid (declclass inter) = pid (declclass newinter)" and
            accmodi_newinter: "Protected \<le> accmodi newinter"
	    by auto
	  from over_newinter_inter override_inter_old
	  have "G\<turnstile>newinter overrides old"
	    by (rule overridesR.Indirect)
	  moreover
	  from eq_pid same_pack_old_inter 
	  have "pid (declclass old) = pid (declclass newinter)"
	    by simp
	  moreover
	  note over_new_newinter accmodi_newinter
	  ultimately show ?thesis
	    by blast
	next
	  case False
	  with override_new_inter
	  have "Protected \<le> accmodi inter"
	    by (cases "accmodi inter") (auto dest: no_Private_override)
	  with override_new_inter override_inter_old same_pack_old_inter
	  show ?thesis
	    by blast
	qed
      qed
    next
      case False
      with accmodi_old hyp_inter_old
      obtain newinter where
	over_inter_newinter: "G \<turnstile> inter overrides newinter" and
          over_newinter_old: "G \<turnstile> newinter overrides old" and 
                eq_pid: "pid (declclass old) = pid (declclass newinter)" and
	accmodi_newinter: "Protected \<le> accmodi newinter"
	by auto
      from override_new_inter over_inter_newinter 
      have "G \<turnstile> new overrides newinter"
	by (rule overridesR.Indirect)
      with eq_pid over_newinter_old accmodi_newinter
      show ?thesis
	by blast
    qed
  qed
qed

lemma declclass_widen[rule_format]: 
 "wf_prog G 
 \<longrightarrow> (\<forall>c m. class G C = Some c \<longrightarrow> methd G C sig = Some m 
 \<longrightarrow> G\<turnstile>C \<preceq>\<^sub>C declclass m)" (is "?P G C")
proof (rule class_rec.induct,intro allI impI)
  fix G C c m
  assume Hyp: "\<forall>c. C \<noteq> Object \<and> ws_prog G \<and> class G C = Some c 
               \<longrightarrow> ?P G (super c)"
  assume wf: "wf_prog G" and cls_C: "class G C = Some c" and
         m:  "methd G C sig = Some m"
  show "G\<turnstile>C\<preceq>\<^sub>C declclass m" 
  proof (cases "C=Object")
    case True 
    with wf m show ?thesis by (simp add: methd_Object_SomeD)
  next
    let ?filter="filter_tab (\<lambda>sig m. G\<turnstile>C inherits method sig m)"
    let ?table = "table_of (map (\<lambda>(s, m). (s, C, m)) (methods c))"
    case False 
    with cls_C wf m
    have methd_C: "(?filter (methd G (super c)) ++ ?table) sig = Some m "
      by (simp add: methd_rec)
    show ?thesis
    proof (cases "?table sig")
      case None
      from this methd_C have "?filter (methd G (super c)) sig = Some m"
	by simp
      moreover
      from wf cls_C False obtain sup where "class G (super c) = Some sup"
	by (blast dest: wf_prog_cdecl wf_cdecl_supD is_acc_class_is_class)
      moreover note wf False cls_C  
      ultimately have "G\<turnstile>super c \<preceq>\<^sub>C declclass m"  
	by (auto intro: Hyp [rule_format])
      moreover from cls_C False have  "G\<turnstile>C \<prec>\<^sub>C\<^sub>1 super c" by (rule subcls1I)
      ultimately show ?thesis by - (rule rtrancl_into_rtrancl2)
    next
      case Some
      from this wf False cls_C methd_C show ?thesis by auto
    qed
  qed
qed

lemma declclass_methd_Object: 
 "\<lbrakk>wf_prog G; methd G Object sig = Some m\<rbrakk> \<Longrightarrow> declclass m = Object"
by auto

lemma methd_declaredD: 
 "\<lbrakk>wf_prog G; is_class G C;methd G C sig = Some m\<rbrakk> 
  \<Longrightarrow> G\<turnstile>(mdecl (sig,mthd m)) declared_in (declclass m)"
proof -
  assume    wf: "wf_prog G"
  then have ws: "ws_prog G" ..
  assume  clsC: "is_class G C"
  from clsC ws 
  show "methd G C sig = Some m 
        \<Longrightarrow> G\<turnstile>(mdecl (sig,mthd m)) declared_in (declclass m)"
    (is "PROP ?P C") 
  proof (induct ?P C rule: ws_class_induct')
    case Object
    assume "methd G Object sig = Some m" 
    with wf show ?thesis
      by - (rule method_declared_inI, auto) 
  next
    case Subcls
    fix C c
    assume clsC: "class G C = Some c"
    and       m: "methd G C sig = Some m"
    and     hyp: "methd G (super c) sig = Some m \<Longrightarrow> ?thesis" 
    let ?newMethods = "table_of (map (\<lambda>(s, m). (s, C, m)) (methods c))"
    show ?thesis
    proof (cases "?newMethods sig")
      case None
      from None ws clsC m hyp 
      show ?thesis by (auto intro: method_declared_inI simp add: methd_rec)
    next
      case Some
      from Some ws clsC m 
      show ?thesis by (auto intro: method_declared_inI simp add: methd_rec) 
    qed
  qed
qed

lemma methd_rec_Some_cases [consumes 4, case_names NewMethod InheritedMethod]:
  assumes methd_C: "methd G C sig = Some m" and
               ws: "ws_prog G" and
             clsC: "class G C = Some c" and
        neq_C_Obj: "C\<noteq>Object"
  shows
"\<lbrakk>table_of (map (\<lambda>(s, m). (s, C, m)) (methods c)) sig = Some m \<Longrightarrow> P;
  \<lbrakk>G\<turnstile>C inherits (method sig m); methd G (super c) sig = Some m\<rbrakk> \<Longrightarrow> P 
 \<rbrakk> \<Longrightarrow> P"
proof -
  let ?inherited   = "filter_tab (\<lambda>sig m. G\<turnstile>C inherits method sig m) 
                              (methd G (super c))"
  let ?new = "table_of (map (\<lambda>(s, m). (s, C, m)) (methods c))"
  from ws clsC neq_C_Obj methd_C 
  have methd_unfold: "(?inherited ++ ?new) sig = Some m"
    by (simp add: methd_rec)
  assume NewMethod: "?new sig = Some m \<Longrightarrow> P"
  assume InheritedMethod: "\<lbrakk>G\<turnstile>C inherits (method sig m); 
                            methd G (super c) sig = Some m\<rbrakk> \<Longrightarrow> P"
  show P
  proof (cases "?new sig")
    case None
    with methd_unfold have "?inherited sig = Some m"
      by (auto)
    with InheritedMethod show P by blast
  next
    case Some
    with methd_unfold have "?new sig = Some m"
      by auto
    with NewMethod show P by blast
  qed
qed

  
lemma methd_member_of:
  assumes wf: "wf_prog G"
  shows
    "\<lbrakk>is_class G C; methd G C sig = Some m\<rbrakk> \<Longrightarrow> G\<turnstile>Methd sig m member_of C" 
  (is "?Class C \<Longrightarrow> ?Method C \<Longrightarrow> ?MemberOf C") 
proof -
  from wf   have   ws: "ws_prog G" ..
  assume defC: "is_class G C"
  from defC ws 
  show "?Class C \<Longrightarrow> ?Method C \<Longrightarrow> ?MemberOf C"
  proof (induct rule: ws_class_induct')  
    case Object
    with wf have declC: "Object = declclass m"
      by (simp add: declclass_methd_Object)
    from Object wf have "G\<turnstile>Methd sig m declared_in Object"
      by (auto intro: methd_declaredD simp add: declC)
    with declC 
    show "?MemberOf Object"
      by (auto intro!: members.Immediate
                  simp del: methd_Object)
  next
    case (Subcls C c)
    assume  clsC: "class G C = Some c" and
       neq_C_Obj: "C \<noteq> Object"  
    assume methd: "?Method C"
    from methd ws clsC neq_C_Obj
    show "?MemberOf C"
    proof (cases rule: methd_rec_Some_cases)
      case NewMethod
      with clsC show ?thesis
	by (auto dest: method_declared_inI intro!: members.Immediate)
    next
      case InheritedMethod
      then show "?thesis"
	by (blast dest: inherits_member)
    qed
  qed
qed

lemma current_methd: 
      "\<lbrakk>table_of (methods c) sig = Some new;
        ws_prog G; class G C = Some c; C \<noteq> Object; 
        methd G (super c) sig = Some old\<rbrakk> 
    \<Longrightarrow> methd G C sig = Some (C,new)"
by (auto simp add: methd_rec
            intro: filter_tab_SomeI map_add_find_right table_of_map_SomeI)

lemma wf_prog_staticD:
  assumes     wf: "wf_prog G" and
            clsC: "class G C = Some c" and
       neq_C_Obj: "C \<noteq> Object" and 
             old: "methd G (super c) sig = Some old" and 
     accmodi_old: "Protected \<le> accmodi old" and
             new: "table_of (methods c) sig = Some new"
  shows "is_static new = is_static old"
proof -
  from clsC wf 
  have wf_cdecl: "wf_cdecl G (C,c)" by (rule wf_prog_cdecl)
  from wf clsC neq_C_Obj
  have is_cls_super: "is_class G (super c)" 
    by (blast dest: wf_prog_acc_superD is_acc_classD)
  from wf is_cls_super old 
  have old_member_of: "G\<turnstile>Methd sig old member_of (super c)"  
    by (rule methd_member_of)
  from old wf is_cls_super 
  have old_declared: "G\<turnstile>Methd sig old declared_in (declclass old)"
    by (auto dest: methd_declared_in_declclass)
  from new clsC 
  have new_declared: "G\<turnstile>Methd sig (C,new) declared_in C"
    by (auto intro: method_declared_inI)
  note trancl_rtrancl_tranc = trancl_rtrancl_trancl [trans] (* ### in Basis *)
  from clsC neq_C_Obj
  have subcls1_C_super: "G\<turnstile>C \<prec>\<^sub>C\<^sub>1 super c"
    by (rule subcls1I)
  then have "G\<turnstile>C \<prec>\<^sub>C super c" ..
  also from old wf is_cls_super
  have "G\<turnstile>super c \<preceq>\<^sub>C (declclass old)" by (auto dest: methd_declC)
  finally have subcls_C_old:  "G\<turnstile>C \<prec>\<^sub>C (declclass old)" .
  from accmodi_old 
  have inheritable: "G\<turnstile>Methd sig old inheritable_in pid C"
    by (auto simp add: inheritable_in_def
                 dest: acc_modi_le_Dests)
  show ?thesis
  proof (cases "is_static new")
    case True
    with subcls_C_old new_declared old_declared inheritable
    have "G,sig\<turnstile>(C,new) hides old"
      by (auto intro: hidesI)
    with True wf_cdecl neq_C_Obj new 
    show ?thesis
      by (auto dest: wf_cdecl_hides_SomeD)
  next
    case False
    with subcls_C_old new_declared old_declared inheritable subcls1_C_super
         old_member_of
    have "G,sig\<turnstile>(C,new) overrides\<^sub>S old"
      by (auto intro: stat_overridesR.Direct)
    with False wf_cdecl neq_C_Obj new 
    show ?thesis
      by (auto dest: wf_cdecl_overrides_SomeD)
  qed
qed

lemma inheritable_instance_methd: 
  assumes subclseq_C_D: "G\<turnstile>C \<preceq>\<^sub>C D" and
              is_cls_D: "is_class G D" and
                    wf: "wf_prog G" and 
                   old: "methd G D sig = Some old" and
           accmodi_old: "Protected \<le> accmodi old" and  
        not_static_old: "\<not> is_static old"
  shows
  "\<exists>new. methd G C sig = Some new \<and>
         (new = old \<or> G,sig\<turnstile>new overrides\<^sub>S old)"
 (is "(\<exists>new. (?Constraint C new old))")
proof -
  from subclseq_C_D is_cls_D 
  have is_cls_C: "is_class G C" by (rule subcls_is_class2) 
  from wf 
  have ws: "ws_prog G" ..
  from is_cls_C ws subclseq_C_D 
  show "\<exists>new. ?Constraint C new old"
  proof (induct rule: ws_class_induct')
    case (Object co)
    then have eq_D_Obj: "D=Object" by auto
    with old 
    have "?Constraint Object old old"
      by auto
    with eq_D_Obj 
    show "\<exists> new. ?Constraint Object new old" by auto
  next
    case (Subcls C c)
    assume hyp: "G\<turnstile>super c\<preceq>\<^sub>C D \<Longrightarrow> \<exists>new. ?Constraint (super c) new old"
    assume clsC: "class G C = Some c"
    assume neq_C_Obj: "C\<noteq>Object"
    from clsC wf 
    have wf_cdecl: "wf_cdecl G (C,c)" 
      by (rule wf_prog_cdecl)
    from ws clsC neq_C_Obj
    have is_cls_super: "is_class G (super c)"
      by (auto dest: ws_prog_cdeclD)
    from clsC wf neq_C_Obj 
    have superAccessible: "G\<turnstile>(Class (super c)) accessible_in (pid C)" and
	 subcls1_C_super: "G\<turnstile>C \<prec>\<^sub>C\<^sub>1 super c"
      by (auto dest: wf_prog_cdecl wf_cdecl_supD is_acc_classD
              intro: subcls1I)
    show "\<exists>new. ?Constraint C new old"
    proof (cases "G\<turnstile>super c\<preceq>\<^sub>C D")
      case False
      from False Subcls 
      have eq_C_D: "C=D"
	by (auto dest: subclseq_superD)
      with old 
      have "?Constraint C old old"
	by auto
      with eq_C_D 
      show "\<exists> new. ?Constraint C new old" by auto
    next
      case True
      with hyp obtain super_method
	where super: "?Constraint (super c) super_method old" by blast
      from super not_static_old
      have not_static_super: "\<not> is_static super_method"
	by (auto dest!: stat_overrides_commonD)
      from super old wf accmodi_old
      have accmodi_super_method: "Protected \<le> accmodi super_method"
	by (auto dest!: wf_prog_stat_overridesD
                 intro: order_trans)
      from super accmodi_old wf
      have inheritable: "G\<turnstile>Methd sig super_method inheritable_in (pid C)"
	by (auto dest!: wf_prog_stat_overridesD
                        acc_modi_le_Dests
              simp add: inheritable_in_def)	           
      from super wf is_cls_super
      have member: "G\<turnstile>Methd sig super_method member_of (super c)"
	by (auto intro: methd_member_of) 
      from member
      have decl_super_method:
        "G\<turnstile>Methd sig super_method declared_in (declclass super_method)"
	by (auto dest: member_of_declC)
      from super subcls1_C_super ws is_cls_super 
      have subcls_C_super: "G\<turnstile>C \<prec>\<^sub>C (declclass super_method)"
	by (auto intro: rtrancl_into_trancl2 dest: methd_declC) 
      show "\<exists> new. ?Constraint C new old"
      proof (cases "methd G C sig")
	case None
	have "methd G (super c) sig = None"
	proof -
	  from clsC ws None 
	  have no_new: "table_of (methods c) sig = None" 
	    by (auto simp add: methd_rec)
	  with clsC 
	  have undeclared: "G\<turnstile>mid sig undeclared_in C"
	    by (auto simp add: undeclared_in_def cdeclaredmethd_def)
	  with inheritable member superAccessible subcls1_C_super
	  have inherits: "G\<turnstile>C inherits (method sig super_method)"
	    by (auto simp add: inherits_def)
	  with clsC ws no_new super neq_C_Obj
	  have "methd G C sig = Some super_method"
	    by (auto simp add: methd_rec map_add_def intro: filter_tab_SomeI)
          with None show ?thesis
	    by simp
	qed
	with super show ?thesis by auto
      next
	case (Some new)
	from this ws clsC neq_C_Obj
	show ?thesis
	proof (cases rule: methd_rec_Some_cases)
	  case InheritedMethod
	  with super Some show ?thesis 
	    by auto
	next
	  case NewMethod
	  assume new: "table_of (map (\<lambda>(s, m). (s, C, m)) (methods c)) sig 
                       = Some new"
	  from new 
	  have declcls_new: "declclass new = C" 
	    by auto
	  from wf clsC neq_C_Obj super new not_static_super accmodi_super_method
	  have not_static_new: "\<not> is_static new" 
	    by (auto dest: wf_prog_staticD) 
	  from clsC new
	  have decl_new: "G\<turnstile>Methd sig new declared_in C"
	    by (auto simp add: declared_in_def cdeclaredmethd_def)
	  from not_static_new decl_new decl_super_method
	       member subcls1_C_super inheritable declcls_new subcls_C_super 
	  have "G,sig\<turnstile> new overrides\<^sub>S super_method"
	    by (auto intro: stat_overridesR.Direct) 
	  with super Some
	  show ?thesis
	    by (auto intro: stat_overridesR.Indirect)
	qed
      qed
    qed
  qed
qed

lemma inheritable_instance_methd_cases [consumes 6
                                       , case_names Inheritance Overriding]: 
  assumes subclseq_C_D: "G\<turnstile>C \<preceq>\<^sub>C D" and
              is_cls_D: "is_class G D" and
                    wf: "wf_prog G" and 
                   old: "methd G D sig = Some old" and
           accmodi_old: "Protected \<le> accmodi old" and  
        not_static_old: "\<not> is_static old" and
           inheritance:  "methd G C sig = Some old \<Longrightarrow> P" and
            overriding:  "\<And> new. \<lbrakk>methd G C sig = Some new;
                                   G,sig\<turnstile>new overrides\<^sub>S old\<rbrakk> \<Longrightarrow> P"
        
  shows P
proof -
from subclseq_C_D is_cls_D wf old accmodi_old not_static_old 
show ?thesis
  by (auto dest: inheritable_instance_methd intro: inheritance overriding)
qed

lemma inheritable_instance_methd_props: 
  assumes subclseq_C_D: "G\<turnstile>C \<preceq>\<^sub>C D" and
              is_cls_D: "is_class G D" and
                    wf: "wf_prog G" and 
                   old: "methd G D sig = Some old" and
           accmodi_old: "Protected \<le> accmodi old" and  
        not_static_old: "\<not> is_static old"
  shows
  "\<exists>new. methd G C sig = Some new \<and>
          \<not> is_static new \<and> G\<turnstile>resTy new\<preceq>resTy old \<and> accmodi old \<le>accmodi new"
 (is "(\<exists>new. (?Constraint C new old))")
proof -
  from subclseq_C_D is_cls_D wf old accmodi_old not_static_old 
  show ?thesis
  proof (cases rule: inheritable_instance_methd_cases)
    case Inheritance
    with not_static_old accmodi_old show ?thesis by auto
  next
    case (Overriding new)
    then have "\<not> is_static new" by (auto dest: stat_overrides_commonD)
    with Overriding not_static_old accmodi_old wf 
    show ?thesis 
      by (auto dest!: wf_prog_stat_overridesD
               intro: order_trans)
  qed
qed
 	      
(* local lemma *)
ML {* bind_thm("bexI'",permute_prems 0 1 bexI) *}
ML {* bind_thm("ballE'",permute_prems 1 1 ballE) *}
lemma subint_widen_imethds: 
 "\<lbrakk>G\<turnstile>I\<preceq>I J; wf_prog G; is_iface G J; jm \<in> imethds G J sig\<rbrakk> \<Longrightarrow>   
  \<exists> im \<in> imethds G I sig. is_static im = is_static jm \<and> 
                          accmodi im = accmodi jm \<and>
                          G\<turnstile>resTy im\<preceq>resTy jm"
proof -
  assume irel: "G\<turnstile>I\<preceq>I J" and
           wf: "wf_prog G" and
     is_iface: "is_iface G J"
  from irel show "jm \<in> imethds G J sig \<Longrightarrow> ?thesis" 
               (is "PROP ?P I" is "PROP ?Prem J \<Longrightarrow> ?Concl I")
  proof (induct ?P I rule: converse_rtrancl_induct) 
    case Id
    assume "jm \<in> imethds G J sig"
    then show "?Concl J" by  (blast elim: bexI')
  next
    case Step
    fix I SI
    assume subint1_I_SI: "G\<turnstile>I \<prec>I1 SI" and 
            subint_SI_J: "G\<turnstile>SI \<preceq>I J" and
                    hyp: "PROP ?P SI" and
                     jm: "jm \<in> imethds G J sig"
    from subint1_I_SI 
    obtain i where
      ifI: "iface G I = Some i" and
       SI: "SI \<in> set (isuperIfs i)"
      by (blast dest: subint1D)

    let ?newMethods 
          = "(o2s \<circ> table_of (map (\<lambda>(sig, mh). (sig, I, mh)) (imethods i)))"
    show "?Concl I"
    proof (cases "?newMethods sig = {}")
      case True
      with ifI SI hyp wf jm 
      show "?thesis" 
	by (auto simp add: imethds_rec) 
    next
      case False
      from ifI wf False
      have imethds: "imethds G I sig = ?newMethods sig"
	by (simp add: imethds_rec)
      from False
      obtain im where
        imdef: "im \<in> ?newMethods sig" 
	by (blast)
      with imethds 
      have im: "im \<in> imethds G I sig"
	by (blast)
      with im wf ifI 
      obtain
	 imStatic: "\<not> is_static im" and
         imPublic: "accmodi im = Public"
	by (auto dest!: imethds_wf_mhead)	
      from ifI wf 
      have wf_I: "wf_idecl G (I,i)" 
	by (rule wf_prog_idecl)
      with SI wf  
      obtain si where
	 ifSI: "iface G SI = Some si" and
	wf_SI: "wf_idecl G (SI,si)" 
	by (auto dest!: wf_idecl_supD is_acc_ifaceD
                  dest: wf_prog_idecl)
      from jm hyp 
      obtain sim::"qtname \<times> mhead"  where
                      sim: "sim \<in> imethds G SI sig" and
         eq_static_sim_jm: "is_static sim = is_static jm" and 
         eq_access_sim_jm: "accmodi sim = accmodi jm" and 
        resTy_widen_sim_jm: "G\<turnstile>resTy sim\<preceq>resTy jm"
	by blast
      with wf_I SI imdef sim 
      have "G\<turnstile>resTy im\<preceq>resTy sim"   
	by (auto dest!: wf_idecl_hidings hidings_entailsD)
      with wf resTy_widen_sim_jm 
      have resTy_widen_im_jm: "G\<turnstile>resTy im\<preceq>resTy jm"
	by (blast intro: widen_trans)
      from sim wf ifSI  
      obtain
	simStatic: "\<not> is_static sim" and
        simPublic: "accmodi sim = Public"
	by (auto dest!: imethds_wf_mhead)
      from im 
           imStatic simStatic eq_static_sim_jm
           imPublic simPublic eq_access_sim_jm
           resTy_widen_im_jm
      show ?thesis 
	by auto 
    qed
  qed
qed
     
(* Tactical version *)
(* 
lemma subint_widen_imethds: "\<lbrakk>G\<turnstile>I\<preceq>I J; wf_prog G; is_iface G J\<rbrakk> \<Longrightarrow>  
  \<forall> jm \<in> imethds G J sig.  
  \<exists> im \<in> imethds G I sig. static (mthd im)=static (mthd jm) \<and> 
                          access (mthd im)= access (mthd jm) \<and>
                          G\<turnstile>resTy (mthd im)\<preceq>resTy (mthd jm)"
apply (erule converse_rtrancl_induct)
apply  (clarsimp elim!: bexI')
apply (frule subint1D)
apply clarify
apply (erule ballE')
apply  fast
apply (erule_tac V = "?x \<in> imethds G J sig" in thin_rl)
apply clarsimp
apply (subst imethds_rec, assumption, erule wf_ws_prog)
apply (unfold overrides_t_def)
apply (drule (1) wf_prog_idecl)
apply (frule (3) imethds_wf_mhead [OF _ _ wf_idecl_supD [THEN conjunct1 
                                       [THEN is_acc_ifaceD [THEN conjunct1]]]])
apply (case_tac "(o2s \<circ> table_of (map (\<lambda>(s, mh). (s, y, mh)) (imethods i)))
                  sig ={}")
apply   force

apply   (simp only:)
apply   (simp)
apply   clarify
apply   (frule wf_idecl_hidings [THEN hidings_entailsD])
apply     blast
apply     blast
apply   (rule bexI')
apply     simp
apply     (drule table_of_map_SomeI [of _ "sig"])
apply     simp

apply     (frule wf_idecl_mhead [of _ _ _ "sig"])
apply       (rule table_of_Some_in_set)
apply       assumption
apply     auto
done
*)
    

(* local lemma *)
lemma implmt1_methd: 
 "\<And>sig. \<lbrakk>G\<turnstile>C\<leadsto>1I; wf_prog G; im \<in> imethds G I sig\<rbrakk> \<Longrightarrow>  
  \<exists>cm \<in>methd G C sig: \<not> is_static cm \<and> \<not> is_static im \<and> 
                       G\<turnstile>resTy cm\<preceq>resTy im \<and>
                       accmodi im = Public \<and> accmodi cm = Public"
apply (drule implmt1D)
apply clarify
apply (drule (2) wf_prog_cdecl [THEN wf_cdecl_impD])
apply (frule (1) imethds_wf_mhead)
apply  (simp add: is_acc_iface_def)
apply (force)
done


(* local lemma *)
lemma implmt_methd [rule_format (no_asm)]: 
"\<lbrakk>wf_prog G; G\<turnstile>C\<leadsto>I\<rbrakk> \<Longrightarrow> is_iface G I \<longrightarrow>  
 (\<forall> im    \<in>imethds G I   sig.  
  \<exists> cm\<in>methd G C sig: \<not>is_static cm \<and> \<not> is_static im \<and> 
                      G\<turnstile>resTy cm\<preceq>resTy im \<and>
                      accmodi im = Public \<and> accmodi cm = Public)"
apply (frule implmt_is_class)
apply (erule implmt.induct)
apply   safe
apply   (drule (2) implmt1_methd)
apply   fast
apply  (drule (1) subint_widen_imethds)
apply   simp
apply   assumption
apply  clarify
apply  (drule (2) implmt1_methd)
apply  (force)
apply (frule subcls1D)
apply (drule (1) bspec)
apply clarify
apply (drule (3) r_into_rtrancl [THEN inheritable_instance_methd_props, 
                                 OF _ implmt_is_class])
apply auto 
done

lemma mheadsD [rule_format (no_asm)]: 
"emh \<in> mheads G S t sig \<longrightarrow> wf_prog G \<longrightarrow>
 (\<exists>C D m. t = ClassT C \<and> declrefT emh = ClassT D \<and> 
          accmethd G S C sig = Some m \<and>
          (declclass m = D) \<and> mhead (mthd m) = (mhd emh)) \<or>
 (\<exists>I. t = IfaceT I \<and> ((\<exists>im. im  \<in> accimethds G (pid S) I sig \<and> 
          mthd im = mhd emh) \<or> 
  (\<exists>m. G\<turnstile>Iface I accessible_in (pid S) \<and> accmethd G S Object sig = Some m \<and> 
       accmodi m \<noteq> Private \<and> 
       declrefT emh = ClassT Object \<and> mhead (mthd m) = mhd emh))) \<or>
 (\<exists>T m. t = ArrayT T \<and> G\<turnstile>Array T accessible_in (pid S) \<and>
        accmethd G S Object sig = Some m \<and> accmodi m \<noteq> Private \<and> 
        declrefT emh = ClassT Object \<and> mhead (mthd m) = mhd emh)"
apply (rule_tac "ref_ty1"="t" in ref_ty_ty.induct [THEN conjunct1])
apply auto
apply (auto simp add: cmheads_def accObjectmheads_def Objectmheads_def)
apply (auto  dest!: accmethd_SomeD)
done

lemma mheads_cases [consumes 2, case_names Class_methd 
                    Iface_methd Iface_Object_methd Array_Object_methd]: 
"\<lbrakk>emh \<in> mheads G S t sig; wf_prog G;
 \<And> C D m. \<lbrakk>t = ClassT C;declrefT emh = ClassT D; accmethd G S C sig = Some m;
           (declclass m = D); mhead (mthd m) = (mhd emh)\<rbrakk> \<Longrightarrow> P emh; 
 \<And> I im. \<lbrakk>t = IfaceT I; im  \<in> accimethds G (pid S) I sig; mthd im = mhd emh\<rbrakk>
          \<Longrightarrow> P emh;
 \<And> I m. \<lbrakk>t = IfaceT I; G\<turnstile>Iface I accessible_in (pid S);
          accmethd G S Object sig = Some m; accmodi m \<noteq> Private;
         declrefT emh = ClassT Object; mhead (mthd m) = mhd emh\<rbrakk> \<Longrightarrow> P emh;
 \<And> T m. \<lbrakk>t = ArrayT T;G\<turnstile>Array T accessible_in (pid S);
          accmethd G S Object sig = Some m; accmodi m \<noteq> Private; 
          declrefT emh = ClassT Object; mhead (mthd m) = mhd emh\<rbrakk> \<Longrightarrow>  P emh 
\<rbrakk> \<Longrightarrow> P emh"
by (blast dest!: mheadsD)

lemma declclassD[rule_format]:
 "\<lbrakk>wf_prog G;class G C = Some c; methd G C sig = Some m; 
   class G (declclass m) = Some d\<rbrakk>
  \<Longrightarrow> table_of (methods d) sig  = Some (mthd m)"
proof -
  assume    wf: "wf_prog G"
  then have ws: "ws_prog G" ..
  assume  clsC: "class G C = Some c"
  from clsC ws 
  show "\<And> m d. \<lbrakk>methd G C sig = Some m; class G (declclass m) = Some d\<rbrakk>
        \<Longrightarrow> table_of (methods d) sig  = Some (mthd m)" 
         (is "PROP ?P C") 
  proof (induct ?P C rule: ws_class_induct)
    case Object
    fix m d
    assume "methd G Object sig = Some m" 
           "class G (declclass m) = Some d"
    with wf show "?thesis m d" by auto
  next
    case Subcls
    fix C c m d
    assume hyp: "PROP ?P (super c)"
    and      m: "methd G C sig = Some m"
    and  declC: "class G (declclass m) = Some d"
    and   clsC: "class G C = Some c"
    and   nObj: "C \<noteq> Object"
    let ?newMethods = "table_of (map (\<lambda>(s, m). (s, C, m)) (methods c)) sig"
    show "?thesis m d" 
    proof (cases "?newMethods")
      case None
      from None clsC nObj ws m declC hyp  
      show "?thesis" by (auto simp add: methd_rec)
    next
      case Some
      from Some clsC nObj ws m declC hyp  
      show "?thesis" 
	by (auto simp add: methd_rec
                     dest: wf_prog_cdecl wf_cdecl_supD is_acc_class_is_class)
    qed
  qed
qed

(* Tactical version *)
(*
lemma declclassD[rule_format]:
 "wf_prog G \<longrightarrow>  
 (\<forall> c d m. class G C = Some c \<longrightarrow> methd G C sig = Some m \<longrightarrow> 
  class G (declclass m) = Some d
 \<longrightarrow> table_of (methods d) sig  = Some (mthd m))"
apply (rule class_rec.induct)
apply (rule impI)
apply (rule allI)+
apply (rule impI)
apply (case_tac "C=Object")
apply   (force simp add: methd_rec)

apply   (subst methd_rec)
apply     (blast dest: wf_ws_prog)+
apply   (case_tac "table_of (map (\<lambda>(s, m). (s, C, m)) (methods c)) sig")
apply     (auto dest: wf_prog_cdecl wf_cdecl_supD is_acc_class_is_class)
done
*)

lemma dynmethd_Object:
  assumes statM: "methd G Object sig = Some statM" and
        private: "accmodi statM = Private" and 
       is_cls_C: "is_class G C" and
             wf: "wf_prog G"
  shows "dynmethd G Object C sig = Some statM"
proof -
  from is_cls_C wf 
  have subclseq: "G\<turnstile>C \<preceq>\<^sub>C Object" 
    by (auto intro: subcls_ObjectI)
  from wf have ws: "ws_prog G" 
    by simp
  from wf 
  have is_cls_Obj: "is_class G Object" 
    by simp
  from statM subclseq is_cls_Obj ws private
  show ?thesis
  proof (cases rule: dynmethd_cases)
    case Static then show ?thesis .
  next
    case Overrides 
    with private show ?thesis 
      by (auto dest: no_Private_override)
  qed
qed

lemma wf_imethds_hiding_objmethdsD: 
  assumes     old: "methd G Object sig = Some old" and
          is_if_I: "is_iface G I" and
               wf: "wf_prog G" and    
      not_private: "accmodi old \<noteq> Private" and
              new: "new \<in> imethds G I sig" 
  shows "G\<turnstile>resTy new\<preceq>resTy old \<and> is_static new = is_static old" (is "?P new")
proof -
  from wf have ws: "ws_prog G" by simp
  {
    fix I i new
    assume ifI: "iface G I = Some i"
    assume new: "table_of (imethods i) sig = Some new" 
    from ifI new not_private wf old  
    have "?P (I,new)"
      by (auto dest!: wf_prog_idecl wf_idecl_hiding cond_hiding_entailsD
            simp del: methd_Object)
  } note hyp_newmethod = this  
  from is_if_I ws new 
  show ?thesis
  proof (induct rule: ws_interface_induct)
    case (Step I i)
    assume ifI: "iface G I = Some i" 
    assume new: "new \<in> imethds G I sig" 
    from Step
    have hyp: "\<forall> J \<in> set (isuperIfs i). (new \<in> imethds G J sig \<longrightarrow> ?P new)"
      by auto 
    from new ifI ws
    show "?P new"
    proof (cases rule: imethds_cases)
      case NewMethod
      with ifI hyp_newmethod
      show ?thesis
	by auto
    next
      case (InheritedMethod J)
      assume "J \<in> set (isuperIfs i)" 
             "new \<in> imethds G J sig"
      with hyp 
      show "?thesis"
	by auto
    qed
  qed
qed

text {*
Which dynamic classes are valid to look up a member of a distinct static type?
We have to distinct class members (named static members in Java) 
from instance members. Class members are global to all Objects of a class,
instance members are local to a single Object instance. If a member is
equipped with the static modifier it is a class member, else it is an 
instance member.
The following table gives an overview of the current framework. We assume
to have a reference with static type statT and a dynamic class dynC. Between
both of these types the widening relation holds 
@{term "G\<turnstile>Class dynC\<preceq> statT"}. Unfortunately this ordinary widening relation 
isn't enough to describe the valid lookup classes, since we must cope the
special cases of arrays and interfaces,too. If we statically expect an array or
inteface we may lookup a field or a method in Object which isn't covered in 
the widening relation.

statT      field         instance method       static (class) method
------------------------------------------------------------------------
 NullT      /                  /                   /
 Iface      /                dynC                Object
 Class    dynC               dynC                 dynC
 Array      /                Object              Object

In most cases we con lookup the member in the dynamic class. But as an
interface can't declare new static methods, nor an array can define new
methods at all, we have to lookup methods in the base class Object.

The limitation to classes in the field column is artificial  and comes out
of the typing rule for the field access (see rule @{text "FVar"} in the 
welltyping relation @{term "wt"} in theory WellType). 
I stems out of the fact, that Object
indeed has no non private fields. So interfaces and arrays can actually
have no fields at all and a field access would be senseless. (In Java
interfaces are allowed to declare new fields but in current Bali not!).
So there is no principal reason why we should not allow Objects to declare
non private fields. Then we would get the following column:
       
 statT    field
----------------- 
 NullT      /  
 Iface    Object 
 Class    dynC 
 Array    Object
*}
consts valid_lookup_cls:: "prog \<Rightarrow> ref_ty \<Rightarrow> qtname \<Rightarrow> bool \<Rightarrow> bool"
                        ("_,_ \<turnstile> _ valid'_lookup'_cls'_for _" [61,61,61,61] 60)
primrec
"G,NullT    \<turnstile> dynC valid_lookup_cls_for static_membr = False"
"G,IfaceT I \<turnstile> dynC valid_lookup_cls_for static_membr 
              = (if static_membr 
                    then dynC=Object 
                    else G\<turnstile>Class dynC\<preceq> Iface I)"
"G,ClassT C \<turnstile> dynC valid_lookup_cls_for static_membr = G\<turnstile>Class dynC\<preceq> Class C"
"G,ArrayT T \<turnstile> dynC valid_lookup_cls_for static_membr = (dynC=Object)"

lemma valid_lookup_cls_is_class:
  assumes dynC: "G,statT \<turnstile> dynC valid_lookup_cls_for static_membr" and
      ty_statT: "isrtype G statT" and
            wf: "wf_prog G"
  shows "is_class G dynC"
proof (cases statT)
  case NullT
  with dynC ty_statT show ?thesis
    by (auto dest: widen_NT2)
next
  case (IfaceT I)
  with dynC wf show ?thesis
    by (auto dest: implmt_is_class)
next
  case (ClassT C)
  with dynC ty_statT show ?thesis
    by (auto dest: subcls_is_class2)
next
  case (ArrayT T)
  with dynC wf show ?thesis
    by (auto)
qed

declare split_paired_All [simp del] split_paired_Ex [simp del]
ML_setup {*
simpset_ref() := simpset() delloop "split_all_tac";
claset_ref () := claset () delSWrapper "split_all_tac"
*}
lemma dynamic_mheadsD:   
"\<lbrakk>emh \<in> mheads G S statT sig;    
  G,statT \<turnstile> dynC valid_lookup_cls_for (is_static emh);
  isrtype G statT; wf_prog G
 \<rbrakk> \<Longrightarrow> \<exists>m \<in> dynlookup G statT dynC sig: 
          is_static m=is_static emh \<and> G\<turnstile>resTy m\<preceq>resTy emh"
proof - 
  assume      emh: "emh \<in> mheads G S statT sig"
  and          wf: "wf_prog G"
  and   dynC_Prop: "G,statT \<turnstile> dynC valid_lookup_cls_for (is_static emh)"
  and      istype: "isrtype G statT"
  from dynC_Prop istype wf 
  obtain y where
    dynC: "class G dynC = Some y" 
    by (auto dest: valid_lookup_cls_is_class)
  from emh wf show ?thesis
  proof (cases rule: mheads_cases)
    case Class_methd
    fix statC statDeclC sm
    assume     statC: "statT = ClassT statC"
    assume            "accmethd G S statC sig = Some sm"
    then have     sm: "methd G statC sig = Some sm" 
      by (blast dest: accmethd_SomeD)  
    assume eq_mheads: "mhead (mthd sm) = mhd emh"
    from statC 
    have dynlookup: "dynlookup G statT dynC sig = dynmethd G statC dynC sig"
      by (simp add: dynlookup_def)
    from wf statC istype dynC_Prop sm 
    obtain dm where
      "dynmethd G statC dynC sig = Some dm"
      "is_static dm = is_static sm" 
      "G\<turnstile>resTy dm\<preceq>resTy sm"  
      by (force dest!: ws_dynmethd accmethd_SomeD)
    with dynlookup eq_mheads 
    show ?thesis 
      by (cases emh type: *) (auto)
  next
    case Iface_methd
    fix I im
    assume    statI: "statT = IfaceT I" and
          eq_mheads: "mthd im = mhd emh" and
                     "im \<in> accimethds G (pid S) I sig" 
    then have im: "im \<in> imethds G I sig" 
      by (blast dest: accimethdsD)
    with istype statI eq_mheads wf 
    have not_static_emh: "\<not> is_static emh"
      by (cases emh) (auto dest: wf_prog_idecl imethds_wf_mhead)
    from statI im
    have dynlookup: "dynlookup G statT dynC sig = methd G dynC sig"
      by (auto simp add: dynlookup_def dynimethd_def) 
    from wf dynC_Prop statI istype im not_static_emh 
    obtain dm where
      "methd G dynC sig = Some dm"
      "is_static dm = is_static im" 
      "G\<turnstile>resTy (mthd dm)\<preceq>resTy (mthd im)" 
      by (force dest: implmt_methd)
    with dynlookup eq_mheads
    show ?thesis 
      by (cases emh type: *) (auto)
  next
    case Iface_Object_methd
    fix I sm
    assume   statI: "statT = IfaceT I" and
                sm: "accmethd G S Object sig = Some sm" and 
         eq_mheads: "mhead (mthd sm) = mhd emh" and
             nPriv: "accmodi sm \<noteq> Private"
     show ?thesis 
     proof (cases "imethds G I sig = {}")
       case True
       with statI 
       have dynlookup: "dynlookup G statT dynC sig = dynmethd G Object dynC sig"
	 by (simp add: dynlookup_def dynimethd_def)
       from wf dynC 
       have subclsObj: "G\<turnstile>dynC \<preceq>\<^sub>C Object"
	 by (auto intro: subcls_ObjectI)
       from wf dynC dynC_Prop istype sm subclsObj 
       obtain dm where
	 "dynmethd G Object dynC sig = Some dm"
	 "is_static dm = is_static sm" 
	 "G\<turnstile>resTy (mthd dm)\<preceq>resTy (mthd sm)"  
	 by (auto dest!: ws_dynmethd accmethd_SomeD 
                  intro: class_Object [OF wf] intro: that)
       with dynlookup eq_mheads
       show ?thesis 
	 by (cases emh type: *) (auto)
     next
       case False
       with statI
       have dynlookup: "dynlookup G statT dynC sig = methd G dynC sig"
	 by (simp add: dynlookup_def dynimethd_def)
       from istype statI
       have "is_iface G I"
	 by auto
       with wf sm nPriv False 
       obtain im where
	      im: "im \<in> imethds G I sig" and
	 eq_stat: "is_static im = is_static sm" and
         resProp: "G\<turnstile>resTy (mthd im)\<preceq>resTy (mthd sm)"
	 by (auto dest: wf_imethds_hiding_objmethdsD accmethd_SomeD)
       from im wf statI istype eq_stat eq_mheads
       have not_static_sm: "\<not> is_static emh"
	 by (cases emh) (auto dest: wf_prog_idecl imethds_wf_mhead)
       from im wf dynC_Prop dynC istype statI not_static_sm
       obtain dm where
	 "methd G dynC sig = Some dm"
	 "is_static dm = is_static im" 
	 "G\<turnstile>resTy (mthd dm)\<preceq>resTy (mthd im)" 
	 by (auto dest: implmt_methd)
       with wf eq_stat resProp dynlookup eq_mheads
       show ?thesis 
	 by (cases emh type: *) (auto intro: widen_trans)
     qed
  next
    case Array_Object_methd
    fix T sm
    assume statArr: "statT = ArrayT T" and
                sm: "accmethd G S Object sig = Some sm" and 
         eq_mheads: "mhead (mthd sm) = mhd emh" 
    from statArr dynC_Prop wf
    have dynlookup: "dynlookup G statT dynC sig = methd G Object sig"
      by (auto simp add: dynlookup_def dynmethd_C_C)
    with sm eq_mheads sm 
    show ?thesis 
      by (cases emh type: *) (auto dest: accmethd_SomeD)
  qed
qed
declare split_paired_All [simp] split_paired_Ex [simp]
ML_setup {*
claset_ref()  := claset() addSbefore ("split_all_tac", split_all_tac);
simpset_ref() := simpset() addloop ("split_all_tac", split_all_tac)
*}

(* Tactical version *)
(*
lemma dynamic_mheadsD: "  
 \<lbrakk>emh \<in> mheads G S statT sig; wf_prog G; class G dynC = Some y;  
   if (\<exists>T. statT=ArrayT T) then dynC=Object else G\<turnstile>Class dynC\<preceq>RefT statT; 
   isrtype G statT\<rbrakk> \<Longrightarrow>  
  \<exists>m \<in> dynlookup G statT dynC sig: 
     static (mthd m)=static (mhd emh) \<and> G\<turnstile>resTy (mthd m)\<preceq>resTy (mhd emh)"
apply (drule mheadsD)
apply safe
       -- reftype statT is a class  
apply  (case_tac "\<exists>T. ClassT C = ArrayT T")
apply    (simp)

apply    (clarsimp simp add: dynlookup_def )
apply    (frule_tac statC="C" and dynC="dynC"  and sig="sig"  
         in ws_dynmethd)
apply      assumption+
apply    (case_tac "emh")  
apply    (force dest: accmethd_SomeD)

       -- reftype statT is a interface, method defined in interface 
apply    (clarsimp simp add: dynlookup_def)
apply    (drule (1) implmt_methd)
apply      blast
apply      blast
apply    (clarify)  
apply    (unfold dynimethd_def)
apply    (rule_tac x="cm" in bexI)
apply      (case_tac "emh")
apply      force

apply      force

        -- reftype statT is a interface, method defined in Object 
apply    (simp add: dynlookup_def)
apply    (simp only: dynimethd_def)
apply    (case_tac "imethds G I sig = {}")
apply       simp
apply       (frule_tac statC="Object" and dynC="dynC"  and sig="sig"  
             in ws_dynmethd)
apply          (blast intro: subcls_ObjectI wf_ws_prog) 
apply          (blast dest: class_Object)
apply       (case_tac "emh") 
apply       (force dest: accmethd_SomeD)

apply       simp
apply       (subgoal_tac "\<exists> im. im \<in> imethds G I sig") 
prefer 2      apply blast
apply       clarify
apply       (frule (1) implmt_methd)
apply         simp
apply         blast  
apply       (clarify dest!: accmethd_SomeD)
apply       (frule (4) iface_overrides_Object)
apply       clarify
apply       (case_tac emh)
apply       force

        -- reftype statT is a array
apply    (simp add: dynlookup_def)
apply    (case_tac emh)
apply    (force dest: accmethd_SomeD simp add: dynmethd_def)
done
*)

(* FIXME occasionally convert to ws_class_induct*) 
lemma methd_declclass:
"\<lbrakk>class G C = Some c; wf_prog G; methd G C sig = Some m\<rbrakk> 
 \<Longrightarrow> methd G (declclass m) sig = Some m"
proof -
  assume asm: "class G C = Some c" "wf_prog G" "methd G C sig = Some m"
  have "wf_prog G  \<longrightarrow> 
	   (\<forall> c m. class G C = Some c \<longrightarrow>  methd G C sig = Some m 
                   \<longrightarrow>  methd G (declclass m) sig = Some m)"      (is "?P G C") 
  proof (rule class_rec.induct,intro allI impI)
    fix G C c m
    assume hyp: "\<forall>c. C \<noteq> Object \<and> ws_prog G \<and> class G C = Some c \<longrightarrow>
                     ?P G (super c)"
    assume wf: "wf_prog G" and cls_C: "class G C = Some c" and
            m: "methd G C sig = Some m"
    show "methd G (declclass m) sig = Some m"
    proof (cases "C=Object")
      case True
      with wf m show ?thesis by (auto intro: table_of_map_SomeI)
    next
      let ?filter="filter_tab (\<lambda>sig m. G\<turnstile>C inherits method sig m)"
      let ?table = "table_of (map (\<lambda>(s, m). (s, C, m)) (methods c))"
      case False
      with cls_C wf m
      have methd_C: "(?filter (methd G (super c)) ++ ?table) sig = Some m "
	by (simp add: methd_rec)
      show ?thesis
      proof (cases "?table sig")
	case None
	from this methd_C have "?filter (methd G (super c)) sig = Some m"
	  by simp
	moreover
	from wf cls_C False obtain sup where "class G (super c) = Some sup"
	  by (blast dest: wf_prog_cdecl wf_cdecl_supD is_acc_class_is_class)
	moreover note wf False cls_C 
	ultimately show ?thesis by (auto intro: hyp [rule_format])
      next
	case Some
	from this methd_C m show ?thesis by auto 
      qed
    qed
  qed	
  with asm show ?thesis by auto
qed

lemma dynmethd_declclass:
 "\<lbrakk>dynmethd G statC dynC sig = Some m;
   wf_prog G; is_class G statC
  \<rbrakk> \<Longrightarrow> methd G (declclass m) sig = Some m"
by (auto dest: dynmethd_declC)

lemma dynlookup_declC:
 "\<lbrakk>dynlookup G statT dynC sig = Some m; wf_prog G;
   is_class G dynC;isrtype G statT
  \<rbrakk> \<Longrightarrow> G\<turnstile>dynC \<preceq>\<^sub>C (declclass m) \<and> is_class G (declclass m)"
by (cases "statT")
   (auto simp add: dynlookup_def dynimethd_def 
             dest: methd_declC dynmethd_declC)

lemma dynlookup_Array_declclassD [simp]:
"\<lbrakk>dynlookup G (ArrayT T) Object sig = Some dm;wf_prog G\<rbrakk> 
 \<Longrightarrow> declclass dm = Object"
proof -
  assume dynL: "dynlookup G (ArrayT T) Object sig = Some dm"
  assume wf: "wf_prog G"
  from wf have ws: "ws_prog G" by auto
  from wf have is_cls_Obj: "is_class G Object" by auto
  from dynL wf
  show ?thesis
    by (auto simp add: dynlookup_def dynmethd_C_C [OF is_cls_Obj ws]
                 dest: methd_Object_SomeD)
qed   
  

declare split_paired_All [simp del] split_paired_Ex [simp del]
ML_setup {*
simpset_ref() := simpset() delloop "split_all_tac";
claset_ref () := claset () delSWrapper "split_all_tac"
*}
lemma wt_is_type: "E,dt\<Turnstile>v\<Colon>T \<Longrightarrow>  wf_prog (prg E) \<longrightarrow> 
  dt=empty_dt \<longrightarrow> (case T of 
                     Inl T \<Rightarrow> is_type (prg E) T 
                   | Inr Ts \<Rightarrow> Ball (set Ts) (is_type (prg E)))"
apply (unfold empty_dt_def)
apply (erule wt.induct)
apply (auto split del: split_if_asm simp del: snd_conv 
            simp add: is_acc_class_def is_acc_type_def)
apply    (erule typeof_empty_is_type)
apply   (frule (1) wf_prog_cdecl [THEN wf_cdecl_supD], 
        force simp del: snd_conv, clarsimp simp add: is_acc_class_def)
apply  (drule (1) max_spec2mheads [THEN conjunct1, THEN mheadsD])
apply  (drule_tac [2] accfield_fields) 
apply  (frule class_Object)
apply  (auto dest: accmethd_rT_is_type 
                   imethds_wf_mhead [THEN conjunct1, THEN rT_is_acc_type]
             dest!:accimethdsD
             simp del: class_Object
             simp add: is_acc_type_def
    )
done
declare split_paired_All [simp] split_paired_Ex [simp]
ML_setup {*
claset_ref()  := claset() addSbefore ("split_all_tac", split_all_tac);
simpset_ref() := simpset() addloop ("split_all_tac", split_all_tac)
*}

lemma ty_expr_is_type: 
"\<lbrakk>E\<turnstile>e\<Colon>-T; wf_prog (prg E)\<rbrakk> \<Longrightarrow> is_type (prg E) T"
by (auto dest!: wt_is_type)
lemma ty_var_is_type: 
"\<lbrakk>E\<turnstile>v\<Colon>=T; wf_prog (prg E)\<rbrakk> \<Longrightarrow> is_type (prg E) T"
by (auto dest!: wt_is_type)
lemma ty_exprs_is_type: 
"\<lbrakk>E\<turnstile>es\<Colon>\<doteq>Ts; wf_prog (prg E)\<rbrakk> \<Longrightarrow> Ball (set Ts) (is_type (prg E))"
by (auto dest!: wt_is_type)


lemma static_mheadsD: 
 "\<lbrakk> emh \<in> mheads G S t sig; wf_prog G; E\<turnstile>e\<Colon>-RefT t; prg E=G ; 
   invmode (mhd emh) e \<noteq> IntVir 
  \<rbrakk> \<Longrightarrow> \<exists>m. (   (\<exists> C. t = ClassT C \<and> accmethd G S C sig = Some m)
               \<or> (\<forall> C. t \<noteq> ClassT C \<and> accmethd G S Object sig = Some m )) \<and> 
          declrefT emh = ClassT (declclass m) \<and>  mhead (mthd m) = (mhd emh)"
apply (subgoal_tac "is_static emh \<or> e = Super")
defer apply (force simp add: invmode_def)
apply (frule  ty_expr_is_type)
apply   simp
apply (case_tac "is_static emh")
apply  (frule (1) mheadsD)
apply  clarsimp
apply  safe
apply    blast
apply   (auto dest!: imethds_wf_mhead
                     accmethd_SomeD 
                     accimethdsD
              simp add: accObjectmheads_def Objectmheads_def)

apply  (erule wt_elim_cases)
apply  (force simp add: cmheads_def)
done

lemma wt_MethdI:  
"\<lbrakk>methd G C sig = Some m; wf_prog G;  
  class G C = Some c\<rbrakk> \<Longrightarrow>  
 \<exists>T. \<lparr>prg=G,cls=(declclass m),
      lcl=callee_lcl (declclass m) sig (mthd m)\<rparr>\<turnstile> Methd C sig\<Colon>-T \<and> G\<turnstile>T\<preceq>resTy m"
apply (frule (2) methd_wf_mdecl, clarify)
apply (force dest!: wf_mdecl_bodyD intro!: wt.Methd)
done

subsection "accessibility concerns"

lemma mheads_type_accessible:
 "\<lbrakk>emh \<in> mheads G S T sig; wf_prog G\<rbrakk>
 \<Longrightarrow> G\<turnstile>RefT T accessible_in (pid S)"
by (erule mheads_cases)
   (auto dest: accmethd_SomeD accessible_from_commonD accimethdsD)

lemma static_to_dynamic_accessible_from_aux:
"\<lbrakk>G\<turnstile>m of C accessible_from accC;wf_prog G\<rbrakk> 
 \<Longrightarrow> G\<turnstile>m in C dyn_accessible_from accC"
proof (induct rule: accessible_fromR.induct)
qed (auto intro: dyn_accessible_fromR.intros 
                 member_of_to_member_in
                 static_to_dynamic_overriding)

lemma static_to_dynamic_accessible_from:
  assumes stat_acc: "G\<turnstile>m of statC accessible_from accC" and
          subclseq: "G\<turnstile>dynC \<preceq>\<^sub>C statC" and
                wf: "wf_prog G"
  shows "G\<turnstile>m in dynC dyn_accessible_from accC"
proof - 
  from stat_acc subclseq 
  show ?thesis (is "?Dyn_accessible m")
  proof (induct rule: accessible_fromR.induct)
    case (Immediate statC m)
    then show "?Dyn_accessible m"
      by (blast intro: dyn_accessible_fromR.Immediate
                       member_inI
                       permits_acc_inheritance)
  next
    case (Overriding _ _ m)
    with wf show "?Dyn_accessible m"
      by (blast intro: dyn_accessible_fromR.Overriding
                       member_inI
                       static_to_dynamic_overriding  
                       rtrancl_trancl_trancl 
                       static_to_dynamic_accessible_from_aux)
  qed
qed

lemma static_to_dynamic_accessible_from_static:
  assumes stat_acc: "G\<turnstile>m of statC accessible_from accC" and
            static: "is_static m" and
                wf: "wf_prog G"
  shows "G\<turnstile>m in (declclass m) dyn_accessible_from accC"
proof -
  from stat_acc wf 
  have "G\<turnstile>m in statC dyn_accessible_from accC"
    by (auto intro: static_to_dynamic_accessible_from)
  from this static
  show ?thesis
    by (rule dyn_accessible_from_static_declC)
qed

lemma dynmethd_member_in:
  assumes    m: "dynmethd G statC dynC sig = Some m" and
   iscls_statC: "is_class G statC" and
            wf: "wf_prog G"
  shows "G\<turnstile>Methd sig m member_in dynC"
proof -
  from m 
  have subclseq: "G\<turnstile>dynC \<preceq>\<^sub>C statC"
    by (auto simp add: dynmethd_def)
  from subclseq iscls_statC 
  have iscls_dynC: "is_class G dynC"
    by (rule subcls_is_class2)
  from  iscls_dynC iscls_statC wf m
  have "G\<turnstile>dynC \<preceq>\<^sub>C (declclass m) \<and> is_class G (declclass m) \<and>
        methd G (declclass m) sig = Some m" 
    by - (drule dynmethd_declC, auto)
  with wf 
  show ?thesis
    by (auto intro: member_inI dest: methd_member_of)
qed

lemma dynmethd_access_prop:
  assumes statM: "methd G statC sig = Some statM" and
       stat_acc: "G\<turnstile>Methd sig statM of statC accessible_from accC" and
           dynM: "dynmethd G statC dynC sig = Some dynM" and
             wf: "wf_prog G" 
  shows "G\<turnstile>Methd sig dynM in dynC dyn_accessible_from accC"
proof -
  from wf have ws: "ws_prog G" ..
  from dynM 
  have subclseq: "G\<turnstile>dynC \<preceq>\<^sub>C statC"
    by (auto simp add: dynmethd_def)
  from stat_acc 
  have is_cls_statC: "is_class G statC"
    by (auto dest: accessible_from_commonD member_of_is_classD)
  with subclseq 
  have is_cls_dynC: "is_class G dynC"
    by (rule subcls_is_class2)
  from is_cls_statC statM wf 
  have member_statC: "G\<turnstile>Methd sig statM member_of statC"
    by (auto intro: methd_member_of)
  from stat_acc 
  have statC_acc: "G\<turnstile>Class statC accessible_in (pid accC)"
    by (auto dest: accessible_from_commonD)
  from statM subclseq is_cls_statC ws 
  show ?thesis
  proof (cases rule: dynmethd_cases)
    case Static
    assume dynmethd: "dynmethd G statC dynC sig = Some statM"
    with dynM have eq_dynM_statM: "dynM=statM" 
      by simp
    with stat_acc subclseq wf 
    show ?thesis
      by (auto intro: static_to_dynamic_accessible_from)
  next
    case (Overrides newM)
    assume dynmethd: "dynmethd G statC dynC sig = Some newM"
    assume override: "G,sig\<turnstile>newM overrides statM"
    assume      neq: "newM\<noteq>statM"
    from dynmethd dynM 
    have eq_dynM_newM: "dynM=newM" 
      by simp
    from dynmethd eq_dynM_newM wf is_cls_statC
    have "G\<turnstile>Methd sig dynM member_in dynC"
      by (auto intro: dynmethd_member_in)
    moreover
    from subclseq
    have "G\<turnstile>dynC\<prec>\<^sub>C statC"
    proof (cases rule: subclseq_cases)
      case Eq
      assume "dynC=statC"
      moreover
      from is_cls_statC obtain c
	where "class G statC = Some c"
	by auto
      moreover 
      note statM ws dynmethd 
      ultimately
      have "newM=statM" 
	by (auto simp add: dynmethd_C_C)
      with neq show ?thesis 
	by (contradiction)
    next
      case Subcls show ?thesis .
    qed 
    moreover
    from stat_acc wf 
    have "G\<turnstile>Methd sig statM in statC dyn_accessible_from accC"
      by (blast intro: static_to_dynamic_accessible_from)
    moreover
    note override eq_dynM_newM
    ultimately show ?thesis
      by (cases dynM,cases statM) (auto intro: dyn_accessible_fromR.Overriding)
  qed
qed

lemma implmt_methd_access:
  fixes accC::qtname
  assumes iface_methd: "imethds G I sig \<noteq> {}" and
           implements: "G\<turnstile>dynC\<leadsto>I"  and
               isif_I: "is_iface G I" and
                   wf: "wf_prog G" 
  shows "\<exists> dynM. methd G dynC sig = Some dynM \<and> 
            G\<turnstile>Methd sig dynM in dynC dyn_accessible_from accC"
proof -
  from implements 
  have iscls_dynC: "is_class G dynC" by (rule implmt_is_class)
  from iface_methd
  obtain im
    where "im \<in> imethds G I sig"
    by auto
  with wf implements isif_I 
  obtain dynM 
    where dynM: "methd G dynC sig = Some dynM" and
           pub: "accmodi dynM = Public"
    by (blast dest: implmt_methd)
  with iscls_dynC wf
  have "G\<turnstile>Methd sig dynM in dynC dyn_accessible_from accC"
    by (auto intro!: dyn_accessible_fromR.Immediate 
              intro: methd_member_of member_of_to_member_in
                     simp add: permits_acc_def)
  with dynM    
  show ?thesis
    by blast
qed

corollary implmt_dynimethd_access:
  fixes accC::qtname
  assumes iface_methd: "imethds G I sig \<noteq> {}" and
           implements: "G\<turnstile>dynC\<leadsto>I"  and
               isif_I: "is_iface G I" and
                   wf: "wf_prog G" 
  shows "\<exists> dynM. dynimethd G I dynC sig = Some dynM \<and> 
            G\<turnstile>Methd sig dynM in dynC dyn_accessible_from accC"
proof -
  from iface_methd
  have "dynimethd G I dynC sig = methd G dynC sig"
    by (simp add: dynimethd_def)
  with iface_methd implements isif_I wf 
  show ?thesis
    by (simp only:)
       (blast intro: implmt_methd_access)
qed

lemma dynlookup_access_prop:
  assumes emh: "emh \<in> mheads G accC statT sig" and
         dynM: "dynlookup G statT dynC sig = Some dynM" and
    dynC_prop: "G,statT \<turnstile> dynC valid_lookup_cls_for is_static emh" and
    isT_statT: "isrtype G statT" and
           wf: "wf_prog G"
  shows "G \<turnstile>Methd sig dynM in dynC dyn_accessible_from accC"
proof -
  from emh wf
  have statT_acc: "G\<turnstile>RefT statT accessible_in (pid accC)"
    by (rule mheads_type_accessible)
  from dynC_prop isT_statT wf
  have iscls_dynC: "is_class G dynC"
    by (rule valid_lookup_cls_is_class)
  from emh dynC_prop isT_statT wf dynM
  have eq_static: "is_static emh = is_static dynM"
    by (auto dest: dynamic_mheadsD)
  from emh wf show ?thesis
  proof (cases rule: mheads_cases)
    case (Class_methd statC _ statM)
    assume statT: "statT = ClassT statC"
    assume "accmethd G accC statC sig = Some statM"
    then have    statM: "methd G statC sig = Some statM" and
              stat_acc: "G\<turnstile>Methd sig statM of statC accessible_from accC"
      by (auto dest: accmethd_SomeD)
    from dynM statT
    have dynM': "dynmethd G statC dynC sig = Some dynM"
      by (simp add: dynlookup_def) 
    from statM stat_acc wf dynM'
    show ?thesis
      by (auto dest!: dynmethd_access_prop)
  next
    case (Iface_methd I im)
    then have iface_methd: "imethds G I sig \<noteq> {}" and
                 statT_acc: "G\<turnstile>RefT statT accessible_in (pid accC)" 
      by (auto dest: accimethdsD)
    assume   statT: "statT = IfaceT I"
    assume      im: "im \<in>  accimethds G (pid accC) I sig"
    assume eq_mhds: "mthd im = mhd emh"
    from dynM statT
    have dynM': "dynimethd G I dynC sig = Some dynM"
      by (simp add: dynlookup_def)
    from isT_statT statT 
    have isif_I: "is_iface G I"
      by simp
    show ?thesis
    proof (cases "is_static emh")
      case False
      with statT dynC_prop 
      have widen_dynC: "G\<turnstile>Class dynC \<preceq> RefT statT"
	by simp
      from statT widen_dynC
      have implmnt: "G\<turnstile>dynC\<leadsto>I"
	by auto    
      from eq_static False 
      have not_static_dynM: "\<not> is_static dynM" 
	by simp
      from iface_methd implmnt isif_I wf dynM'
      show ?thesis
	by - (drule implmt_dynimethd_access, auto)
    next
      case True
      assume "is_static emh"
      moreover
      from wf isT_statT statT im 
      have "\<not> is_static im"
	by (auto dest: accimethdsD wf_prog_idecl imethds_wf_mhead)
      moreover note eq_mhds
      ultimately show ?thesis
	by (cases emh) auto
    qed
  next
    case (Iface_Object_methd I statM)
    assume statT: "statT = IfaceT I"
    assume "accmethd G accC Object sig = Some statM"
    then have    statM: "methd G Object sig = Some statM" and
              stat_acc: "G\<turnstile>Methd sig statM of Object accessible_from accC"
      by (auto dest: accmethd_SomeD)
    assume not_Private_statM: "accmodi statM \<noteq> Private"
    assume eq_mhds: "mhead (mthd statM) = mhd emh"
    from iscls_dynC wf
    have widen_dynC_Obj: "G\<turnstile>dynC \<preceq>\<^sub>C Object"
      by (auto intro: subcls_ObjectI)
    show ?thesis
    proof (cases "imethds G I sig = {}")
      case True
      from dynM statT True
      have dynM': "dynmethd G Object dynC sig = Some dynM"
	by (simp add: dynlookup_def dynimethd_def)
      from statT  
      have "G\<turnstile>RefT statT \<preceq>Class Object"
	by auto
      with statM statT_acc stat_acc widen_dynC_Obj statT isT_statT 
        wf dynM' eq_static dynC_prop  
      show ?thesis
	by - (drule dynmethd_access_prop,force+) 
    next
      case False
      then obtain im where
	im: "im \<in>  imethds G I sig"
	by auto
      have not_static_emh: "\<not> is_static emh"
      proof -
	from im statM statT isT_statT wf not_Private_statM 
	have "is_static im = is_static statM"
	  by (fastsimp dest: wf_imethds_hiding_objmethdsD)
	with wf isT_statT statT im 
	have "\<not> is_static statM"
	  by (auto dest: wf_prog_idecl imethds_wf_mhead)
	with eq_mhds
	show ?thesis  
	  by (cases emh) auto
      qed
      with statT dynC_prop
      have implmnt: "G\<turnstile>dynC\<leadsto>I"
	by simp
      with isT_statT statT
      have isif_I: "is_iface G I"
	by simp
      from dynM statT
      have dynM': "dynimethd G I dynC sig = Some dynM"
	by (simp add: dynlookup_def) 
      from False implmnt isif_I wf dynM'
      show ?thesis
	by - (drule implmt_dynimethd_access, auto)
    qed
  next
    case (Array_Object_methd T statM)
    assume statT: "statT = ArrayT T"
    assume "accmethd G accC Object sig = Some statM"
    then have    statM: "methd G Object sig = Some statM" and
              stat_acc: "G\<turnstile>Methd sig statM of Object accessible_from accC"
      by (auto dest: accmethd_SomeD)
    from statT dynC_prop
    have dynC_Obj: "dynC = Object" 
      by simp
    then
    have widen_dynC_Obj: "G\<turnstile>Class dynC \<preceq> Class Object"
      by simp
    from dynM statT    
    have dynM': "dynmethd G Object dynC sig = Some dynM"
      by (simp add: dynlookup_def)
    from statM statT_acc stat_acc dynM' wf widen_dynC_Obj  
         statT isT_statT  
    show ?thesis   
      by - (drule dynmethd_access_prop, simp+) 
  qed
qed

lemma dynlookup_access:
  assumes emh: "emh \<in> mheads G accC statT sig" and
    dynC_prop: "G,statT \<turnstile> dynC valid_lookup_cls_for (is_static emh) " and
    isT_statT: "isrtype G statT" and
           wf: "wf_prog G"
  shows "\<exists> dynM. dynlookup G statT dynC sig = Some dynM \<and> 
            G\<turnstile>Methd sig dynM in dynC dyn_accessible_from accC"
proof - 
  from dynC_prop isT_statT wf
  have is_cls_dynC: "is_class G dynC"
    by (auto dest: valid_lookup_cls_is_class)
  with emh wf dynC_prop isT_statT
  obtain dynM where 
    "dynlookup G statT dynC sig = Some dynM"
    by - (drule dynamic_mheadsD,auto)
  with  emh dynC_prop isT_statT wf
  show ?thesis 
    by (blast intro: dynlookup_access_prop)
qed

lemma stat_overrides_Package_old: 
  assumes stat_override: "G \<turnstile> new overrides\<^sub>S old" and 
          accmodi_new: "accmodi new = Package" and
                   wf: "wf_prog G "
  shows "accmodi old = Package"
proof -
  from stat_override wf 
  have "accmodi old \<le> accmodi new"
    by (auto dest: wf_prog_stat_overridesD)
  with stat_override accmodi_new show ?thesis
    by (cases "accmodi old") (auto dest: no_Private_stat_override 
                                   dest: acc_modi_le_Dests)
qed

subsubsection {* Properties of dynamic accessibility *}

lemma dyn_accessible_Private:
 assumes dyn_acc: "G \<turnstile> m in C dyn_accessible_from accC" and
            priv: "accmodi m = Private"
   shows "accC = declclass m"
proof -
  from dyn_acc priv
  show ?thesis
  proof (induct)
    case (Immediate C m)
    have "G \<turnstile> m in C permits_acc_to accC" and "accmodi m = Private" .
    then show ?case
      by (simp add: permits_acc_def)
  next
    case Overriding
    then show ?case
      by (auto dest!: overrides_commonD)
  qed
qed

text {* @{text dyn_accessible_Package} only works with the @{text wf_prog} assumption. 
Without it. it is easy to leaf the Package!
*}
lemma dyn_accessible_Package:
 "\<lbrakk>G \<turnstile> m in C dyn_accessible_from accC; accmodi m = Package;
   wf_prog G\<rbrakk>
  \<Longrightarrow> pid accC = pid (declclass m)"
proof -
  assume wf: "wf_prog G "
  assume accessible: "G \<turnstile> m in C dyn_accessible_from accC"
  then show "accmodi m = Package 
            \<Longrightarrow> pid accC = pid (declclass m)"
    (is "?Pack m \<Longrightarrow> ?P m")
  proof (induct rule: dyn_accessible_fromR.induct)
    case (Immediate C m)
    assume "G\<turnstile>m member_in C"
           "G \<turnstile> m in C permits_acc_to accC"
           "accmodi m = Package"      
    then show "?P m"
      by (auto simp add: permits_acc_def)
  next
    case (Overriding declC C new newm old Sup)
    assume member_new: "G \<turnstile> new member_in C" and
                  new: "new = (declC, mdecl newm)" and
             override: "G \<turnstile> (declC, newm) overrides old" and
         subcls_C_Sup: "G\<turnstile>C \<prec>\<^sub>C Sup" and
              acc_old: "G \<turnstile> methdMembr old in Sup dyn_accessible_from accC" and
                  hyp: "?Pack (methdMembr old) \<Longrightarrow> ?P (methdMembr old)" and
          accmodi_new: "accmodi new = Package"
    from override accmodi_new new wf 
    have accmodi_old: "accmodi old = Package"  
      by (auto dest: overrides_Package_old)
    with hyp 
    have P_sup: "?P (methdMembr old)"
      by (simp)
    from wf override new accmodi_old accmodi_new
    have eq_pid_new_old: "pid (declclass new) = pid (declclass old)"
      by (auto dest: dyn_override_Package)
    with eq_pid_new_old P_sup show "?P new"
      by auto
  qed
qed

text {* For fields we don't need the wellformedness of the program, since
there is no overriding *}
lemma dyn_accessible_field_Package:
 assumes dyn_acc: "G \<turnstile> f in C dyn_accessible_from accC" and
            pack: "accmodi f = Package" and
           field: "is_field f"
   shows "pid accC = pid (declclass f)"
proof -
  from dyn_acc pack field
  show ?thesis
  proof (induct)
    case (Immediate C f)
    have "G \<turnstile> f in C permits_acc_to accC" and "accmodi f = Package" .
    then show ?case
      by (simp add: permits_acc_def)
  next
    case Overriding
    then show ?case by (simp add: is_field_def)
  qed
qed

text {* @{text dyn_accessible_instance_field_Protected} only works for fields
since methods can break the package bounds due to overriding
*}
lemma dyn_accessible_instance_field_Protected:
  assumes dyn_acc: "G \<turnstile> f in C dyn_accessible_from accC" and
             prot: "accmodi f = Protected" and
            field: "is_field f" and
   instance_field: "\<not> is_static f" and
          outside: "pid (declclass f) \<noteq> pid accC"
  shows "G\<turnstile> C \<preceq>\<^sub>C accC"
proof -
  from dyn_acc prot field instance_field outside
  show ?thesis
  proof (induct)
    case (Immediate C f)
    have "G \<turnstile> f in C permits_acc_to accC" .
    moreover 
    assume "accmodi f = Protected" and  "is_field f" and "\<not> is_static f" and
           "pid (declclass f) \<noteq> pid accC"
    ultimately 
    show "G\<turnstile> C \<preceq>\<^sub>C accC"
      by (auto simp add: permits_acc_def)
  next
    case Overriding
    then show ?case by (simp add: is_field_def)
  qed
qed
   
lemma dyn_accessible_static_field_Protected:
  assumes dyn_acc: "G \<turnstile> f in C dyn_accessible_from accC" and
             prot: "accmodi f = Protected" and
            field: "is_field f" and
     static_field: "is_static f" and
          outside: "pid (declclass f) \<noteq> pid accC"
  shows "G\<turnstile> accC \<preceq>\<^sub>C declclass f  \<and> G\<turnstile>C \<preceq>\<^sub>C declclass f"
proof -
  from dyn_acc prot field static_field outside
  show ?thesis
  proof (induct)
    case (Immediate C f)
    assume "accmodi f = Protected" and  "is_field f" and "is_static f" and
           "pid (declclass f) \<noteq> pid accC"
    moreover 
    have "G \<turnstile> f in C permits_acc_to accC" .
    ultimately
    have "G\<turnstile> accC \<preceq>\<^sub>C declclass f"
      by (auto simp add: permits_acc_def)
    moreover
    have "G \<turnstile> f member_in C" .
    then have "G\<turnstile>C \<preceq>\<^sub>C declclass f"
      by (rule member_in_class_relation)
    ultimately show ?case
      by blast
  next
    case Overriding
    then show ?case by (simp add: is_field_def)
  qed
qed

end