(*  Title:      HOL/Bali/Eval.thy
    ID:         $Id$
    Author:     David von Oheimb
    License:    GPL (GNU GENERAL PUBLIC LICENSE)
*)
header {* Operational evaluation (big-step) semantics of Java expressions and 
          statements
*}

theory Eval = State + DeclConcepts:

text {*

improvements over Java Specification 1.0:
\begin{itemize}
\item dynamic method lookup does not need to consider the return type 
      (cf.15.11.4.4)
\item throw raises a NullPointer exception if a null reference is given, and 
      each throw of a standard exception yield a fresh exception object 
      (was not specified)
\item if there is not enough memory even to allocate an OutOfMemory exception,
  evaluation/execution fails, i.e. simply stops (was not specified)
\item array assignment checks lhs (and may throw exceptions) before evaluating 
      rhs
\item fixed exact positions of class initializations 
      (immediate at first active use)
\end{itemize}

design issues:
\begin{itemize}
\item evaluation vs. (single-step) transition semantics
  evaluation semantics chosen, because:
  \begin{itemize} 
  \item[++] less verbose and therefore easier to read (and to handle in proofs)
  \item[+]  more abstract
  \item[+]  intermediate values (appearing in recursive rules) need not be 
     stored explicitly, e.g. no call body construct or stack of invocation 
     frames containing local variables and return addresses for method calls 
     needed
  \item[+]  convenient rule induction for subject reduction theorem
  \item[-]  no interleaving (for parallelism) can be described
  \item[-]  stating a property of infinite executions requires the meta-level 
     argument that this property holds for any finite prefixes of it 
     (e.g. stopped using a counter that is decremented to zero and then 
     throwing an exception)
  \end{itemize}
\item unified evaluation for variables, expressions, expression lists, 
      statements
\item the value entry in statement rules is redundant 
\item the value entry in rules is irrelevant in case of exceptions, but its full
  inclusion helps to make the rule structure independent of exception occurence.
\item as irrelevant value entries are ignored, it does not matter if they are 
      unique.
  For simplicity, (fixed) arbitrary values are preferred over "free" values.
\item the rule format is such that the start state may contain an exception.
  \begin{itemize}
  \item[++] faciliates exception handling
  \item[+]  symmetry
  \end{itemize}
\item the rules are defined carefully in order to be applicable even in not
  type-correct situations (yielding undefined values),
  e.g. @{text "the_Addr (Val (Bool b)) = arbitrary"}.
  \begin{itemize}
  \item[++] fewer rules 
  \item[-]  less readable because of auxiliary functions like @{text the_Addr}
  \end{itemize}
  Alternative: "defensive" evaluation throwing some InternalError exception
               in case of (impossible, for correct programs) type mismatches
\item there is exactly one rule per syntactic construct
  \begin{itemize}
  \item[+] no redundancy in case distinctions
  \end{itemize}
\item halloc fails iff there is no free heap address. When there is
  only one free heap address left, it returns an OutOfMemory exception.
  In this way it is guaranteed that when an OutOfMemory exception is thrown for
  the first time, there is a free location on the heap to allocate it.
\item the allocation of objects that represent standard exceptions is deferred 
      until execution of any enclosing catch clause, which is transparent to 
      the program.
  \begin{itemize}
  \item[-]  requires an auxiliary execution relation
  \item[++] avoids copies of allocation code and awkward case distinctions 
           (whether there is enough memory to allocate the exception) in 
            evaluation rules
  \end{itemize}
\item unfortunately @{text new_Addr} is not directly executable because of 
      Hilbert operator.
\end{itemize}
simplifications:
\begin{itemize}
\item local variables are initialized with default values 
      (no definite assignment)
\item garbage collection not considered, therefore also no finalizers
\item stack overflow and memory overflow during class initialization not 
      modelled
\item exceptions in initializations not replaced by ExceptionInInitializerError
\end{itemize}
*}

types vvar  =         "val \<times> (val \<Rightarrow> state \<Rightarrow> state)"
      vals  =        "(val, vvar, val list) sum3"
translations
     "vvar" <= (type) "val \<times> (val \<Rightarrow> state \<Rightarrow> state)"
     "vals" <= (type)"(val, vvar, val list) sum3"

syntax (xsymbols)
  dummy_res :: "vals" ("\<diamondsuit>")
translations
  "\<diamondsuit>" == "In1 Unit"

constdefs
  arbitrary3 :: "('al + 'ar, 'b, 'c) sum3 \<Rightarrow> vals"
 "arbitrary3 \<equiv> sum3_case (In1 \<circ> sum_case (\<lambda>x. arbitrary) (\<lambda>x. Unit))
                     (\<lambda>x. In2 arbitrary) (\<lambda>x. In3 arbitrary)"

lemma [simp]: "arbitrary3 (In1l x) = In1 arbitrary"
by (simp add: arbitrary3_def)

lemma [simp]: "arbitrary3 (In1r x) = \<diamondsuit>"
by (simp add: arbitrary3_def)

lemma [simp]: "arbitrary3 (In2  x) = In2 arbitrary"
by (simp add: arbitrary3_def)

lemma [simp]: "arbitrary3 (In3  x) = In3 arbitrary"
by (simp add: arbitrary3_def)


section "exception throwing and catching"

constdefs
  throw :: "val \<Rightarrow> abopt \<Rightarrow> abopt"
 "throw a' x \<equiv> abrupt_if True (Some (Xcpt (Loc (the_Addr a')))) (np a' x)"

lemma throw_def2: 
 "throw a' x = abrupt_if True (Some (Xcpt (Loc (the_Addr a')))) (np a' x)"
apply (unfold throw_def)
apply (simp (no_asm))
done

constdefs
  fits    :: "prog \<Rightarrow> st \<Rightarrow> val \<Rightarrow> ty \<Rightarrow> bool" ("_,_\<turnstile>_ fits _"[61,61,61,61]60)
 "G,s\<turnstile>a' fits T  \<equiv> (\<exists>rt. T=RefT rt) \<longrightarrow> a'=Null \<or> G\<turnstile>obj_ty(lookup_obj s a')\<preceq>T"

lemma fits_Null [simp]: "G,s\<turnstile>Null fits T"
by (simp add: fits_def)


lemma fits_Addr_RefT [simp]:
  "G,s\<turnstile>Addr a fits RefT t = G\<turnstile>obj_ty (the (heap s a))\<preceq>RefT t"
by (simp add: fits_def)

lemma fitsD: "\<And>X. G,s\<turnstile>a' fits T \<Longrightarrow> (\<exists>pt. T = PrimT pt) \<or>  
  (\<exists>t. T = RefT t) \<and> a' = Null \<or>  
  (\<exists>t. T = RefT t) \<and> a' \<noteq> Null \<and>  G\<turnstile>obj_ty (lookup_obj s a')\<preceq>T"
apply (unfold fits_def)
apply (case_tac "\<exists>pt. T = PrimT pt")
apply  simp_all
apply (case_tac "T")
defer 
apply (case_tac "a' = Null")
apply  simp_all
done

constdefs
  catch ::"prog \<Rightarrow> state \<Rightarrow> qtname \<Rightarrow> bool"      ("_,_\<turnstile>catch _"[61,61,61]60)
 "G,s\<turnstile>catch C\<equiv>\<exists>xc. abrupt s=Some (Xcpt xc) \<and> 
                    G,store s\<turnstile>Addr (the_Loc xc) fits Class C"

lemma catch_Norm [simp]: "\<not>G,Norm s\<turnstile>catch tn"
apply (unfold catch_def)
apply (simp (no_asm))
done

lemma catch_XcptLoc [simp]: 
  "G,(Some (Xcpt (Loc a)),s)\<turnstile>catch C = G,s\<turnstile>Addr a fits Class C"
apply (unfold catch_def)
apply (simp (no_asm))
done

constdefs
  new_xcpt_var :: "vname \<Rightarrow> state \<Rightarrow> state"
 "new_xcpt_var vn \<equiv> 
     \<lambda>(x,s). Norm (lupd(VName vn\<mapsto>Addr (the_Loc (the_Xcpt (the x)))) s)"

lemma new_xcpt_var_def2 [simp]: 
 "new_xcpt_var vn (x,s) = 
    Norm (lupd(VName vn\<mapsto>Addr (the_Loc (the_Xcpt (the x)))) s)"
apply (unfold new_xcpt_var_def)
apply (simp (no_asm))
done



section "misc"

constdefs

  assign     :: "('a \<Rightarrow> state \<Rightarrow> state) \<Rightarrow> 'a \<Rightarrow> state \<Rightarrow> state"
 "assign f v \<equiv> \<lambda>(x,s). let (x',s') = (if x = None then f v else id) (x,s)
		   in  (x',if x' = None then s' else s)"

(*
lemma assign_Norm_Norm [simp]: 
"f v \<lparr>abrupt=None,store=s\<rparr> = \<lparr>abrupt=None,store=s'\<rparr> 
 \<Longrightarrow> assign f v \<lparr>abrupt=None,store=s\<rparr> = \<lparr>abrupt=None,store=s'\<rparr>"
by (simp add: assign_def Let_def)
*)

lemma assign_Norm_Norm [simp]: 
"f v (Norm s) = Norm s' \<Longrightarrow> assign f v (Norm s) = Norm s'"
by (simp add: assign_def Let_def)

(*
lemma assign_Norm_Some [simp]: 
  "\<lbrakk>abrupt (f v \<lparr>abrupt=None,store=s\<rparr>) = Some y\<rbrakk> 
   \<Longrightarrow> assign f v \<lparr>abrupt=None,store=s\<rparr> = \<lparr>abrupt=Some y,store =s\<rparr>"
by (simp add: assign_def Let_def split_beta)
*)

lemma assign_Norm_Some [simp]: 
  "\<lbrakk>abrupt (f v (Norm s)) = Some y\<rbrakk> 
   \<Longrightarrow> assign f v (Norm s) = (Some y,s)"
by (simp add: assign_def Let_def split_beta)


lemma assign_Some [simp]: 
"assign f v (Some x,s) = (Some x,s)" 
by (simp add: assign_def Let_def split_beta)

lemma assign_supd [simp]: 
"assign (\<lambda>v. supd (f v)) v (x,s)  
  = (x, if x = None then f v s else s)"
apply auto
done

lemma assign_raise_if [simp]: 
  "assign (\<lambda>v (x,s). ((raise_if (b s v) xcpt) x, f v s)) v (x, s) =  
  (raise_if (b s v) xcpt x, if x=None \<and> \<not>b s v then f v s else s)"
apply (case_tac "x = None")
apply auto
done

(*
lemma assign_raise_if [simp]: 
  "assign (\<lambda>v s. \<lparr>abrupt=(raise_if (b (store s) v) xcpt) (abrupt s),
                  store = f v (store s)\<rparr>) v s =  
  \<lparr>abrupt=raise_if (b (store s) v) xcpt (abrupt s),
   store= if (abrupt s)=None \<and> \<not>b (store s) v 
             then f v (store s) else (store s)\<rparr>"
apply (case_tac "abrupt s = None")
apply auto
done
*)

constdefs

  init_comp_ty :: "ty \<Rightarrow> stmt"
 "init_comp_ty T \<equiv> if (\<exists>C. T = Class C) then Init (the_Class T) else Skip"

lemma init_comp_ty_PrimT [simp]: "init_comp_ty (PrimT pt) = Skip"
apply (unfold init_comp_ty_def)
apply (simp (no_asm))
done

constdefs

(*
  target  :: "inv_mode \<Rightarrow> st \<Rightarrow> val \<Rightarrow> ref_ty \<Rightarrow> qtname"
 "target m s a' t 
    \<equiv> if m = IntVir
	 then obj_class (lookup_obj s a') 
         else the_Class (RefT t)"
*)

 invocation_class  :: "inv_mode \<Rightarrow> st \<Rightarrow> val \<Rightarrow> ref_ty \<Rightarrow> qtname"
 "invocation_class m s a' statT 
    \<equiv> (case m of
         Static \<Rightarrow> if (\<exists> statC. statT = ClassT statC) 
                      then the_Class (RefT statT) 
                      else Object
       | SuperM \<Rightarrow> the_Class (RefT statT)
       | IntVir \<Rightarrow> obj_class (lookup_obj s a'))"

invocation_declclass::"prog \<Rightarrow> inv_mode \<Rightarrow> st \<Rightarrow> val \<Rightarrow> ref_ty \<Rightarrow> sig \<Rightarrow> qtname"
"invocation_declclass G m s a' statT sig 
   \<equiv> declclass (the (dynlookup G statT 
                                (invocation_class m s a' statT)
                                sig))" 
  
lemma invocation_class_IntVir [simp]: 
"invocation_class IntVir s a' statT = obj_class (lookup_obj s a')"
by (simp add: invocation_class_def)

lemma dynclass_SuperM [simp]: 
 "invocation_class SuperM s a' statT = the_Class (RefT statT)"
by (simp add: invocation_class_def)
(*
lemma invocation_class_notIntVir [simp]: 
 "m \<noteq> IntVir \<Longrightarrow> invocation_class m s a' statT = the_Class (RefT statT)"
by (simp add: invocation_class_def)
*)

lemma invocation_class_Static [simp]: 
  "invocation_class Static s a' statT = (if (\<exists> statC. statT = ClassT statC) 
                                            then the_Class (RefT statT) 
                                            else Object)"
by (simp add: invocation_class_def)

constdefs
  init_lvars :: "prog \<Rightarrow> qtname \<Rightarrow> sig \<Rightarrow> inv_mode \<Rightarrow> val \<Rightarrow> val list \<Rightarrow>
		   state \<Rightarrow> state"
 "init_lvars G C sig mode a' pvs 
   \<equiv> \<lambda> (x,s). 
      let m = mthd (the (methd G C sig));
          l = \<lambda> k. 
              (case k of
                 EName e 
                   \<Rightarrow> (case e of 
                         VNam v \<Rightarrow> (init_vals (table_of (lcls (mbody m)))
                                                     ((pars m)[\<mapsto>]pvs)) v
                       | Res    \<Rightarrow> Some (default_val (resTy m)))
               | This 
                   \<Rightarrow> (if mode=Static then None else Some a'))
      in set_lvars l (if mode = Static then x else np a' x,s)"



lemma init_lvars_def2: "init_lvars G C sig mode a' pvs (x,s) =  
  set_lvars 
    (\<lambda> k. 
       (case k of
          EName e 
            \<Rightarrow> (case e of 
                  VNam v 
                  \<Rightarrow> (init_vals 
                       (table_of (lcls (mbody (mthd (the (methd G C sig))))))
                                 ((pars (mthd (the (methd G C sig))))[\<mapsto>]pvs)) v
               | Res \<Rightarrow> Some (default_val (resTy (mthd (the (methd G C sig))))))
        | This 
            \<Rightarrow> (if mode=Static then None else Some a')))
    (if mode = Static then x else np a' x,s)"
apply (unfold init_lvars_def)
apply (simp (no_asm) add: Let_def)
done

constdefs
  body :: "prog \<Rightarrow> qtname \<Rightarrow> sig \<Rightarrow> expr"
 "body G C sig \<equiv> let m = the (methd G C sig) 
                 in Body (declclass m) (stmt (mbody (mthd m)))"

lemma body_def2: 
"body G C sig = Body  (declclass (the (methd G C sig))) 
                      (stmt (mbody (mthd (the (methd G C sig)))))"
apply (unfold body_def Let_def)
apply auto
done

section "variables"

constdefs

  lvar :: "lname \<Rightarrow> st \<Rightarrow> vvar"
 "lvar vn s \<equiv> (the (locals s vn), \<lambda>v. supd (lupd(vn\<mapsto>v)))"

  fvar :: "qtname \<Rightarrow> bool \<Rightarrow> vname \<Rightarrow> val \<Rightarrow> state \<Rightarrow> vvar \<times> state"
 "fvar C stat fn a' s 
    \<equiv> let (oref,xf) = if stat then (Stat C,id)
                              else (Heap (the_Addr a'),np a');
	          n = Inl (fn,C); 
                  f = (\<lambda>v. supd (upd_gobj oref n v)) 
      in ((the (values (the (globs (store s) oref)) n),f),abupd xf s)"

  avar :: "prog \<Rightarrow> val \<Rightarrow> val \<Rightarrow> state \<Rightarrow> vvar \<times> state"
 "avar G i' a' s 
    \<equiv> let   oref = Heap (the_Addr a'); 
               i = the_Intg i'; 
               n = Inr i;
        (T,k,cs) = the_Arr (globs (store s) oref); 
               f = (\<lambda>v (x,s). (raise_if (\<not>G,s\<turnstile>v fits T) 
                                           ArrStore x
                              ,upd_gobj oref n v s)) 
      in ((the (cs n),f)
         ,abupd (raise_if (\<not>i in_bounds k) IndOutBound \<circ> np a') s)"

lemma fvar_def2: "fvar C stat fn a' s =  
  ((the 
     (values 
      (the (globs (store s) (if stat then Stat C else Heap (the_Addr a')))) 
      (Inl (fn,C)))
   ,(\<lambda>v. supd (upd_gobj (if stat then Stat C else Heap (the_Addr a')) 
                        (Inl (fn,C)) 
                        v)))
  ,abupd (if stat then id else np a') s)
  "
apply (unfold fvar_def)
apply (simp (no_asm) add: Let_def split_beta)
done

lemma avar_def2: "avar G i' a' s =  
  ((the ((snd(snd(the_Arr (globs (store s) (Heap (the_Addr a')))))) 
           (Inr (the_Intg i')))
   ,(\<lambda>v (x,s').  (raise_if (\<not>G,s'\<turnstile>v fits (fst(the_Arr (globs (store s)
                                                   (Heap (the_Addr a')))))) 
                            ArrStore x
                 ,upd_gobj  (Heap (the_Addr a')) 
                               (Inr (the_Intg i')) v s')))
  ,abupd (raise_if (\<not>(the_Intg i') in_bounds (fst(snd(the_Arr (globs (store s) 
                   (Heap (the_Addr a'))))))) IndOutBound \<circ> np a')
          s)"
apply (unfold avar_def)
apply (simp (no_asm) add: Let_def split_beta)
done


section "evaluation judgments"

consts
  eval   :: "prog \<Rightarrow> (state \<times> term    \<times> vals \<times> state) set"
  halloc::  "prog \<Rightarrow> (state \<times> obj_tag \<times> loc  \<times> state) set"
  sxalloc:: "prog \<Rightarrow> (state                  \<times> state) set"


syntax
eval ::"[prog,state,term,vals*state]=>bool"("_|-_ -_>-> _"  [61,61,80,   61]60)
exec ::"[prog,state,stmt      ,state]=>bool"("_|-_ -_-> _"   [61,61,65,   61]60)
evar ::"[prog,state,var  ,vvar,state]=>bool"("_|-_ -_=>_-> _"[61,61,90,61,61]60)
eval_::"[prog,state,expr ,val, state]=>bool"("_|-_ -_->_-> _"[61,61,80,61,61]60)
evals::"[prog,state,expr list ,
		    val  list ,state]=>bool"("_|-_ -_#>_-> _"[61,61,61,61,61]60)
hallo::"[prog,state,obj_tag,
	             loc,state]=>bool"("_|-_ -halloc _>_-> _"[61,61,61,61,61]60)
sallo::"[prog,state        ,state]=>bool"("_|-_ -sxalloc-> _"[61,61,      61]60)

syntax (xsymbols)
eval ::"[prog,state,term,vals\<times>state]\<Rightarrow>bool" ("_\<turnstile>_ \<midarrow>_\<succ>\<rightarrow> _"  [61,61,80,   61]60)
exec ::"[prog,state,stmt      ,state]\<Rightarrow>bool"("_\<turnstile>_ \<midarrow>_\<rightarrow> _"   [61,61,65,   61]60)
evar ::"[prog,state,var  ,vvar,state]\<Rightarrow>bool"("_\<turnstile>_ \<midarrow>_=\<succ>_\<rightarrow> _"[61,61,90,61,61]60)
eval_::"[prog,state,expr ,val ,state]\<Rightarrow>bool"("_\<turnstile>_ \<midarrow>_-\<succ>_\<rightarrow> _"[61,61,80,61,61]60)
evals::"[prog,state,expr list ,
		    val  list ,state]\<Rightarrow>bool"("_\<turnstile>_ \<midarrow>_\<doteq>\<succ>_\<rightarrow> _"[61,61,61,61,61]60)
hallo::"[prog,state,obj_tag,
	             loc,state]\<Rightarrow>bool"("_\<turnstile>_ \<midarrow>halloc _\<succ>_\<rightarrow> _"[61,61,61,61,61]60)
sallo::"[prog,state,        state]\<Rightarrow>bool"("_\<turnstile>_ \<midarrow>sxalloc\<rightarrow> _"[61,61,      61]60)

translations
  "G\<turnstile>s \<midarrow>t   \<succ>\<rightarrow>  w___s' " == "(s,t,w___s') \<in> eval G"
  "G\<turnstile>s \<midarrow>t   \<succ>\<rightarrow> (w,  s')" <= "(s,t,w,  s') \<in> eval G"
  "G\<turnstile>s \<midarrow>t   \<succ>\<rightarrow> (w,x,s')" <= "(s,t,w,x,s') \<in> eval G"
  "G\<turnstile>s \<midarrow>c    \<rightarrow>  (x,s')" <= "G\<turnstile>s \<midarrow>In1r c\<succ>\<rightarrow> (\<diamondsuit>,x,s')"
  "G\<turnstile>s \<midarrow>c    \<rightarrow>     s' " == "G\<turnstile>s \<midarrow>In1r c\<succ>\<rightarrow> (\<diamondsuit>  ,  s')"
  "G\<turnstile>s \<midarrow>e-\<succ>v \<rightarrow>  (x,s')" <= "G\<turnstile>s \<midarrow>In1l e\<succ>\<rightarrow> (In1 v ,x,s')"
  "G\<turnstile>s \<midarrow>e-\<succ>v \<rightarrow>     s' " == "G\<turnstile>s \<midarrow>In1l e\<succ>\<rightarrow> (In1 v ,  s')"
  "G\<turnstile>s \<midarrow>e=\<succ>vf\<rightarrow>  (x,s')" <= "G\<turnstile>s \<midarrow>In2  e\<succ>\<rightarrow> (In2 vf,x,s')"
  "G\<turnstile>s \<midarrow>e=\<succ>vf\<rightarrow>     s' " == "G\<turnstile>s \<midarrow>In2  e\<succ>\<rightarrow> (In2 vf,  s')"
  "G\<turnstile>s \<midarrow>e\<doteq>\<succ>v \<rightarrow>  (x,s')" <= "G\<turnstile>s \<midarrow>In3  e\<succ>\<rightarrow> (In3 v ,x,s')"
  "G\<turnstile>s \<midarrow>e\<doteq>\<succ>v \<rightarrow>     s' " == "G\<turnstile>s \<midarrow>In3  e\<succ>\<rightarrow> (In3 v ,  s')"
  "G\<turnstile>s \<midarrow>halloc oi\<succ>a\<rightarrow> (x,s')" <= "(s,oi,a,x,s') \<in> halloc G"
  "G\<turnstile>s \<midarrow>halloc oi\<succ>a\<rightarrow>    s' " == "(s,oi,a,  s') \<in> halloc G"
  "G\<turnstile>s \<midarrow>sxalloc\<rightarrow>     (x,s')" <= "(s     ,x,s') \<in> sxalloc G"
  "G\<turnstile>s \<midarrow>sxalloc\<rightarrow>        s' " == "(s     ,  s') \<in> sxalloc G"

inductive "halloc G" intros (* allocating objects on the heap, cf. 12.5 *)

  Abrupt: 
  "G\<turnstile>(Some x,s) \<midarrow>halloc oi\<succ>arbitrary\<rightarrow> (Some x,s)"

  New:	  "\<lbrakk>new_Addr (heap s) = Some a; 
	    (x,oi') = (if atleast_free (heap s) (Suc (Suc 0)) then (None,oi)
		       else (Some (Xcpt (Loc a)),CInst (SXcpt OutOfMemory)))\<rbrakk>
            \<Longrightarrow>
	    G\<turnstile>Norm s \<midarrow>halloc oi\<succ>a\<rightarrow> (x,init_obj G oi' (Heap a) s)"

inductive "sxalloc G" intros (* allocating exception objects for
	 	 	      standard exceptions (other than OutOfMemory) *)

  Norm:	 "G\<turnstile> Norm              s   \<midarrow>sxalloc\<rightarrow>  Norm             s"

  XcptL: "G\<turnstile>(Some (Xcpt (Loc a) ),s)  \<midarrow>sxalloc\<rightarrow> (Some (Xcpt (Loc a)),s)"

  SXcpt: "\<lbrakk>G\<turnstile>Norm s0 \<midarrow>halloc (CInst (SXcpt xn))\<succ>a\<rightarrow> (x,s1)\<rbrakk> \<Longrightarrow>
	  G\<turnstile>(Some (Xcpt (Std xn)),s0) \<midarrow>sxalloc\<rightarrow> (Some (Xcpt (Loc a)),s1)"


inductive "eval G" intros

(* propagation of abrupt completion *)

  (* cf. 14.1, 15.5 *)
  Abrupt: 
   "G\<turnstile>(Some xc,s) \<midarrow>t\<succ>\<rightarrow> (arbitrary3 t,(Some xc,s))"


(* execution of statements *)

  (* cf. 14.5 *)
  Skip:	 			    "G\<turnstile>Norm s \<midarrow>Skip\<rightarrow> Norm s"

  (* cf. 14.7 *)
  Expr:	"\<lbrakk>G\<turnstile>Norm s0 \<midarrow>e-\<succ>v\<rightarrow> s1\<rbrakk> \<Longrightarrow>
				  G\<turnstile>Norm s0 \<midarrow>Expr e\<rightarrow> s1"

  Lab:  "\<lbrakk>G\<turnstile>Norm s0 \<midarrow>c \<rightarrow> s1\<rbrakk> \<Longrightarrow>
                                G\<turnstile>Norm s0 \<midarrow>l\<bullet> c\<rightarrow> abupd (absorb (Break l)) s1"
  (* cf. 14.2 *)
  Comp:	"\<lbrakk>G\<turnstile>Norm s0 \<midarrow>c1 \<rightarrow> s1;
	  G\<turnstile>     s1 \<midarrow>c2 \<rightarrow> s2\<rbrakk> \<Longrightarrow>
				 G\<turnstile>Norm s0 \<midarrow>c1;; c2\<rightarrow> s2"


  (* cf. 14.8.2 *)
  If:	"\<lbrakk>G\<turnstile>Norm s0 \<midarrow>e-\<succ>b\<rightarrow> s1;
	  G\<turnstile>     s1\<midarrow>(if the_Bool b then c1 else c2)\<rightarrow> s2\<rbrakk> \<Longrightarrow>
		       G\<turnstile>Norm s0 \<midarrow>If(e) c1 Else c2 \<rightarrow> s2"

  (* cf. 14.10, 14.10.1 *)
  (*      G\<turnstile>Norm s0 \<midarrow>If(e) (c;; While(e) c) Else Skip\<rightarrow> s3 *)
  (* A "continue jump" from the while body c is handled by 
     this rule. If a continue jump with the proper label was invoked inside c
     this label (Cont l) is deleted out of the abrupt component of the state 
     before the iterative evaluation of the while statement.
     A "break jump" is handled by the Lab Statement (Lab l (while\<dots>).
  *)
  Loop:	"\<lbrakk>G\<turnstile>Norm s0 \<midarrow>e-\<succ>b\<rightarrow> s1;
	  if normal s1 \<and> the_Bool b 
             then (G\<turnstile>s1 \<midarrow>c\<rightarrow> s2 \<and> 
                   G\<turnstile>(abupd (absorb (Cont l)) s2) \<midarrow>l\<bullet> While(e) c\<rightarrow> s3)
	     else s3 = s1\<rbrakk> \<Longrightarrow>
			      G\<turnstile>Norm s0 \<midarrow>l\<bullet> While(e) c\<rightarrow> s3"

  Do: "G\<turnstile>Norm s \<midarrow>Do j\<rightarrow> (Some (Jump j), s)"
   
  (* cf. 14.16 *)
  Throw: "\<lbrakk>G\<turnstile>Norm s0 \<midarrow>e-\<succ>a'\<rightarrow> s1\<rbrakk> \<Longrightarrow>
				 G\<turnstile>Norm s0 \<midarrow>Throw e\<rightarrow> abupd (throw a') s1"

  (* cf. 14.18.1 *)
  Try:	"\<lbrakk>G\<turnstile>Norm s0 \<midarrow>c1\<rightarrow> s1; G\<turnstile>s1 \<midarrow>sxalloc\<rightarrow> s2; 
	  if G,s2\<turnstile>catch C then G\<turnstile>new_xcpt_var vn s2 \<midarrow>c2\<rightarrow> s3 else s3 = s2\<rbrakk> \<Longrightarrow>
		  G\<turnstile>Norm s0 \<midarrow>Try c1 Catch(C vn) c2\<rightarrow> s3"

  (* cf. 14.18.2 *)
  Fin:	"\<lbrakk>G\<turnstile>Norm s0 \<midarrow>c1\<rightarrow> (x1,s1);
	  G\<turnstile>Norm s1 \<midarrow>c2\<rightarrow> s2\<rbrakk> \<Longrightarrow>
               G\<turnstile>Norm s0 \<midarrow>c1 Finally c2\<rightarrow> abupd (abrupt_if (x1\<noteq>None) x1) s2"

  (* cf. 12.4.2, 8.5 *)
  Init:	"\<lbrakk>the (class G C) = c;
	  if inited C (globs s0) then s3 = Norm s0
	  else (G\<turnstile>Norm (init_class_obj G C s0) 
		  \<midarrow>(if C = Object then Skip else Init (super c))\<rightarrow> s1 \<and>
	       G\<turnstile>set_lvars empty s1 \<midarrow>init c\<rightarrow> s2 \<and> s3 = restore_lvars s1 s2)\<rbrakk> 
              \<Longrightarrow>
		 G\<turnstile>Norm s0 \<midarrow>Init C\<rightarrow> s3"

(* evaluation of expressions *)

  (* cf. 15.8.1, 12.4.1 *)
  NewC:	"\<lbrakk>G\<turnstile>Norm s0 \<midarrow>Init C\<rightarrow> s1;
	  G\<turnstile>     s1 \<midarrow>halloc (CInst C)\<succ>a\<rightarrow> s2\<rbrakk> \<Longrightarrow>
	                          G\<turnstile>Norm s0 \<midarrow>NewC C-\<succ>Addr a\<rightarrow> s2"

  (* cf. 15.9.1, 12.4.1 *)
  NewA:	"\<lbrakk>G\<turnstile>Norm s0 \<midarrow>init_comp_ty T\<rightarrow> s1; G\<turnstile>s1 \<midarrow>e-\<succ>i'\<rightarrow> s2; 
	  G\<turnstile>abupd (check_neg i') s2 \<midarrow>halloc (Arr T (the_Intg i'))\<succ>a\<rightarrow> s3\<rbrakk> \<Longrightarrow>
	                        G\<turnstile>Norm s0 \<midarrow>New T[e]-\<succ>Addr a\<rightarrow> s3"

  (* cf. 15.15 *)
  Cast:	"\<lbrakk>G\<turnstile>Norm s0 \<midarrow>e-\<succ>v\<rightarrow> s1;
	  s2 = abupd (raise_if (\<not>G,store s1\<turnstile>v fits T) ClassCast) s1\<rbrakk> \<Longrightarrow>
			        G\<turnstile>Norm s0 \<midarrow>Cast T e-\<succ>v\<rightarrow> s2"

  (* cf. 15.19.2 *)
  Inst:	"\<lbrakk>G\<turnstile>Norm s0 \<midarrow>e-\<succ>v\<rightarrow> s1;
	  b = (v\<noteq>Null \<and> G,store s1\<turnstile>v fits RefT T)\<rbrakk> \<Longrightarrow>
			      G\<turnstile>Norm s0 \<midarrow>e InstOf T-\<succ>Bool b\<rightarrow> s1"

  (* cf. 15.7.1 *)
  Lit:	"G\<turnstile>Norm s \<midarrow>Lit v-\<succ>v\<rightarrow> Norm s"



  (* cf. 15.10.2 *)
  Super: "G\<turnstile>Norm s \<midarrow>Super-\<succ>val_this s\<rightarrow> Norm s"

  (* cf. 15.2 *)
  Acc:	"\<lbrakk>G\<turnstile>Norm s0 \<midarrow>va=\<succ>(v,f)\<rightarrow> s1\<rbrakk> \<Longrightarrow>
	                          G\<turnstile>Norm s0 \<midarrow>Acc va-\<succ>v\<rightarrow> s1"

  (* cf. 15.25.1 *)
  Ass:	"\<lbrakk>G\<turnstile>Norm s0 \<midarrow>va=\<succ>(w,f)\<rightarrow> s1;
          G\<turnstile>     s1 \<midarrow>e-\<succ>v  \<rightarrow> s2\<rbrakk> \<Longrightarrow>
				   G\<turnstile>Norm s0 \<midarrow>va:=e-\<succ>v\<rightarrow> assign f v s2"

  (* cf. 15.24 *)
  Cond:	"\<lbrakk>G\<turnstile>Norm s0 \<midarrow>e0-\<succ>b\<rightarrow> s1;
          G\<turnstile>     s1 \<midarrow>(if the_Bool b then e1 else e2)-\<succ>v\<rightarrow> s2\<rbrakk> \<Longrightarrow>
			    G\<turnstile>Norm s0 \<midarrow>e0 ? e1 : e2-\<succ>v\<rightarrow> s2"


  (* cf. 15.11.4.1, 15.11.4.2, 15.11.4.4, 15.11.4.5 *)
  Call:	
  "\<lbrakk>G\<turnstile>Norm s0 \<midarrow>e-\<succ>a'\<rightarrow> s1; G\<turnstile>s1 \<midarrow>args\<doteq>\<succ>vs\<rightarrow> s2;
    D = invocation_declclass G mode (store s2) a' statT \<lparr>name=mn,parTs=pTs\<rparr>;
    G\<turnstile>init_lvars G D \<lparr>name=mn,parTs=pTs\<rparr> mode a' vs s2 
         \<midarrow>Methd D \<lparr>name=mn,parTs=pTs\<rparr>-\<succ>v\<rightarrow> s3\<rbrakk>
   \<Longrightarrow>
       G\<turnstile>Norm s0 \<midarrow>{statT,mode}e\<cdot>mn({pTs}args)-\<succ>v\<rightarrow> (restore_lvars s2 s3)"

  Methd:	"\<lbrakk>G\<turnstile>Norm s0 \<midarrow>body G D sig-\<succ>v\<rightarrow> s1\<rbrakk> \<Longrightarrow>
				G\<turnstile>Norm s0 \<midarrow>Methd D sig-\<succ>v\<rightarrow> s1"

  (* cf. 14.15, 12.4.1 *)
  Body:	"\<lbrakk>G\<turnstile>Norm s0 \<midarrow>Init D\<rightarrow> s1; G\<turnstile>s1 \<midarrow>c\<rightarrow> s2\<rbrakk> \<Longrightarrow>
 G\<turnstile>Norm s0 \<midarrow>Body D c -\<succ>the (locals (store s2) Result)\<rightarrow>abupd (absorb Ret) s2"

(* evaluation of variables *)

  (* cf. 15.13.1, 15.7.2 *)
  LVar:	"G\<turnstile>Norm s \<midarrow>LVar vn=\<succ>lvar vn s\<rightarrow> Norm s"

  (* cf. 15.10.1, 12.4.1 *)
  FVar:	"\<lbrakk>G\<turnstile>Norm s0 \<midarrow>Init C\<rightarrow> s1; G\<turnstile>s1 \<midarrow>e-\<succ>a\<rightarrow> s2;
	  (v,s2') = fvar C stat fn a s2\<rbrakk> \<Longrightarrow>
	  G\<turnstile>Norm s0 \<midarrow>{C,stat}e..fn=\<succ>v\<rightarrow> s2'"

  (* cf. 15.12.1, 15.25.1 *)
  AVar:	"\<lbrakk>G\<turnstile> Norm s0 \<midarrow>e1-\<succ>a\<rightarrow> s1; G\<turnstile>s1 \<midarrow>e2-\<succ>i\<rightarrow> s2;
	  (v,s2') = avar G i a s2\<rbrakk> \<Longrightarrow>
	              G\<turnstile>Norm s0 \<midarrow>e1.[e2]=\<succ>v\<rightarrow> s2'"


(* evaluation of expression lists *)

  (* cf. 15.11.4.2 *)
  Nil:
				    "G\<turnstile>Norm s0 \<midarrow>[]\<doteq>\<succ>[]\<rightarrow> Norm s0"

  (* cf. 15.6.4 *)
  Cons:	"\<lbrakk>G\<turnstile>Norm s0 \<midarrow>e -\<succ> v \<rightarrow> s1;
          G\<turnstile>     s1 \<midarrow>es\<doteq>\<succ>vs\<rightarrow> s2\<rbrakk> \<Longrightarrow>
				   G\<turnstile>Norm s0 \<midarrow>e#es\<doteq>\<succ>v#vs\<rightarrow> s2"

(* Rearrangement of premisses:
[0,1(Abrupt),2(Skip),8(Do),4(Lab),28(Nil),29(Cons),25(LVar),15(Cast),16(Inst),
 17(Lit),18(Super),19(Acc),3(Expr),5(Comp),23(Methd),24(Body),21(Cond),6(If),
 7(Loop),11(Fin),9(Throw),13(NewC),14(NewA),12(Init),20(Ass),10(Try),26(FVar),
 27(AVar),22(Call)]
*)
ML {*
bind_thm ("eval_induct_", rearrange_prems 
[0,1,2,8,4,28,29,25,15,16,
 17,18,19,3,5,23,24,21,6,
 7,11,9,13,14,12,20,10,26,
 27,22] (thm "eval.induct"))
*}

lemmas eval_induct = eval_induct_ [split_format and and and and and and and and
   and and and and s1 (* Acc *) and and s2 (* Comp *) and and and and and and 
   s2 (* Fin *) and and s2 (* NewC *)] 

declare split_if     [split del] split_if_asm     [split del] 
        option.split [split del] option.split_asm [split del]
inductive_cases halloc_elim_cases: 
  "G\<turnstile>(Some xc,s) \<midarrow>halloc oi\<succ>a\<rightarrow> s'"
  "G\<turnstile>(Norm    s) \<midarrow>halloc oi\<succ>a\<rightarrow> s'"

inductive_cases sxalloc_elim_cases:
 	"G\<turnstile> Norm                 s  \<midarrow>sxalloc\<rightarrow> s'"
 	"G\<turnstile>(Some (Xcpt (Loc a )),s) \<midarrow>sxalloc\<rightarrow> s'"
 	"G\<turnstile>(Some (Xcpt (Std xn)),s) \<midarrow>sxalloc\<rightarrow> s'"
inductive_cases sxalloc_cases: "G\<turnstile>s \<midarrow>sxalloc\<rightarrow> s'"

lemma sxalloc_elim_cases2: "\<lbrakk>G\<turnstile>s \<midarrow>sxalloc\<rightarrow> s';  
       \<And>s.   \<lbrakk>s' = Norm s\<rbrakk> \<Longrightarrow> P;  
       \<And>a s. \<lbrakk>s' = (Some (Xcpt (Loc a)),s)\<rbrakk> \<Longrightarrow> P  
      \<rbrakk> \<Longrightarrow> P"
apply cut_tac 
apply (erule sxalloc_cases)
apply blast+
done

declare not_None_eq [simp del] (* IntDef.Zero_def [simp del] *)
declare split_paired_All [simp del] split_paired_Ex [simp del]
ML_setup {*
simpset_ref() := simpset() delloop "split_all_tac"
*}
inductive_cases eval_cases: "G\<turnstile>s \<midarrow>t\<succ>\<rightarrow> vs'"

inductive_cases eval_elim_cases:
        "G\<turnstile>(Some xc,s) \<midarrow>t                         \<succ>\<rightarrow> vs'"
	"G\<turnstile>Norm s \<midarrow>In1r Skip                      \<succ>\<rightarrow> xs'"
        "G\<turnstile>Norm s \<midarrow>In1r (Do j)                    \<succ>\<rightarrow> xs'"
        "G\<turnstile>Norm s \<midarrow>In1r (l\<bullet> c)                    \<succ>\<rightarrow> xs'"
	"G\<turnstile>Norm s \<midarrow>In3  ([])                      \<succ>\<rightarrow> vs'"
	"G\<turnstile>Norm s \<midarrow>In3  (e#es)                    \<succ>\<rightarrow> vs'"
	"G\<turnstile>Norm s \<midarrow>In1l (Lit w)                   \<succ>\<rightarrow> vs'"
	"G\<turnstile>Norm s \<midarrow>In2  (LVar vn)                 \<succ>\<rightarrow> vs'"
	"G\<turnstile>Norm s \<midarrow>In1l (Cast T e)                \<succ>\<rightarrow> vs'"
	"G\<turnstile>Norm s \<midarrow>In1l (e InstOf T)              \<succ>\<rightarrow> vs'"
	"G\<turnstile>Norm s \<midarrow>In1l (Super)                   \<succ>\<rightarrow> vs'"
	"G\<turnstile>Norm s \<midarrow>In1l (Acc va)                  \<succ>\<rightarrow> vs'"
	"G\<turnstile>Norm s \<midarrow>In1r (Expr e)                  \<succ>\<rightarrow> xs'"
	"G\<turnstile>Norm s \<midarrow>In1r (c1;; c2)                 \<succ>\<rightarrow> xs'"
	"G\<turnstile>Norm s \<midarrow>In1l (Methd C sig)             \<succ>\<rightarrow> xs'"
	"G\<turnstile>Norm s \<midarrow>In1l (Body D c)                \<succ>\<rightarrow> xs'"
	"G\<turnstile>Norm s \<midarrow>In1l (e0 ? e1 : e2)            \<succ>\<rightarrow> vs'"
	"G\<turnstile>Norm s \<midarrow>In1r (If(e) c1 Else c2)        \<succ>\<rightarrow> xs'"
	"G\<turnstile>Norm s \<midarrow>In1r (l\<bullet> While(e) c)           \<succ>\<rightarrow> xs'"
	"G\<turnstile>Norm s \<midarrow>In1r (c1 Finally c2)           \<succ>\<rightarrow> xs'"
	"G\<turnstile>Norm s \<midarrow>In1r (Throw e)                 \<succ>\<rightarrow> xs'"
	"G\<turnstile>Norm s \<midarrow>In1l (NewC C)                  \<succ>\<rightarrow> vs'"
	"G\<turnstile>Norm s \<midarrow>In1l (New T[e])                \<succ>\<rightarrow> vs'"
	"G\<turnstile>Norm s \<midarrow>In1l (Ass va e)                \<succ>\<rightarrow> vs'"
	"G\<turnstile>Norm s \<midarrow>In1r (Try c1 Catch(tn vn) c2)  \<succ>\<rightarrow> xs'"
	"G\<turnstile>Norm s \<midarrow>In2  ({C,stat}e..fn)           \<succ>\<rightarrow> vs'"
	"G\<turnstile>Norm s \<midarrow>In2  (e1.[e2])                 \<succ>\<rightarrow> vs'"
	"G\<turnstile>Norm s \<midarrow>In1l ({statT,mode}e\<cdot>mn({pT}p)) \<succ>\<rightarrow> vs'"
	"G\<turnstile>Norm s \<midarrow>In1r (Init C)                  \<succ>\<rightarrow> xs'"
declare not_None_eq [simp]  (* IntDef.Zero_def [simp] *)
declare split_paired_All [simp] split_paired_Ex [simp]
ML_setup {*
simpset_ref() := simpset() addloop ("split_all_tac", split_all_tac)
*}
declare split_if     [split] split_if_asm     [split] 
        option.split [split] option.split_asm [split]

lemma eval_Inj_elim: 
 "G\<turnstile>s \<midarrow>t\<succ>\<rightarrow> (w,s') 
 \<Longrightarrow> case t of 
       In1 ec \<Rightarrow> (case ec of 
                    Inl e \<Rightarrow> (\<exists>v. w = In1 v) 
                  | Inr c \<Rightarrow> w = \<diamondsuit>)  
     | In2 e \<Rightarrow> (\<exists>v. w = In2 v) 
     | In3 e \<Rightarrow> (\<exists>v. w = In3 v)"
apply (erule eval_cases)
apply auto
apply (induct_tac "t")
apply (induct_tac "a")
apply auto
done

ML_setup {*
fun eval_fun nam inj rhs =
let
  val name = "eval_" ^ nam ^ "_eq"
  val lhs = "G\<turnstile>s \<midarrow>" ^ inj ^ " t\<succ>\<rightarrow> (w, s')"
  val () = qed_goal name (the_context()) (lhs ^ " = (" ^ rhs ^ ")") 
	(K [Auto_tac, ALLGOALS (ftac (thm "eval_Inj_elim")) THEN Auto_tac])
  fun is_Inj (Const (inj,_) $ _) = true
    | is_Inj _                   = false
  fun pred (_ $ (Const ("Pair",_) $ _ $ 
      (Const ("Pair", _) $ _ $ (Const ("Pair", _) $ x $ _ ))) $ _ ) = is_Inj x
in
  make_simproc name lhs pred (thm name)
end

val eval_expr_proc =eval_fun "expr" "In1l" "\<exists>v.  w=In1 v   \<and> G\<turnstile>s \<midarrow>t-\<succ>v \<rightarrow> s'"
val eval_var_proc  =eval_fun "var"  "In2"  "\<exists>vf. w=In2 vf  \<and> G\<turnstile>s \<midarrow>t=\<succ>vf\<rightarrow> s'"
val eval_exprs_proc=eval_fun "exprs""In3"  "\<exists>vs. w=In3 vs  \<and> G\<turnstile>s \<midarrow>t\<doteq>\<succ>vs\<rightarrow> s'"
val eval_stmt_proc =eval_fun "stmt" "In1r" "     w=\<diamondsuit> \<and> G\<turnstile>s \<midarrow>t    \<rightarrow> s'";
Addsimprocs [eval_expr_proc,eval_var_proc,eval_exprs_proc,eval_stmt_proc];
bind_thms ("AbruptIs", sum3_instantiate (thm "eval.Abrupt"))
*}

declare halloc.Abrupt [intro!] eval.Abrupt [intro!]  AbruptIs [intro!] 


lemma eval_no_abrupt_lemma: 
   "\<And>s s'. G\<turnstile>s \<midarrow>t\<succ>\<rightarrow> (w,s') \<Longrightarrow> normal s' \<longrightarrow> normal s"
by (erule eval_cases, auto)

lemma eval_no_abrupt: 
  "G\<turnstile>(x,s) \<midarrow>t\<succ>\<rightarrow> (w,Norm s') = 
        (x = None \<and> G\<turnstile>Norm s \<midarrow>t\<succ>\<rightarrow> (w,Norm s'))"
apply auto
apply (frule eval_no_abrupt_lemma, auto)+
done

ML {*
local
  fun is_None (Const ("Datatype.option.None",_)) = true
    | is_None _ = false
  fun pred (t as (_ $ (Const ("Pair",_) $
     (Const ("Pair", _) $ x $ _) $ _ ) $ _)) = is_None x
in
  val eval_no_abrupt_proc = 
  make_simproc "eval_no_abrupt" "G\<turnstile>(x,s) \<midarrow>e\<succ>\<rightarrow> (w,Norm s')" pred 
          (thm "eval_no_abrupt")
end;
Addsimprocs [eval_no_abrupt_proc]
*}


lemma eval_abrupt_lemma: 
  "G\<turnstile>s \<midarrow>t\<succ>\<rightarrow> (v,s') \<Longrightarrow> abrupt s=Some xc \<longrightarrow> s'= s \<and> v = arbitrary3 t"
by (erule eval_cases, auto)

lemma eval_abrupt: 
 " G\<turnstile>(Some xc,s) \<midarrow>t\<succ>\<rightarrow> (w,s') =  
     (s'=(Some xc,s) \<and> w=arbitrary3 t \<and> 
     G\<turnstile>(Some xc,s) \<midarrow>t\<succ>\<rightarrow> (arbitrary3 t,(Some xc,s)))"
apply auto
apply (frule eval_abrupt_lemma, auto)+
done

ML {*
local
  fun is_Some (Const ("Pair",_) $ (Const ("Datatype.option.Some",_) $ _)$ _) =true
    | is_Some _ = false
  fun pred (_ $ (Const ("Pair",_) $
     _ $ (Const ("Pair", _) $ _ $ (Const ("Pair", _) $ _ $
       x))) $ _ ) = is_Some x
in
  val eval_abrupt_proc = 
  make_simproc "eval_abrupt" 
               "G\<turnstile>(Some xc,s) \<midarrow>e\<succ>\<rightarrow> (w,s')" pred (thm "eval_abrupt")
end;
Addsimprocs [eval_abrupt_proc]
*}


lemma LitI: "G\<turnstile>s \<midarrow>Lit v-\<succ>(if normal s then v else arbitrary)\<rightarrow> s"
apply (case_tac "s", case_tac "a = None")
by (auto intro!: eval.Lit)

lemma SkipI [intro!]: "G\<turnstile>s \<midarrow>Skip\<rightarrow> s"
apply (case_tac "s", case_tac "a = None")
by (auto intro!: eval.Skip)

lemma ExprI: "G\<turnstile>s \<midarrow>e-\<succ>v\<rightarrow> s' \<Longrightarrow> G\<turnstile>s \<midarrow>Expr e\<rightarrow> s'"
apply (case_tac "s", case_tac "a = None")
by (auto intro!: eval.Expr)

lemma CompI: "\<lbrakk>G\<turnstile>s \<midarrow>c1\<rightarrow> s1; G\<turnstile>s1 \<midarrow>c2\<rightarrow> s2\<rbrakk> \<Longrightarrow> G\<turnstile>s \<midarrow>c1;; c2\<rightarrow> s2"
apply (case_tac "s", case_tac "a = None")
by (auto intro!: eval.Comp)

lemma CondI: 
  "\<And>s1. \<lbrakk>G\<turnstile>s \<midarrow>e-\<succ>b\<rightarrow> s1; G\<turnstile>s1 \<midarrow>(if the_Bool b then e1 else e2)-\<succ>v\<rightarrow> s2\<rbrakk> \<Longrightarrow> 
         G\<turnstile>s \<midarrow>e ? e1 : e2-\<succ>(if normal s1 then v else arbitrary)\<rightarrow> s2"
apply (case_tac "s", case_tac "a = None")
by (auto intro!: eval.Cond)

lemma IfI: "\<lbrakk>G\<turnstile>s \<midarrow>e-\<succ>v\<rightarrow> s1; G\<turnstile>s1 \<midarrow>(if the_Bool v then c1 else c2)\<rightarrow> s2\<rbrakk>
                 \<Longrightarrow> G\<turnstile>s \<midarrow>If(e) c1 Else c2\<rightarrow> s2"
apply (case_tac "s", case_tac "a = None")
by (auto intro!: eval.If)

lemma MethdI: "G\<turnstile>s \<midarrow>body G C sig-\<succ>v\<rightarrow> s' \<Longrightarrow> G\<turnstile>s \<midarrow>Methd C sig-\<succ>v\<rightarrow> s'"
apply (case_tac "s", case_tac "a = None")
by (auto intro!: eval.Methd)

lemma eval_Call: "\<lbrakk>G\<turnstile>Norm s0 \<midarrow>e-\<succ>a'\<rightarrow> s1; G\<turnstile>s1 \<midarrow>ps\<doteq>\<succ>pvs\<rightarrow> s2;  
       D = invocation_declclass G mode (store s2) a' statT \<lparr>name=mn,parTs=pTs\<rparr>; 
       G\<turnstile>init_lvars G D \<lparr>name=mn,parTs=pTs\<rparr> mode a' pvs s2 
        \<midarrow>Methd D \<lparr>name=mn,parTs=pTs\<rparr>-\<succ> v\<rightarrow> s3; 
       s3' = restore_lvars s2 s3\<rbrakk> \<Longrightarrow>  
       G\<turnstile>Norm s0 \<midarrow>{statT,mode}e\<cdot>mn({pTs}ps)-\<succ>v\<rightarrow> s3'"
apply (drule eval.Call, assumption)
apply (rule HOL.refl)
apply simp+
done

lemma eval_Init: 
"\<lbrakk>if inited C (globs s0) then s3 = Norm s0 
  else G\<turnstile>Norm (init_class_obj G C s0)  
         \<midarrow>(if C = Object then Skip else Init (super (the (class G C))))\<rightarrow> s1 \<and>
       G\<turnstile>set_lvars empty s1 \<midarrow>(init (the (class G C)))\<rightarrow> s2 \<and> 
      s3 = restore_lvars s1 s2\<rbrakk> \<Longrightarrow>  
  G\<turnstile>Norm s0 \<midarrow>Init C\<rightarrow> s3"
apply (rule eval.Init)
apply auto
done

lemma init_done: "initd C s \<Longrightarrow> G\<turnstile>s \<midarrow>Init C\<rightarrow> s"
apply (case_tac "s", simp)
apply (case_tac "a")
apply  safe
apply (rule eval_Init)
apply   auto
done

lemma eval_StatRef: 
"G\<turnstile>s \<midarrow>StatRef rt-\<succ>(if abrupt s=None then Null else arbitrary)\<rightarrow> s"
apply (case_tac "s", simp)
apply (case_tac "a = None")
apply (auto del: eval.Abrupt intro!: eval.intros)
done


lemma SkipD [dest!]: "G\<turnstile>s \<midarrow>Skip\<rightarrow> s' \<Longrightarrow> s' = s" 
apply (erule eval_cases)
by auto

lemma Skip_eq [simp]: "G\<turnstile>s \<midarrow>Skip\<rightarrow> s' = (s = s')"
by auto

(*unused*)
lemma init_retains_locals [rule_format (no_asm)]: "G\<turnstile>s \<midarrow>t\<succ>\<rightarrow> (w,s') \<Longrightarrow>  
  (\<forall>C. t=In1r (Init C) \<longrightarrow> locals (store s) = locals (store s'))"
apply (erule eval.induct)
apply (simp (no_asm_use) split del: split_if_asm option.split_asm)+
apply auto
done

lemma halloc_xcpt [dest!]: 
  "\<And>s'. G\<turnstile>(Some xc,s) \<midarrow>halloc oi\<succ>a\<rightarrow> s' \<Longrightarrow> s'=(Some xc,s)"
apply (erule_tac halloc_elim_cases)
by auto

(*
G\<turnstile>(x,(h,l)) \<midarrow>e\<succ>v\<rightarrow> (x',(h',l'))) \<Longrightarrow> l This = l' This"
G\<turnstile>(x,(h,l)) \<midarrow>s  \<rightarrow> (x',(h',l'))) \<Longrightarrow> l This = l' This"
*)

lemma eval_Methd: 
  "G\<turnstile>s \<midarrow>In1l(body G C sig)\<succ>\<rightarrow> (w,s') \<Longrightarrow> G\<turnstile>s \<midarrow>In1l(Methd C sig)\<succ>\<rightarrow> (w,s')"
apply (case_tac "s")
apply (case_tac "a")
apply clarsimp+
apply (erule eval.Methd)
apply (drule eval_abrupt_lemma)
apply force
done


section "single valued"

lemma unique_halloc [rule_format (no_asm)]: 
  "\<And>s as as'. (s,oi,as)\<in>halloc G \<Longrightarrow> (s,oi,as')\<in>halloc G \<longrightarrow> as'=as"
apply (simp (no_asm_simp) only: split_tupled_all)
apply (erule halloc.induct)
apply  (auto elim!: halloc_elim_cases split del: split_if split_if_asm)
apply (drule trans [THEN sym], erule sym) 
defer
apply (drule trans [THEN sym], erule sym)
apply auto
done


lemma single_valued_halloc: 
  "single_valued {((s,oi),(a,s')). G\<turnstile>s \<midarrow>halloc oi\<succ>a \<rightarrow> s'}"
apply (unfold single_valued_def)
by (clarsimp, drule (1) unique_halloc, auto)


lemma unique_sxalloc [rule_format (no_asm)]: 
  "\<And>s s'. G\<turnstile>s \<midarrow>sxalloc\<rightarrow> s' \<Longrightarrow> G\<turnstile>s \<midarrow>sxalloc\<rightarrow> s'' \<longrightarrow> s'' = s'"
apply (simp (no_asm_simp) only: split_tupled_all)
apply (erule sxalloc.induct)
apply   (auto dest: unique_halloc elim!: sxalloc_elim_cases 
              split del: split_if split_if_asm)
done

lemma single_valued_sxalloc: "single_valued {(s,s'). G\<turnstile>s \<midarrow>sxalloc\<rightarrow> s'}"
apply (unfold single_valued_def)
apply (blast dest: unique_sxalloc)
done

lemma split_pairD: "(x,y) = p \<Longrightarrow> x = fst p & y = snd p"
by auto

lemma unique_eval [rule_format (no_asm)]: 
  "G\<turnstile>s \<midarrow>t\<succ>\<rightarrow> ws \<Longrightarrow> (\<forall>ws'. G\<turnstile>s \<midarrow>t\<succ>\<rightarrow> ws' \<longrightarrow> ws' = ws)"
apply (case_tac "ws")
apply (simp only:)
apply (erule thin_rl)
apply (erule eval_induct)
apply (tactic {* ALLGOALS (EVERY'
      [strip_tac, rotate_tac ~1, eresolve_tac (thms "eval_elim_cases")]) *})
(* 29 subgoals *)
prefer 26 (* Try *) 
apply (simp (no_asm_use) only: split add: split_if_asm)
(* 32 subgoals *)
prefer 28 (* Init *)
apply (case_tac "inited C (globs s0)", (simp only: if_True if_False)+)
prefer 24 (* While *)
apply (simp (no_asm_use) only: split add: split_if_asm, blast)
apply (drule_tac x="(In1 bb, s1a)" in spec, drule (1) mp, simp)
apply (drule_tac x="(In1 bb, s1a)" in spec, drule (1) mp, simp)
apply blast
(* 31 subgoals *)
apply (blast dest: unique_sxalloc unique_halloc split_pairD)+
done

(* unused *)
lemma single_valued_eval: 
 "single_valued {((s,t),vs'). G\<turnstile>s \<midarrow>t\<succ>\<rightarrow> vs'}"
apply (unfold single_valued_def)
by (clarify, drule (1) unique_eval, auto)

end
