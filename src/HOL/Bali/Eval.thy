(*  Title:      HOL/Bali/Eval.thy
    Author:     David von Oheimb
*)
subsection \<open>Operational evaluation (big-step) semantics of Java expressions and 
          statements
\<close>

theory Eval imports State DeclConcepts begin

text \<open>

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
  inclusion helps to make the rule structure independent of exception occurrence.
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
  e.g. \<open>the_Addr (Val (Bool b)) = undefined\<close>.
  \begin{itemize}
  \item[++] fewer rules 
  \item[-]  less readable because of auxiliary functions like \<open>the_Addr\<close>
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
\item unfortunately \<open>new_Addr\<close> is not directly executable because of 
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
\<close>


type_synonym vvar = "val \<times> (val \<Rightarrow> state \<Rightarrow> state)"
type_synonym vals = "(val, vvar, val list) sum3"
translations
  (type) "vvar" <= (type) "val \<times> (val \<Rightarrow> state \<Rightarrow> state)"
  (type) "vals" <= (type) "(val, vvar, val list) sum3" 

text \<open>To avoid redundancy and to reduce the number of rules, there is only 
 one evaluation rule for each syntactic term. This is also true for variables
 (e.g. see the rules below for \<open>LVar\<close>, \<open>FVar\<close> and \<open>AVar\<close>). 
 So evaluation of a variable must capture both possible further uses: 
 read (rule \<open>Acc\<close>) or write (rule \<open>Ass\<close>) to the variable. 
 Therefor a variable evaluates to a special value \<^term>\<open>vvar\<close>, which is 
 a pair, consisting of the current value (for later read access) and an update 
 function (for later write access). Because
 during assignment to an array variable an exception may occur if the types
 don't match, the update function is very generic: it transforms the 
 full state. This generic update function causes some technical trouble during
 some proofs (e.g. type safety, correctness of definite assignment). There we
 need to prove some additional invariant on this update function to prove the
 assignment correct, since the update function could potentially alter the whole
 state in an arbitrary manner. This invariant must be carried around through
 the whole induction.
 So for future approaches it may be better not to take
 such a generic update function, but only to store the address and the kind
 of variable (array (+ element type), local variable or field) for later 
 assignment. 
\<close>

abbreviation
  dummy_res :: "vals" (\<open>\<diamondsuit>\<close>)
  where "\<diamondsuit> == In1 Unit"

abbreviation (input)
  val_inj_vals (\<open>\<lfloor>_\<rfloor>\<^sub>e\<close> 1000)
  where "\<lfloor>e\<rfloor>\<^sub>e == In1 e"

abbreviation (input)
  var_inj_vals  (\<open>\<lfloor>_\<rfloor>\<^sub>v\<close> 1000)
  where "\<lfloor>v\<rfloor>\<^sub>v == In2 v"

abbreviation (input)
  lst_inj_vals  (\<open>\<lfloor>_\<rfloor>\<^sub>l\<close> 1000)
  where "\<lfloor>es\<rfloor>\<^sub>l == In3 es"

definition undefined3 :: "('al + 'ar, 'b, 'c) sum3 \<Rightarrow> vals" where
 "undefined3 = case_sum3 (In1 \<circ> case_sum (\<lambda>x. undefined) (\<lambda>x. Unit))
                     (\<lambda>x. In2 undefined) (\<lambda>x. In3 undefined)"

lemma [simp]: "undefined3 (In1l x) = In1 undefined"
by (simp add: undefined3_def)

lemma [simp]: "undefined3 (In1r x) = \<diamondsuit>"
by (simp add: undefined3_def)

lemma [simp]: "undefined3 (In2  x) = In2 undefined"
by (simp add: undefined3_def)

lemma [simp]: "undefined3 (In3  x) = In3 undefined"
by (simp add: undefined3_def)


subsubsection "exception throwing and catching"

definition
  throw :: "val \<Rightarrow> abopt \<Rightarrow> abopt" where
  "throw a' x = abrupt_if True (Some (Xcpt (Loc (the_Addr a')))) (np a' x)"

lemma throw_def2: 
 "throw a' x = abrupt_if True (Some (Xcpt (Loc (the_Addr a')))) (np a' x)"
apply (unfold throw_def)
apply (simp (no_asm))
done

definition
  fits :: "prog \<Rightarrow> st \<Rightarrow> val \<Rightarrow> ty \<Rightarrow> bool" (\<open>_,_\<turnstile>_ fits _\<close>[61,61,61,61]60)
  where "G,s\<turnstile>a' fits T = ((\<exists>rt. T=RefT rt) \<longrightarrow> a'=Null \<or> G\<turnstile>obj_ty(lookup_obj s a')\<preceq>T)"

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

definition
  catch :: "prog \<Rightarrow> state \<Rightarrow> qtname \<Rightarrow> bool" (\<open>_,_\<turnstile>catch _\<close>[61,61,61]60) where
  "G,s\<turnstile>catch C = (\<exists>xc. abrupt s=Some (Xcpt xc) \<and> 
                        G,store s\<turnstile>Addr (the_Loc xc) fits Class C)"

lemma catch_Norm [simp]: "\<not>G,Norm s\<turnstile>catch tn"
apply (unfold catch_def)
apply (simp (no_asm))
done

lemma catch_XcptLoc [simp]: 
  "G,(Some (Xcpt (Loc a)),s)\<turnstile>catch C = G,s\<turnstile>Addr a fits Class C"
apply (unfold catch_def)
apply (simp (no_asm))
done

lemma catch_Jump [simp]: "\<not>G,(Some (Jump j),s)\<turnstile>catch tn"
apply (unfold catch_def)
apply (simp (no_asm))
done

lemma catch_Error [simp]: "\<not>G,(Some (Error e),s)\<turnstile>catch tn"
apply (unfold catch_def)
apply (simp (no_asm))
done

definition
  new_xcpt_var :: "vname \<Rightarrow> state \<Rightarrow> state" where
  "new_xcpt_var vn = (\<lambda>(x,s). Norm (lupd(VName vn\<mapsto>Addr (the_Loc (the_Xcpt (the x)))) s))"

lemma new_xcpt_var_def2 [simp]: 
 "new_xcpt_var vn (x,s) = 
    Norm (lupd(VName vn\<mapsto>Addr (the_Loc (the_Xcpt (the x)))) s)"
apply (unfold new_xcpt_var_def)
apply (simp (no_asm))
done



subsubsection "misc"

definition
  assign :: "('a \<Rightarrow> state \<Rightarrow> state) \<Rightarrow> 'a \<Rightarrow> state \<Rightarrow> state" where
 "assign f v = (\<lambda>(x,s). let (x',s') = (if x = None then f v else id) (x,s)
                        in  (x',if x' = None then s' else s))"

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

lemma assign_Some1 [simp]:  "\<not> normal s \<Longrightarrow> assign f v s = s" 
by (auto simp add: assign_def Let_def split_beta)

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

definition
  init_comp_ty :: "ty \<Rightarrow> stmt"
  where "init_comp_ty T = (if (\<exists>C. T = Class C) then Init (the_Class T) else Skip)"

lemma init_comp_ty_PrimT [simp]: "init_comp_ty (PrimT pt) = Skip"
apply (unfold init_comp_ty_def)
apply (simp (no_asm))
done

definition
  invocation_class :: "inv_mode \<Rightarrow> st \<Rightarrow> val \<Rightarrow> ref_ty \<Rightarrow> qtname" where
 "invocation_class m s a' statT =
    (case m of
       Static \<Rightarrow> if (\<exists> statC. statT = ClassT statC) 
                    then the_Class (RefT statT) 
                    else Object
     | SuperM \<Rightarrow> the_Class (RefT statT)
     | IntVir \<Rightarrow> obj_class (lookup_obj s a'))"

definition
  invocation_declclass :: "prog \<Rightarrow> inv_mode \<Rightarrow> st \<Rightarrow> val \<Rightarrow> ref_ty \<Rightarrow> sig \<Rightarrow> qtname" where
  "invocation_declclass G m s a' statT sig =
    declclass (the (dynlookup G statT
                                (invocation_class m s a' statT)
                                sig))" 
  
lemma invocation_class_IntVir [simp]: 
"invocation_class IntVir s a' statT = obj_class (lookup_obj s a')"
by (simp add: invocation_class_def)

lemma dynclass_SuperM [simp]: 
 "invocation_class SuperM s a' statT = the_Class (RefT statT)"
by (simp add: invocation_class_def)

lemma invocation_class_Static [simp]: 
  "invocation_class Static s a' statT = (if (\<exists> statC. statT = ClassT statC) 
                                            then the_Class (RefT statT) 
                                            else Object)"
by (simp add: invocation_class_def)

definition
  init_lvars :: "prog \<Rightarrow> qtname \<Rightarrow> sig \<Rightarrow> inv_mode \<Rightarrow> val \<Rightarrow> val list \<Rightarrow> state \<Rightarrow> state"
where
  "init_lvars G C sig mode a' pvs =
    (\<lambda>(x,s). 
      let m = mthd (the (methd G C sig));
          l = \<lambda> k. 
              (case k of
                 EName e 
                   \<Rightarrow> (case e of 
                         VNam v \<Rightarrow> (Map.empty ((pars m)[\<mapsto>]pvs)) v
                       | Res    \<Rightarrow> None)
               | This 
                   \<Rightarrow> (if mode=Static then None else Some a'))
      in set_lvars l (if mode = Static then x else np a' x,s))"



lemma init_lvars_def2: \<comment> \<open>better suited for simplification\<close> 
"init_lvars G C sig mode a' pvs (x,s) =  
  set_lvars 
    (\<lambda> k. 
       (case k of
          EName e 
            \<Rightarrow> (case e of 
                  VNam v 
                  \<Rightarrow> (Map.empty ((pars (mthd (the (methd G C sig))))[\<mapsto>]pvs)) v
               | Res \<Rightarrow> None)
        | This 
            \<Rightarrow> (if mode=Static then None else Some a')))
    (if mode = Static then x else np a' x,s)"
apply (unfold init_lvars_def)
apply (simp (no_asm) add: Let_def)
done

definition
  body :: "prog \<Rightarrow> qtname \<Rightarrow> sig \<Rightarrow> expr" where
 "body G C sig =
    (let m = the (methd G C sig) 
     in Body (declclass m) (stmt (mbody (mthd m))))"

lemma body_def2: \<comment> \<open>better suited for simplification\<close> 
"body G C sig = Body  (declclass (the (methd G C sig))) 
                      (stmt (mbody (mthd (the (methd G C sig)))))"
apply (unfold body_def Let_def)
apply auto
done

subsubsection "variables"

definition
  lvar :: "lname \<Rightarrow> st \<Rightarrow> vvar"
  where "lvar vn s = (the (locals s vn), \<lambda>v. supd (lupd(vn\<mapsto>v)))"

definition
  fvar :: "qtname \<Rightarrow> bool \<Rightarrow> vname \<Rightarrow> val \<Rightarrow> state \<Rightarrow> vvar \<times> state" where
 "fvar C stat fn a' s =
   (let (oref,xf) = if stat then (Stat C,id)
                            else (Heap (the_Addr a'),np a');
                  n = Inl (fn,C); 
                  f = (\<lambda>v. supd (upd_gobj oref n v)) 
    in ((the (values (the (globs (store s) oref)) n),f),abupd xf s))"

definition
  avar :: "prog \<Rightarrow> val \<Rightarrow> val \<Rightarrow> state \<Rightarrow> vvar \<times> state" where
  "avar G i' a' s =
    (let   oref = Heap (the_Addr a'); 
              i = the_Intg i'; 
              n = Inr i;
       (T,k,cs) = the_Arr (globs (store s) oref); 
              f = (\<lambda>v (x,s). (raise_if (\<not>G,s\<turnstile>v fits T) 
                                           ArrStore x
                              ,upd_gobj oref n v s)) 
     in ((the (cs n),f),abupd (raise_if (\<not>i in_bounds k) IndOutBound \<circ> np a') s))"

lemma fvar_def2: \<comment> \<open>better suited for simplification\<close> 
"fvar C stat fn a' s =  
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

lemma avar_def2: \<comment> \<open>better suited for simplification\<close> 
"avar G i' a' s =  
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

definition
  check_field_access :: "prog \<Rightarrow> qtname \<Rightarrow> qtname \<Rightarrow> vname \<Rightarrow> bool \<Rightarrow> val \<Rightarrow> state \<Rightarrow> state" where
  "check_field_access G accC statDeclC fn stat a' s =
    (let oref = if stat then Stat statDeclC
                else Heap (the_Addr a');
         dynC = case oref of
                   Heap a \<Rightarrow> obj_class (the (globs (store s) oref))
                 | Stat C \<Rightarrow> C;
         f    = (the (table_of (DeclConcepts.fields G dynC) (fn,statDeclC)))
     in abupd 
        (error_if (\<not> G\<turnstile>Field fn (statDeclC,f) in dynC dyn_accessible_from accC)
                  AccessViolation)
        s)"

definition
  check_method_access :: "prog \<Rightarrow> qtname \<Rightarrow> ref_ty \<Rightarrow> inv_mode \<Rightarrow>  sig \<Rightarrow> val \<Rightarrow> state \<Rightarrow> state" where
  "check_method_access G accC statT mode sig  a' s =
    (let invC = invocation_class mode (store s) a' statT;
       dynM = the (dynlookup G statT invC sig)
     in abupd 
        (error_if (\<not> G\<turnstile>Methd sig dynM in invC dyn_accessible_from accC)
                  AccessViolation)
        s)"
       
subsubsection "evaluation judgments"

inductive
  halloc :: "[prog,state,obj_tag,loc,state]\<Rightarrow>bool" (\<open>_\<turnstile>_ \<midarrow>halloc _\<succ>_\<rightarrow> _\<close>[61,61,61,61,61]60) for G::prog
where \<comment> \<open>allocating objects on the heap, cf. 12.5\<close>

  Abrupt: 
  "G\<turnstile>(Some x,s) \<midarrow>halloc oi\<succ>undefined\<rightarrow> (Some x,s)"

| New:    "\<lbrakk>new_Addr (heap s) = Some a; 
            (x,oi') = (if atleast_free (heap s) (Suc (Suc 0)) then (None,oi)
                       else (Some (Xcpt (Loc a)),CInst (SXcpt OutOfMemory)))\<rbrakk>
            \<Longrightarrow>
            G\<turnstile>Norm s \<midarrow>halloc oi\<succ>a\<rightarrow> (x,init_obj G oi' (Heap a) s)"

inductive sxalloc :: "[prog,state,state]\<Rightarrow>bool" (\<open>_\<turnstile>_ \<midarrow>sxalloc\<rightarrow> _\<close>[61,61,61]60) for G::prog
where \<comment> \<open>allocating exception objects for
  standard exceptions (other than OutOfMemory)\<close>

  Norm:  "G\<turnstile> Norm              s   \<midarrow>sxalloc\<rightarrow>  Norm             s"

| Jmp:   "G\<turnstile>(Some (Jump j), s)  \<midarrow>sxalloc\<rightarrow> (Some (Jump j), s)"

| Error: "G\<turnstile>(Some (Error e), s)  \<midarrow>sxalloc\<rightarrow> (Some (Error e), s)"

| XcptL: "G\<turnstile>(Some (Xcpt (Loc a) ),s)  \<midarrow>sxalloc\<rightarrow> (Some (Xcpt (Loc a)),s)"

| SXcpt: "\<lbrakk>G\<turnstile>Norm s0 \<midarrow>halloc (CInst (SXcpt xn))\<succ>a\<rightarrow> (x,s1)\<rbrakk> \<Longrightarrow>
          G\<turnstile>(Some (Xcpt (Std xn)),s0) \<midarrow>sxalloc\<rightarrow> (Some (Xcpt (Loc a)),s1)"


inductive
  eval :: "[prog,state,term,vals,state]\<Rightarrow>bool" (\<open>_\<turnstile>_ \<midarrow>_\<succ>\<rightarrow> '(_, _')\<close>  [61,61,80,0,0]60)
  and exec ::"[prog,state,stmt      ,state]\<Rightarrow>bool"(\<open>_\<turnstile>_ \<midarrow>_\<rightarrow> _\<close>   [61,61,65,   61]60)
  and evar ::"[prog,state,var  ,vvar,state]\<Rightarrow>bool"(\<open>_\<turnstile>_ \<midarrow>_=\<succ>_\<rightarrow> _\<close>[61,61,90,61,61]60)
  and eval'::"[prog,state,expr ,val ,state]\<Rightarrow>bool"(\<open>_\<turnstile>_ \<midarrow>_-\<succ>_\<rightarrow> _\<close>[61,61,80,61,61]60)
  and evals::"[prog,state,expr list ,
                    val  list ,state]\<Rightarrow>bool"(\<open>_\<turnstile>_ \<midarrow>_\<doteq>\<succ>_\<rightarrow> _\<close>[61,61,61,61,61]60)
  for G::prog
where

  "G\<turnstile>s \<midarrow>c    \<rightarrow>     s' \<equiv> G\<turnstile>s \<midarrow>In1r c\<succ>\<rightarrow> (\<diamondsuit>,  s')"
| "G\<turnstile>s \<midarrow>e-\<succ>v \<rightarrow>     s' \<equiv> G\<turnstile>s \<midarrow>In1l e\<succ>\<rightarrow> (In1 v,  s')"
| "G\<turnstile>s \<midarrow>e=\<succ>vf\<rightarrow>     s' \<equiv> G\<turnstile>s \<midarrow>In2  e\<succ>\<rightarrow> (In2 vf, s')"
| "G\<turnstile>s \<midarrow>e\<doteq>\<succ>v \<rightarrow>     s' \<equiv> G\<turnstile>s \<midarrow>In3  e\<succ>\<rightarrow> (In3 v,  s')"

\<comment> \<open>propagation of abrupt completion\<close>

  \<comment> \<open>cf. 14.1, 15.5\<close>
| Abrupt: 
   "G\<turnstile>(Some xc,s) \<midarrow>t\<succ>\<rightarrow> (undefined3 t, (Some xc, s))"


\<comment> \<open>execution of statements\<close>

  \<comment> \<open>cf. 14.5\<close>
| Skip:                             "G\<turnstile>Norm s \<midarrow>Skip\<rightarrow> Norm s"

  \<comment> \<open>cf. 14.7\<close>
| Expr: "\<lbrakk>G\<turnstile>Norm s0 \<midarrow>e-\<succ>v\<rightarrow> s1\<rbrakk> \<Longrightarrow>
                                  G\<turnstile>Norm s0 \<midarrow>Expr e\<rightarrow> s1"

| Lab:  "\<lbrakk>G\<turnstile>Norm s0 \<midarrow>c \<rightarrow> s1\<rbrakk> \<Longrightarrow>
                                G\<turnstile>Norm s0 \<midarrow>l\<bullet> c\<rightarrow> abupd (absorb l) s1"
  \<comment> \<open>cf. 14.2\<close>
| Comp: "\<lbrakk>G\<turnstile>Norm s0 \<midarrow>c1 \<rightarrow> s1;
          G\<turnstile>     s1 \<midarrow>c2 \<rightarrow> s2\<rbrakk> \<Longrightarrow>
                                 G\<turnstile>Norm s0 \<midarrow>c1;; c2\<rightarrow> s2"

  \<comment> \<open>cf. 14.8.2\<close>
| If:   "\<lbrakk>G\<turnstile>Norm s0 \<midarrow>e-\<succ>b\<rightarrow> s1;
          G\<turnstile>     s1\<midarrow>(if the_Bool b then c1 else c2)\<rightarrow> s2\<rbrakk> \<Longrightarrow>
                       G\<turnstile>Norm s0 \<midarrow>If(e) c1 Else c2 \<rightarrow> s2"

  \<comment> \<open>cf. 14.10, 14.10.1\<close>
  
  \<comment> \<open>A continue jump from the while body \<^term>\<open>c\<close> is handled by 
     this rule. If a continue jump with the proper label was invoked inside 
     \<^term>\<open>c\<close> this label (Cont l) is deleted out of the abrupt component of 
     the state before the iterative evaluation of the while statement.
     A break jump is handled by the Lab Statement \<open>Lab l (while\<dots>)\<close>.\<close>
| Loop: "\<lbrakk>G\<turnstile>Norm s0 \<midarrow>e-\<succ>b\<rightarrow> s1;
          if the_Bool b 
             then (G\<turnstile>s1 \<midarrow>c\<rightarrow> s2 \<and> 
                   G\<turnstile>(abupd (absorb (Cont l)) s2) \<midarrow>l\<bullet> While(e) c\<rightarrow> s3)
             else s3 = s1\<rbrakk> \<Longrightarrow>
                              G\<turnstile>Norm s0 \<midarrow>l\<bullet> While(e) c\<rightarrow> s3"

| Jmp: "G\<turnstile>Norm s \<midarrow>Jmp j\<rightarrow> (Some (Jump j), s)"
   
  \<comment> \<open>cf. 14.16\<close>
| Throw: "\<lbrakk>G\<turnstile>Norm s0 \<midarrow>e-\<succ>a'\<rightarrow> s1\<rbrakk> \<Longrightarrow>
                                 G\<turnstile>Norm s0 \<midarrow>Throw e\<rightarrow> abupd (throw a') s1"

  \<comment> \<open>cf. 14.18.1\<close>
| Try:  "\<lbrakk>G\<turnstile>Norm s0 \<midarrow>c1\<rightarrow> s1; G\<turnstile>s1 \<midarrow>sxalloc\<rightarrow> s2; 
          if G,s2\<turnstile>catch C then G\<turnstile>new_xcpt_var vn s2 \<midarrow>c2\<rightarrow> s3 else s3 = s2\<rbrakk> \<Longrightarrow>
                  G\<turnstile>Norm s0 \<midarrow>Try c1 Catch(C vn) c2\<rightarrow> s3"

  \<comment> \<open>cf. 14.18.2\<close>
| Fin:  "\<lbrakk>G\<turnstile>Norm s0 \<midarrow>c1\<rightarrow> (x1,s1);
          G\<turnstile>Norm s1 \<midarrow>c2\<rightarrow> s2;
          s3=(if (\<exists> err. x1=Some (Error err)) 
              then (x1,s1) 
              else abupd (abrupt_if (x1\<noteq>None) x1) s2) \<rbrakk> 
          \<Longrightarrow>
          G\<turnstile>Norm s0 \<midarrow>c1 Finally c2\<rightarrow> s3"
  \<comment> \<open>cf. 12.4.2, 8.5\<close>
| Init: "\<lbrakk>the (class G C) = c;
          if inited C (globs s0) then s3 = Norm s0
          else (G\<turnstile>Norm (init_class_obj G C s0) 
                  \<midarrow>(if C = Object then Skip else Init (super c))\<rightarrow> s1 \<and>
               G\<turnstile>set_lvars Map.empty s1 \<midarrow>init c\<rightarrow> s2 \<and> s3 = restore_lvars s1 s2)\<rbrakk> 
              \<Longrightarrow>
                 G\<turnstile>Norm s0 \<midarrow>Init C\<rightarrow> s3"
   \<comment> \<open>This class initialisation rule is a little bit inaccurate. Look at the
      exact sequence:
      (1) The current class object (the static fields) are initialised
           (\<open>init_class_obj\<close>),
      (2) the superclasses are initialised,
      (3) the static initialiser of the current class is invoked.
      More precisely we should expect another ordering, namely 2 1 3.
      But we can't just naively toggle 1 and 2. By calling 
      \<open>init_class_obj\<close> 
      before initialising the superclasses, we also implicitly record that
      we have started to initialise the current class (by setting an 
      value for the class object). This becomes 
      crucial for the completeness proof of the axiomatic semantics 
      \<open>AxCompl.thy\<close>. Static initialisation requires an induction on 
      the number of classes not yet initialised (or to be more precise, 
      classes were the initialisation has not yet begun). 
      So we could first assign a dummy value to the class before
      superclass initialisation and afterwards set the correct values.
      But as long as we don't take memory overflow into account 
      when allocating class objects, we can leave things as they are for 
      convenience.\<close>
\<comment> \<open>evaluation of expressions\<close>

  \<comment> \<open>cf. 15.8.1, 12.4.1\<close>
| NewC: "\<lbrakk>G\<turnstile>Norm s0 \<midarrow>Init C\<rightarrow> s1;
          G\<turnstile>     s1 \<midarrow>halloc (CInst C)\<succ>a\<rightarrow> s2\<rbrakk> \<Longrightarrow>
                                  G\<turnstile>Norm s0 \<midarrow>NewC C-\<succ>Addr a\<rightarrow> s2"

  \<comment> \<open>cf. 15.9.1, 12.4.1\<close>
| NewA: "\<lbrakk>G\<turnstile>Norm s0 \<midarrow>init_comp_ty T\<rightarrow> s1; G\<turnstile>s1 \<midarrow>e-\<succ>i'\<rightarrow> s2; 
          G\<turnstile>abupd (check_neg i') s2 \<midarrow>halloc (Arr T (the_Intg i'))\<succ>a\<rightarrow> s3\<rbrakk> \<Longrightarrow>
                                G\<turnstile>Norm s0 \<midarrow>New T[e]-\<succ>Addr a\<rightarrow> s3"

  \<comment> \<open>cf. 15.15\<close>
| Cast: "\<lbrakk>G\<turnstile>Norm s0 \<midarrow>e-\<succ>v\<rightarrow> s1;
          s2 = abupd (raise_if (\<not>G,store s1\<turnstile>v fits T) ClassCast) s1\<rbrakk> \<Longrightarrow>
                                G\<turnstile>Norm s0 \<midarrow>Cast T e-\<succ>v\<rightarrow> s2"

  \<comment> \<open>cf. 15.19.2\<close>
| Inst: "\<lbrakk>G\<turnstile>Norm s0 \<midarrow>e-\<succ>v\<rightarrow> s1;
          b = (v\<noteq>Null \<and> G,store s1\<turnstile>v fits RefT T)\<rbrakk> \<Longrightarrow>
                              G\<turnstile>Norm s0 \<midarrow>e InstOf T-\<succ>Bool b\<rightarrow> s1"

  \<comment> \<open>cf. 15.7.1\<close>
| Lit:  "G\<turnstile>Norm s \<midarrow>Lit v-\<succ>v\<rightarrow> Norm s"

| UnOp: "\<lbrakk>G\<turnstile>Norm s0 \<midarrow>e-\<succ>v\<rightarrow> s1\<rbrakk> 
         \<Longrightarrow> G\<turnstile>Norm s0 \<midarrow>UnOp unop e-\<succ>(eval_unop unop v)\<rightarrow> s1"
 
| BinOp: "\<lbrakk>G\<turnstile>Norm s0 \<midarrow>e1-\<succ>v1\<rightarrow> s1; 
          G\<turnstile>s1 \<midarrow>(if need_second_arg binop v1 then (In1l e2) else (In1r Skip))
                \<succ>\<rightarrow> (In1 v2, s2)
          \<rbrakk> 
         \<Longrightarrow> G\<turnstile>Norm s0 \<midarrow>BinOp binop e1 e2-\<succ>(eval_binop binop v1 v2)\<rightarrow> s2"
   
  \<comment> \<open>cf. 15.10.2\<close>
| Super: "G\<turnstile>Norm s \<midarrow>Super-\<succ>val_this s\<rightarrow> Norm s"

  \<comment> \<open>cf. 15.2\<close>
| Acc:  "\<lbrakk>G\<turnstile>Norm s0 \<midarrow>va=\<succ>(v,f)\<rightarrow> s1\<rbrakk> \<Longrightarrow>
                                  G\<turnstile>Norm s0 \<midarrow>Acc va-\<succ>v\<rightarrow> s1"

  \<comment> \<open>cf. 15.25.1\<close>
| Ass:  "\<lbrakk>G\<turnstile>Norm s0 \<midarrow>va=\<succ>(w,f)\<rightarrow> s1;
          G\<turnstile>     s1 \<midarrow>e-\<succ>v  \<rightarrow> s2\<rbrakk> \<Longrightarrow>
                                   G\<turnstile>Norm s0 \<midarrow>va:=e-\<succ>v\<rightarrow> assign f v s2"

  \<comment> \<open>cf. 15.24\<close>
| Cond: "\<lbrakk>G\<turnstile>Norm s0 \<midarrow>e0-\<succ>b\<rightarrow> s1;
          G\<turnstile>     s1 \<midarrow>(if the_Bool b then e1 else e2)-\<succ>v\<rightarrow> s2\<rbrakk> \<Longrightarrow>
                            G\<turnstile>Norm s0 \<midarrow>e0 ? e1 : e2-\<succ>v\<rightarrow> s2"


\<comment> \<open>The interplay of  \<^term>\<open>Call\<close>, \<^term>\<open>Methd\<close> and \<^term>\<open>Body\<close>:
      Method invocation is split up into these three rules:
      \begin{itemize}
      \item [\<^term>\<open>Call\<close>] Calculates the target address and evaluates the
                           arguments of the method, and then performs dynamic
                           or static lookup of the method, corresponding to the
                           call mode. Then the \<^term>\<open>Methd\<close> rule is evaluated
                           on the calculated declaration class of the method
                           invocation.
      \item [\<^term>\<open>Methd\<close>] A syntactic bridge for the folded method body.
                            It is used by the axiomatic semantics to add the
                            proper hypothesis for recursive calls of the method.
      \item [\<^term>\<open>Body\<close>] An extra syntactic entity for the unfolded method
                           body was introduced to properly trigger class 
                           initialisation. Without class initialisation we 
                           could just evaluate the body statement. 
      \end{itemize}\<close>
  \<comment> \<open>cf. 15.11.4.1, 15.11.4.2, 15.11.4.4, 15.11.4.5\<close>
| Call: 
  "\<lbrakk>G\<turnstile>Norm s0 \<midarrow>e-\<succ>a'\<rightarrow> s1; G\<turnstile>s1 \<midarrow>args\<doteq>\<succ>vs\<rightarrow> s2;
    D = invocation_declclass G mode (store s2) a' statT \<lparr>name=mn,parTs=pTs\<rparr>;
    s3=init_lvars G D \<lparr>name=mn,parTs=pTs\<rparr> mode a' vs s2;
    s3' = check_method_access G accC statT mode \<lparr>name=mn,parTs=pTs\<rparr> a' s3;
    G\<turnstile>s3' \<midarrow>Methd D \<lparr>name=mn,parTs=pTs\<rparr>-\<succ>v\<rightarrow> s4\<rbrakk>
   \<Longrightarrow>
       G\<turnstile>Norm s0 \<midarrow>{accC,statT,mode}e\<cdot>mn({pTs}args)-\<succ>v\<rightarrow> (restore_lvars s2 s4)"
\<comment> \<open>The accessibility check is after \<^term>\<open>init_lvars\<close>, to keep it simple. 
   \<^term>\<open>init_lvars\<close> already tests for the absence of a null-pointer 
   reference in case of an instance method invocation.\<close>

| Methd:        "\<lbrakk>G\<turnstile>Norm s0 \<midarrow>body G D sig-\<succ>v\<rightarrow> s1\<rbrakk> \<Longrightarrow>
                                G\<turnstile>Norm s0 \<midarrow>Methd D sig-\<succ>v\<rightarrow> s1"
  
| Body: "\<lbrakk>G\<turnstile>Norm s0 \<midarrow>Init D\<rightarrow> s1; G\<turnstile>s1 \<midarrow>c\<rightarrow> s2; 
          s3 = (if (\<exists> l. abrupt s2 = Some (Jump (Break l)) \<or>  
                         abrupt s2 = Some (Jump (Cont l)))
                  then abupd (\<lambda> x. Some (Error CrossMethodJump)) s2 
                  else s2)\<rbrakk> \<Longrightarrow>
           G\<turnstile>Norm s0 \<midarrow>Body D c-\<succ>the (locals (store s2) Result)
              \<rightarrow>abupd (absorb Ret) s3"
  \<comment> \<open>cf. 14.15, 12.4.1\<close>
  \<comment> \<open>We filter out a break/continue in \<^term>\<open>s2\<close>, so that we can proof 
     definite assignment
     correct, without the need of conformance of the state. By this the
     different parts of the typesafety proof can be disentangled a little.\<close>

\<comment> \<open>evaluation of variables\<close>

  \<comment> \<open>cf. 15.13.1, 15.7.2\<close>
| LVar: "G\<turnstile>Norm s \<midarrow>LVar vn=\<succ>lvar vn s\<rightarrow> Norm s"

  \<comment> \<open>cf. 15.10.1, 12.4.1\<close>
| FVar: "\<lbrakk>G\<turnstile>Norm s0 \<midarrow>Init statDeclC\<rightarrow> s1; G\<turnstile>s1 \<midarrow>e-\<succ>a\<rightarrow> s2;
          (v,s2') = fvar statDeclC stat fn a s2;
          s3 = check_field_access G accC statDeclC fn stat a s2' \<rbrakk> \<Longrightarrow>
          G\<turnstile>Norm s0 \<midarrow>{accC,statDeclC,stat}e..fn=\<succ>v\<rightarrow> s3"
 \<comment> \<open>The accessibility check is after \<^term>\<open>fvar\<close>, to keep it simple. 
    \<^term>\<open>fvar\<close> already tests for the absence of a null-pointer reference 
    in case of an instance field\<close>

  \<comment> \<open>cf. 15.12.1, 15.25.1\<close>
| AVar: "\<lbrakk>G\<turnstile> Norm s0 \<midarrow>e1-\<succ>a\<rightarrow> s1; G\<turnstile>s1 \<midarrow>e2-\<succ>i\<rightarrow> s2;
          (v,s2') = avar G i a s2\<rbrakk> \<Longrightarrow>
                      G\<turnstile>Norm s0 \<midarrow>e1.[e2]=\<succ>v\<rightarrow> s2'"


\<comment> \<open>evaluation of expression lists\<close>

  \<comment> \<open>cf. 15.11.4.2\<close>
| Nil:
                                    "G\<turnstile>Norm s0 \<midarrow>[]\<doteq>\<succ>[]\<rightarrow> Norm s0"

  \<comment> \<open>cf. 15.6.4\<close>
| Cons: "\<lbrakk>G\<turnstile>Norm s0 \<midarrow>e -\<succ> v \<rightarrow> s1;
          G\<turnstile>     s1 \<midarrow>es\<doteq>\<succ>vs\<rightarrow> s2\<rbrakk> \<Longrightarrow>
                                   G\<turnstile>Norm s0 \<midarrow>e#es\<doteq>\<succ>v#vs\<rightarrow> s2"

(* Rearrangement of premisses:
[0,1(Abrupt),2(Skip),8(Jmp),4(Lab),30(Nil),31(Cons),27(LVar),17(Cast),18(Inst),
 17(Lit),18(UnOp),19(BinOp),20(Super),21(Acc),3(Expr),5(Comp),25(Methd),26(Body),23(Cond),6(If),
 7(Loop),11(Fin),9(Throw),13(NewC),14(NewA),12(Init),22(Ass),10(Try),28(FVar),
 29(AVar),24(Call)]
*)

ML \<open>
ML_Thms.bind_thm ("eval_induct", rearrange_prems 
[0,1,2,8,4,30,31,27,15,16,
 17,18,19,20,21,3,5,25,26,23,6,
 7,11,9,13,14,12,22,10,28,
 29,24] @{thm eval.induct})
\<close>


declare if_split     [split del] if_split_asm     [split del] 
        option.split [split del] option.split_asm [split del]
inductive_cases halloc_elim_cases: 
  "G\<turnstile>(Some xc,s) \<midarrow>halloc oi\<succ>a\<rightarrow> s'"
  "G\<turnstile>(Norm    s) \<midarrow>halloc oi\<succ>a\<rightarrow> s'"

inductive_cases sxalloc_elim_cases:
        "G\<turnstile> Norm                 s  \<midarrow>sxalloc\<rightarrow> s'"
        "G\<turnstile>(Some (Jump j),s) \<midarrow>sxalloc\<rightarrow> s'"
        "G\<turnstile>(Some (Error e),s) \<midarrow>sxalloc\<rightarrow> s'"
        "G\<turnstile>(Some (Xcpt (Loc a )),s) \<midarrow>sxalloc\<rightarrow> s'"
        "G\<turnstile>(Some (Xcpt (Std xn)),s) \<midarrow>sxalloc\<rightarrow> s'"
inductive_cases sxalloc_cases: "G\<turnstile>s \<midarrow>sxalloc\<rightarrow> s'"

lemma sxalloc_elim_cases2: "\<lbrakk>G\<turnstile>s \<midarrow>sxalloc\<rightarrow> s';  
       \<And>s.   \<lbrakk>s' = Norm s\<rbrakk> \<Longrightarrow> P;  
       \<And>j s. \<lbrakk>s' = (Some (Jump j),s)\<rbrakk> \<Longrightarrow> P;
       \<And>e s. \<lbrakk>s' = (Some (Error e),s)\<rbrakk> \<Longrightarrow> P;
       \<And>a s. \<lbrakk>s' = (Some (Xcpt (Loc a)),s)\<rbrakk> \<Longrightarrow> P  
      \<rbrakk> \<Longrightarrow> P"
apply cut_tac 
apply (erule sxalloc_cases)
apply blast+
done

declare not_None_eq [simp del] (* IntDef.Zero_def [simp del] *)
declare split_paired_All [simp del] split_paired_Ex [simp del]
setup \<open>map_theory_simpset (fn ctxt => ctxt delloop "split_all_tac")\<close>

inductive_cases eval_cases: "G\<turnstile>s \<midarrow>t\<succ>\<rightarrow> (v, s')"

inductive_cases eval_elim_cases [cases set]:
        "G\<turnstile>(Some xc,s) \<midarrow>t                              \<succ>\<rightarrow> (v, s')"
        "G\<turnstile>Norm s \<midarrow>In1r Skip                           \<succ>\<rightarrow> (x, s')"
        "G\<turnstile>Norm s \<midarrow>In1r (Jmp j)                        \<succ>\<rightarrow> (x, s')"
        "G\<turnstile>Norm s \<midarrow>In1r (l\<bullet> c)                         \<succ>\<rightarrow> (x, s')"
        "G\<turnstile>Norm s \<midarrow>In3  ([])                           \<succ>\<rightarrow> (v, s')"
        "G\<turnstile>Norm s \<midarrow>In3  (e#es)                         \<succ>\<rightarrow> (v, s')"
        "G\<turnstile>Norm s \<midarrow>In1l (Lit w)                        \<succ>\<rightarrow> (v, s')"
        "G\<turnstile>Norm s \<midarrow>In1l (UnOp unop e)                  \<succ>\<rightarrow> (v, s')"
        "G\<turnstile>Norm s \<midarrow>In1l (BinOp binop e1 e2)            \<succ>\<rightarrow> (v, s')"
        "G\<turnstile>Norm s \<midarrow>In2  (LVar vn)                      \<succ>\<rightarrow> (v, s')"
        "G\<turnstile>Norm s \<midarrow>In1l (Cast T e)                     \<succ>\<rightarrow> (v, s')"
        "G\<turnstile>Norm s \<midarrow>In1l (e InstOf T)                   \<succ>\<rightarrow> (v, s')"
        "G\<turnstile>Norm s \<midarrow>In1l (Super)                        \<succ>\<rightarrow> (v, s')"
        "G\<turnstile>Norm s \<midarrow>In1l (Acc va)                       \<succ>\<rightarrow> (v, s')"
        "G\<turnstile>Norm s \<midarrow>In1r (Expr e)                       \<succ>\<rightarrow> (x, s')"
        "G\<turnstile>Norm s \<midarrow>In1r (c1;; c2)                      \<succ>\<rightarrow> (x, s')"
        "G\<turnstile>Norm s \<midarrow>In1l (Methd C sig)                  \<succ>\<rightarrow> (x, s')"
        "G\<turnstile>Norm s \<midarrow>In1l (Body D c)                     \<succ>\<rightarrow> (x, s')"
        "G\<turnstile>Norm s \<midarrow>In1l (e0 ? e1 : e2)                 \<succ>\<rightarrow> (v, s')"
        "G\<turnstile>Norm s \<midarrow>In1r (If(e) c1 Else c2)             \<succ>\<rightarrow> (x, s')"
        "G\<turnstile>Norm s \<midarrow>In1r (l\<bullet> While(e) c)                \<succ>\<rightarrow> (x, s')"
        "G\<turnstile>Norm s \<midarrow>In1r (c1 Finally c2)                \<succ>\<rightarrow> (x, s')"
        "G\<turnstile>Norm s \<midarrow>In1r (Throw e)                      \<succ>\<rightarrow> (x, s')"
        "G\<turnstile>Norm s \<midarrow>In1l (NewC C)                       \<succ>\<rightarrow> (v, s')"
        "G\<turnstile>Norm s \<midarrow>In1l (New T[e])                     \<succ>\<rightarrow> (v, s')"
        "G\<turnstile>Norm s \<midarrow>In1l (Ass va e)                     \<succ>\<rightarrow> (v, s')"
        "G\<turnstile>Norm s \<midarrow>In1r (Try c1 Catch(tn vn) c2)       \<succ>\<rightarrow> (x, s')"
        "G\<turnstile>Norm s \<midarrow>In2  ({accC,statDeclC,stat}e..fn)   \<succ>\<rightarrow> (v, s')"
        "G\<turnstile>Norm s \<midarrow>In2  (e1.[e2])                      \<succ>\<rightarrow> (v, s')"
        "G\<turnstile>Norm s \<midarrow>In1l ({accC,statT,mode}e\<cdot>mn({pT}p)) \<succ>\<rightarrow> (v, s')"
        "G\<turnstile>Norm s \<midarrow>In1r (Init C)                       \<succ>\<rightarrow> (x, s')"
declare not_None_eq [simp]  (* IntDef.Zero_def [simp] *)
declare split_paired_All [simp] split_paired_Ex [simp]
declaration \<open>K (Simplifier.map_ss (fn ss => ss addloop ("split_all_tac", split_all_tac)))\<close>
declare if_split     [split] if_split_asm     [split] 
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
apply (rename_tac a, induct_tac "a")
apply auto
done

text \<open>The following simplification procedures set up the proper injections of
 terms and their corresponding values in the evaluation relation:
 E.g. an expression 
 (injection \<^term>\<open>In1l\<close> into terms) always evaluates to ordinary values 
 (injection \<^term>\<open>In1\<close> into generalised values \<^term>\<open>vals\<close>). 
\<close>

lemma eval_expr_eq: "G\<turnstile>s \<midarrow>In1l t\<succ>\<rightarrow> (w, s') = (\<exists>v. w=In1 v \<and> G\<turnstile>s \<midarrow>t-\<succ>v \<rightarrow> s')"
  by (auto, frule eval_Inj_elim, auto)

lemma eval_var_eq: "G\<turnstile>s \<midarrow>In2 t\<succ>\<rightarrow> (w, s') = (\<exists>vf. w=In2 vf \<and> G\<turnstile>s \<midarrow>t=\<succ>vf\<rightarrow> s')"
  by (auto, frule eval_Inj_elim, auto)

lemma eval_exprs_eq: "G\<turnstile>s \<midarrow>In3 t\<succ>\<rightarrow> (w, s') = (\<exists>vs. w=In3 vs \<and> G\<turnstile>s \<midarrow>t\<doteq>\<succ>vs\<rightarrow> s')"
  by (auto, frule eval_Inj_elim, auto)

lemma eval_stmt_eq: "G\<turnstile>s \<midarrow>In1r t\<succ>\<rightarrow> (w, s') = (w=\<diamondsuit> \<and> G\<turnstile>s \<midarrow>t \<rightarrow> s')"
  by (auto, frule eval_Inj_elim, auto, frule eval_Inj_elim, auto)

simproc_setup eval_expr ("G\<turnstile>s \<midarrow>In1l t\<succ>\<rightarrow> (w, s')") = \<open>
  K (K (fn ct =>
    (case Thm.term_of ct of
      (_ $ _ $ _ $ _ $ (Const _ $ _) $ _) => NONE
    | _ => SOME (mk_meta_eq @{thm eval_expr_eq}))))\<close>

simproc_setup eval_var ("G\<turnstile>s \<midarrow>In2 t\<succ>\<rightarrow> (w, s')") = \<open>
  K (K (fn ct =>
    (case Thm.term_of ct of
      (_ $ _ $ _ $ _ $ (Const _ $ _) $ _) => NONE
    | _ => SOME (mk_meta_eq @{thm eval_var_eq}))))\<close>

simproc_setup eval_exprs ("G\<turnstile>s \<midarrow>In3 t\<succ>\<rightarrow> (w, s')") = \<open>
  K (K (fn ct =>
    (case Thm.term_of ct of
      (_ $ _ $ _ $ _ $ (Const _ $ _) $ _) => NONE
    | _ => SOME (mk_meta_eq @{thm eval_exprs_eq}))))\<close>

simproc_setup eval_stmt ("G\<turnstile>s \<midarrow>In1r t\<succ>\<rightarrow> (w, s')") = \<open>
  K (K (fn ct =>
    (case Thm.term_of ct of
      (_ $ _ $ _ $ _ $ (Const _ $ _) $ _) => NONE
    | _ => SOME (mk_meta_eq @{thm eval_stmt_eq}))))\<close>

ML \<open>
ML_Thms.bind_thms ("AbruptIs", sum3_instantiate \<^context> @{thm eval.Abrupt})
\<close>

declare halloc.Abrupt [intro!] eval.Abrupt [intro!]  AbruptIs [intro!]

text\<open>\<open>Callee\<close>,\<open>InsInitE\<close>, \<open>InsInitV\<close>, \<open>FinA\<close> are only
used in smallstep semantics, not in the bigstep semantics. So their is no
valid evaluation of these terms 
\<close>


lemma eval_Callee: "G\<turnstile>Norm s\<midarrow>Callee l e-\<succ>v\<rightarrow> s' = False"
proof -
  { fix s t v s'
    assume eval: "G\<turnstile>s \<midarrow>t\<succ>\<rightarrow> (v,s')" and
         normal: "normal s" and
         callee: "t=In1l (Callee l e)"
    then have "False" by induct auto
  }  
  then show ?thesis
    by (cases s') fastforce
qed


lemma eval_InsInitE: "G\<turnstile>Norm s\<midarrow>InsInitE c e-\<succ>v\<rightarrow> s' = False"
proof -
  { fix s t v s'
    assume eval: "G\<turnstile>s \<midarrow>t\<succ>\<rightarrow> (v,s')" and
         normal: "normal s" and
         callee: "t=In1l (InsInitE c e)"
    then have "False" by induct auto
  }
  then show ?thesis
    by (cases s') fastforce
qed

lemma eval_InsInitV: "G\<turnstile>Norm s\<midarrow>InsInitV c w=\<succ>v\<rightarrow> s' = False"
proof -
  { fix s t v s'
    assume eval: "G\<turnstile>s \<midarrow>t\<succ>\<rightarrow> (v,s')" and
         normal: "normal s" and
         callee: "t=In2 (InsInitV c w)"
    then have "False" by induct auto
  }  
  then show ?thesis
    by (cases s') fastforce
qed

lemma eval_FinA: "G\<turnstile>Norm s\<midarrow>FinA a c\<rightarrow> s' = False"
proof -
  { fix s t v s'
    assume eval: "G\<turnstile>s \<midarrow>t\<succ>\<rightarrow> (v,s')" and
         normal: "normal s" and
         callee: "t=In1r (FinA a c)"
    then have "False" by induct auto
  }  
  then show ?thesis
    by (cases s') fastforce 
qed

lemma eval_no_abrupt_lemma: 
   "\<And>s s'. G\<turnstile>s \<midarrow>t\<succ>\<rightarrow> (w,s') \<Longrightarrow> normal s' \<longrightarrow> normal s"
by (erule eval_cases, auto)

lemma eval_no_abrupt: 
  "G\<turnstile>(x,s) \<midarrow>t\<succ>\<rightarrow> (w,Norm s') = 
        (x = None \<and> G\<turnstile>Norm s \<midarrow>t\<succ>\<rightarrow> (w,Norm s'))"
apply auto
apply (frule eval_no_abrupt_lemma, auto)+
done

simproc_setup eval_no_abrupt ("G\<turnstile>(x,s) \<midarrow>e\<succ>\<rightarrow> (w,Norm s')") = \<open>
  K (K (fn ct =>
    (case Thm.term_of ct of
      (_ $ _ $ (Const (\<^const_name>\<open>Pair\<close>, _) $ (Const (\<^const_name>\<open>None\<close>, _)) $ _) $ _  $ _ $ _) => NONE
    | _ => SOME (mk_meta_eq @{thm eval_no_abrupt}))))
\<close>


lemma eval_abrupt_lemma: 
  "G\<turnstile>s \<midarrow>t\<succ>\<rightarrow> (v,s') \<Longrightarrow> abrupt s=Some xc \<longrightarrow> s'= s \<and> v = undefined3 t"
by (erule eval_cases, auto)

lemma eval_abrupt: 
 " G\<turnstile>(Some xc,s) \<midarrow>t\<succ>\<rightarrow> (w,s') =  
     (s'=(Some xc,s) \<and> w=undefined3 t \<and> 
     G\<turnstile>(Some xc,s) \<midarrow>t\<succ>\<rightarrow> (undefined3 t,(Some xc,s)))"
apply auto
apply (frule eval_abrupt_lemma, auto)+
done

simproc_setup eval_abrupt ("G\<turnstile>(Some xc,s) \<midarrow>e\<succ>\<rightarrow> (w,s')") = \<open>
  K (K (fn ct =>
    (case Thm.term_of ct of
      (_ $ _ $ _ $ _ $ _ $ (Const (\<^const_name>\<open>Pair\<close>, _) $ (Const (\<^const_name>\<open>Some\<close>, _) $ _)$ _)) => NONE
    | _ => SOME (mk_meta_eq @{thm eval_abrupt}))))
\<close>

lemma LitI: "G\<turnstile>s \<midarrow>Lit v-\<succ>(if normal s then v else undefined)\<rightarrow> s"
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
         G\<turnstile>s \<midarrow>e ? e1 : e2-\<succ>(if normal s1 then v else undefined)\<rightarrow> s2"
apply (case_tac "s", case_tac "a = None")
by (auto intro!: eval.Cond)

lemma IfI: "\<lbrakk>G\<turnstile>s \<midarrow>e-\<succ>v\<rightarrow> s1; G\<turnstile>s1 \<midarrow>(if the_Bool v then c1 else c2)\<rightarrow> s2\<rbrakk>
                 \<Longrightarrow> G\<turnstile>s \<midarrow>If(e) c1 Else c2\<rightarrow> s2"
apply (case_tac "s", case_tac "a = None")
by (auto intro!: eval.If)

lemma MethdI: "G\<turnstile>s \<midarrow>body G C sig-\<succ>v\<rightarrow> s' 
                \<Longrightarrow> G\<turnstile>s \<midarrow>Methd C sig-\<succ>v\<rightarrow> s'"
apply (case_tac "s", case_tac "a = None")
by (auto intro!: eval.Methd)

lemma eval_Call: 
   "\<lbrakk>G\<turnstile>Norm s0 \<midarrow>e-\<succ>a'\<rightarrow> s1; G\<turnstile>s1 \<midarrow>ps\<doteq>\<succ>pvs\<rightarrow> s2;  
     D = invocation_declclass G mode (store s2) a' statT \<lparr>name=mn,parTs=pTs\<rparr>;
     s3 = init_lvars G D \<lparr>name=mn,parTs=pTs\<rparr> mode a' pvs s2;
     s3' = check_method_access G accC statT mode \<lparr>name=mn,parTs=pTs\<rparr> a' s3;
     G\<turnstile>s3'\<midarrow>Methd D \<lparr>name=mn,parTs=pTs\<rparr>-\<succ> v\<rightarrow> s4; 
       s4' = restore_lvars s2 s4\<rbrakk> \<Longrightarrow>  
       G\<turnstile>Norm s0 \<midarrow>{accC,statT,mode}e\<cdot>mn({pTs}ps)-\<succ>v\<rightarrow> s4'"
apply (drule eval.Call, assumption)
apply (rule HOL.refl)
apply simp+
done

lemma eval_Init: 
"\<lbrakk>if inited C (globs s0) then s3 = Norm s0 
  else G\<turnstile>Norm (init_class_obj G C s0)  
         \<midarrow>(if C = Object then Skip else Init (super (the (class G C))))\<rightarrow> s1 \<and>
       G\<turnstile>set_lvars Map.empty s1 \<midarrow>(init (the (class G C)))\<rightarrow> s2 \<and> 
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
"G\<turnstile>s \<midarrow>StatRef rt-\<succ>(if abrupt s=None then Null else undefined)\<rightarrow> s"
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
apply (simp (no_asm_use) split del: if_split_asm option.split_asm)+
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
  "G\<turnstile>s \<midarrow>In1l(body G C sig)\<succ>\<rightarrow> (w,s') 
   \<Longrightarrow> G\<turnstile>s \<midarrow>In1l(Methd C sig)\<succ>\<rightarrow> (w,s')"
apply (case_tac "s")
apply (case_tac "a")
apply clarsimp+
apply (erule eval.Methd)
apply (drule eval_abrupt_lemma)
apply force
done

lemma eval_Body: "\<lbrakk>G\<turnstile>Norm s0 \<midarrow>Init D\<rightarrow> s1; G\<turnstile>s1 \<midarrow>c\<rightarrow> s2;
                   res=the (locals (store s2) Result);
                   s3 = (if (\<exists> l. abrupt s2 = Some (Jump (Break l)) \<or>
                                  abrupt s2 = Some (Jump (Cont l))) 
                   then abupd (\<lambda> x. Some (Error CrossMethodJump)) s2 
                   else s2);
                   s4=abupd (absorb Ret) s3\<rbrakk> \<Longrightarrow>
 G\<turnstile>Norm s0 \<midarrow>Body D c-\<succ>res\<rightarrow>s4"
by (auto elim: eval.Body)

lemma eval_binop_arg2_indep:
"\<not> need_second_arg binop v1 \<Longrightarrow> eval_binop binop v1 x = eval_binop binop v1 y"
by (cases binop)
   (simp_all add: need_second_arg_def)


lemma eval_BinOp_arg2_indepI:
  assumes eval_e1: "G\<turnstile>Norm s0 \<midarrow>e1-\<succ>v1\<rightarrow> s1" and
          no_need: "\<not> need_second_arg binop v1" 
  shows "G\<turnstile>Norm s0 \<midarrow>BinOp binop e1 e2-\<succ>(eval_binop binop v1 v2)\<rightarrow> s1"
         (is "?EvalBinOp v2")
proof -
  from eval_e1 
  have "?EvalBinOp Unit" 
    by (rule eval.BinOp)
       (simp add: no_need)
  moreover
  from no_need 
  have "eval_binop binop v1 Unit = eval_binop binop v1 v2"
    by (simp add: eval_binop_arg2_indep)
  ultimately
  show ?thesis
    by simp
qed


subsubsection "single valued"

lemma unique_halloc [rule_format (no_asm)]: 
  "G\<turnstile>s \<midarrow>halloc oi\<succ>a \<rightarrow> s' \<Longrightarrow> G\<turnstile>s \<midarrow>halloc oi\<succ>a' \<rightarrow> s'' \<longrightarrow> a' = a \<and> s'' = s'"
apply (erule halloc.induct)
apply  (auto elim!: halloc_elim_cases split del: if_split if_split_asm)
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
  "G\<turnstile>s \<midarrow>sxalloc\<rightarrow> s' \<Longrightarrow> G\<turnstile>s \<midarrow>sxalloc\<rightarrow> s'' \<longrightarrow> s'' = s'"
apply (erule sxalloc.induct)
apply   (auto dest: unique_halloc elim!: sxalloc_elim_cases 
              split del: if_split if_split_asm)
done

lemma single_valued_sxalloc: "single_valued {(s,s'). G\<turnstile>s \<midarrow>sxalloc\<rightarrow> s'}"
apply (unfold single_valued_def)
apply (blast dest: unique_sxalloc)
done

lemma split_pairD: "(x,y) = p \<Longrightarrow> x = fst p & y = snd p"
by auto



lemma unique_eval [rule_format (no_asm)]: 
  "G\<turnstile>s \<midarrow>t\<succ>\<rightarrow> (w, s') \<Longrightarrow> (\<forall>w' s''. G\<turnstile>s \<midarrow>t\<succ>\<rightarrow> (w', s'') \<longrightarrow> w' = w \<and> s'' = s')"
apply (erule eval_induct)
apply (tactic \<open>ALLGOALS (EVERY'
      [strip_tac \<^context>, rotate_tac ~1, eresolve_tac \<^context> @{thms eval_elim_cases}])\<close>)
(* 31 subgoals *)
prefer 28 (* Try *) 
apply (simp (no_asm_use) only: split: if_split_asm)
(* 34 subgoals *)
prefer 30 (* Init *)
apply (case_tac "inited C (globs s0)", (simp only: if_True if_False simp_thms)+)
prefer 26 (* While *)
apply (simp (no_asm_use) only: split: if_split_asm, blast)
(* 36 subgoals *)
apply (blast dest: unique_sxalloc unique_halloc split_pairD)+
done

(* unused *)
lemma single_valued_eval: 
 "single_valued {((s, t), (v, s')). G\<turnstile>s \<midarrow>t\<succ>\<rightarrow> (v, s')}"
apply (unfold single_valued_def)
by (clarify, drule (1) unique_eval, auto)

end
