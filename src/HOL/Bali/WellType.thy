(*  Title:      HOL/Bali/WellType.thy
    ID:         $Id$
    Author:     David von Oheimb
    License:    GPL (GNU GENERAL PUBLIC LICENSE)
*)
header {* Well-typedness of Java programs *}

theory WellType = DeclConcepts:

text {*
improvements over Java Specification 1.0:
\begin{itemize}
\item methods of Object can be called upon references of interface or array type
\end{itemize}
simplifications:
\begin{itemize}
\item the type rules include all static checks on statements and expressions, 
      e.g. definedness of names (of parameters, locals, fields, methods)
\end{itemize}
design issues:
\begin{itemize}
\item unified type judgment for statements, variables, expressions, 
      expression lists
\item statements are typed like expressions with dummy type Void
\item the typing rules take an extra argument that is capable of determining 
  the dynamic type of objects. Therefore, they can be used for both 
  checking static types and determining runtime types in transition semantics.
\end{itemize}
*}

types	lenv
	= "(lname, ty) table"  --{* local variables, including This and Result*}

record env = 
         prg:: "prog"    --{* program *}
         cls:: "qtname"  --{* current package and class name *}
         lcl:: "lenv"    --{* local environment *}     
  
translations
  "lenv" <= (type) "(lname, ty) table"
  "lenv" <= (type) "lname \<Rightarrow> ty option"
  "env" <= (type) "\<lparr>prg::prog,cls::qtname,lcl::lenv\<rparr>"
  "env" <= (type) "\<lparr>prg::prog,cls::qtname,lcl::lenv,\<dots>::'a\<rparr>"



syntax
  pkg :: "env \<Rightarrow> pname" --{* select the current package from an environment *}
translations 
  "pkg e" == "pid (cls e)"

section "Static overloading: maximally specific methods "

types
  emhead = "ref_ty \<times> mhead"

--{* Some mnemotic selectors for emhead *}
constdefs 
  "declrefT" :: "emhead \<Rightarrow> ref_ty"
  "declrefT \<equiv> fst"

  "mhd"     :: "emhead \<Rightarrow> mhead"
  "mhd \<equiv> snd"

lemma declrefT_simp[simp]:"declrefT (r,m) = r"
by (simp add: declrefT_def)

lemma mhd_simp[simp]:"mhd (r,m) = m"
by (simp add: mhd_def)

lemma static_mhd_simp[simp]: "static (mhd m) = is_static m"
by (cases m) (simp add: member_is_static_simp mhd_def)

lemma mhd_resTy_simp [simp]: "resTy (mhd m) = resTy m"
by (cases m) simp

lemma mhd_is_static_simp [simp]: "is_static (mhd m) = is_static m"
by (cases m) simp

lemma mhd_accmodi_simp [simp]: "accmodi (mhd m) = accmodi m"
by (cases m) simp

consts
  cmheads        :: "prog \<Rightarrow> qtname \<Rightarrow> qtname \<Rightarrow> sig \<Rightarrow> emhead set"
  Objectmheads   :: "prog \<Rightarrow> qtname           \<Rightarrow> sig \<Rightarrow> emhead set"
  accObjectmheads:: "prog \<Rightarrow> qtname \<Rightarrow> ref_ty \<Rightarrow> sig \<Rightarrow> emhead set"
  mheads         :: "prog \<Rightarrow> qtname \<Rightarrow> ref_ty \<Rightarrow> sig \<Rightarrow> emhead set"
defs
 cmheads_def:
"cmheads G S C 
  \<equiv> \<lambda>sig. (\<lambda>(Cls,mthd). (ClassT Cls,(mhead mthd))) ` o2s (accmethd G S C sig)"
  Objectmheads_def:
"Objectmheads G S  
  \<equiv> \<lambda>sig. (\<lambda>(Cls,mthd). (ClassT Cls,(mhead mthd))) 
    ` o2s (filter_tab (\<lambda>sig m. accmodi m \<noteq> Private) (accmethd G S Object) sig)"
  accObjectmheads_def:
"accObjectmheads G S T
   \<equiv> if G\<turnstile>RefT T accessible_in (pid S)
        then Objectmheads G S
        else \<lambda>sig. {}"
primrec
"mheads G S  NullT     = (\<lambda>sig. {})"
"mheads G S (IfaceT I) = (\<lambda>sig. (\<lambda>(I,h).(IfaceT I,h)) 
                         ` accimethds G (pid S) I sig \<union> 
                           accObjectmheads G S (IfaceT I) sig)"
"mheads G S (ClassT C) = cmheads G S C"
"mheads G S (ArrayT T) = accObjectmheads G S (ArrayT T)"

constdefs
  --{* applicable methods, cf. 15.11.2.1 *}
  appl_methds   :: "prog \<Rightarrow> qtname \<Rightarrow>  ref_ty \<Rightarrow> sig \<Rightarrow> (emhead \<times> ty list)\<spacespace> set"
 "appl_methds G S rt \<equiv> \<lambda> sig. 
      {(mh,pTs') |mh pTs'. mh \<in> mheads G S rt \<lparr>name=name sig,parTs=pTs'\<rparr> \<and> 
                           G\<turnstile>(parTs sig)[\<preceq>]pTs'}"

  --{* more specific methods, cf. 15.11.2.2 *}
  more_spec     :: "prog \<Rightarrow> emhead \<times> ty list \<Rightarrow> emhead \<times> ty list \<Rightarrow> bool"
 "more_spec G \<equiv> \<lambda>(mh,pTs). \<lambda>(mh',pTs'). G\<turnstile>pTs[\<preceq>]pTs'"
(*more_spec G \<equiv>\<lambda>((d,h),pTs). \<lambda>((d',h'),pTs'). G\<turnstile>RefT d\<preceq>RefT d'\<and>G\<turnstile>pTs[\<preceq>]pTs'*)

  --{* maximally specific methods, cf. 15.11.2.2 *}
   max_spec     :: "prog \<Rightarrow> qtname \<Rightarrow> ref_ty \<Rightarrow> sig \<Rightarrow> (emhead \<times> ty list)\<spacespace> set"

 "max_spec G S rt sig \<equiv>{m. m \<in>appl_methds G S rt sig \<and>
		      (\<forall>m'\<in>appl_methds G S rt sig. more_spec G m' m \<longrightarrow> m'=m)}"


lemma max_spec2appl_meths: 
  "x \<in> max_spec G S T sig \<Longrightarrow> x \<in> appl_methds G S T sig" 
by (auto simp: max_spec_def)

lemma appl_methsD: "(mh,pTs')\<in>appl_methds G S T \<lparr>name=mn,parTs=pTs\<rparr> \<Longrightarrow>  
   mh \<in> mheads G S T \<lparr>name=mn,parTs=pTs'\<rparr> \<and> G\<turnstile>pTs[\<preceq>]pTs'"
by (auto simp: appl_methds_def)

lemma max_spec2mheads: 
"max_spec G S rt \<lparr>name=mn,parTs=pTs\<rparr> = insert (mh, pTs') A 
 \<Longrightarrow> mh \<in> mheads G S rt \<lparr>name=mn,parTs=pTs'\<rparr> \<and> G\<turnstile>pTs[\<preceq>]pTs'"
apply (auto dest: equalityD2 subsetD max_spec2appl_meths appl_methsD)
done


constdefs
  empty_dt :: "dyn_ty"
 "empty_dt \<equiv> \<lambda>a. None"

  invmode :: "('a::type)member_scheme \<Rightarrow> expr \<Rightarrow> inv_mode"
"invmode m e \<equiv> if is_static m 
                  then Static 
                  else if e=Super then SuperM else IntVir"

lemma invmode_nonstatic [simp]: 
  "invmode \<lparr>access=a,static=False,\<dots>=x\<rparr> (Acc (LVar e)) = IntVir"
apply (unfold invmode_def)
apply (simp (no_asm) add: member_is_static_simp)
done


lemma invmode_Static_eq [simp]: "(invmode m e = Static) = is_static m"
apply (unfold invmode_def)
apply (simp (no_asm))
done


lemma invmode_IntVir_eq: "(invmode m e = IntVir) = (\<not>(is_static m) \<and> e\<noteq>Super)"
apply (unfold invmode_def)
apply (simp (no_asm))
done

lemma Null_staticD: 
  "a'=Null \<longrightarrow> (is_static m) \<Longrightarrow> invmode m e = IntVir \<longrightarrow> a' \<noteq> Null"
apply (clarsimp simp add: invmode_IntVir_eq)
done

section "Typing for unary operations"

consts unop_type :: "unop \<Rightarrow> prim_ty"
primrec 
"unop_type UPlus   = Integer"
"unop_type UMinus  = Integer"
"unop_type UBitNot = Integer"
"unop_type UNot    = Boolean"    

consts wt_unop :: "unop \<Rightarrow> ty \<Rightarrow> bool"
primrec
"wt_unop UPlus   t = (t = PrimT Integer)"
"wt_unop UMinus  t = (t = PrimT Integer)"
"wt_unop UBitNot t = (t = PrimT Integer)"
"wt_unop UNot    t = (t = PrimT Boolean)"

section "Typing for binary operations"

consts binop_type :: "binop \<Rightarrow> prim_ty"
primrec
"binop_type Mul      = Integer"     
"binop_type Div      = Integer"
"binop_type Mod      = Integer"
"binop_type Plus     = Integer"
"binop_type Minus    = Integer"
"binop_type LShift   = Integer"
"binop_type RShift   = Integer"
"binop_type RShiftU  = Integer"
"binop_type Less     = Boolean"
"binop_type Le       = Boolean"
"binop_type Greater  = Boolean"
"binop_type Ge       = Boolean"
"binop_type Eq       = Boolean"
"binop_type Neq      = Boolean"
"binop_type BitAnd   = Integer"
"binop_type And      = Boolean"
"binop_type BitXor   = Integer"
"binop_type Xor      = Boolean"
"binop_type BitOr    = Integer"
"binop_type Or       = Boolean"
"binop_type CondAnd  = Boolean"
"binop_type CondOr   = Boolean"

consts wt_binop :: "prog \<Rightarrow> binop \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> bool"
primrec
"wt_binop G Mul     t1 t2 = ((t1 = PrimT Integer) \<and> (t2 = PrimT Integer))"
"wt_binop G Div     t1 t2 = ((t1 = PrimT Integer) \<and> (t2 = PrimT Integer))"
"wt_binop G Mod     t1 t2 = ((t1 = PrimT Integer) \<and> (t2 = PrimT Integer))"
"wt_binop G Plus    t1 t2 = ((t1 = PrimT Integer) \<and> (t2 = PrimT Integer))"
"wt_binop G Minus   t1 t2 = ((t1 = PrimT Integer) \<and> (t2 = PrimT Integer))"
"wt_binop G LShift  t1 t2 = ((t1 = PrimT Integer) \<and> (t2 = PrimT Integer))"
"wt_binop G RShift  t1 t2 = ((t1 = PrimT Integer) \<and> (t2 = PrimT Integer))"
"wt_binop G RShiftU t1 t2 = ((t1 = PrimT Integer) \<and> (t2 = PrimT Integer))"
"wt_binop G Less    t1 t2 = ((t1 = PrimT Integer) \<and> (t2 = PrimT Integer))"
"wt_binop G Le      t1 t2 = ((t1 = PrimT Integer) \<and> (t2 = PrimT Integer))"
"wt_binop G Greater t1 t2 = ((t1 = PrimT Integer) \<and> (t2 = PrimT Integer))"
"wt_binop G Ge      t1 t2 = ((t1 = PrimT Integer) \<and> (t2 = PrimT Integer))"
"wt_binop G Eq      t1 t2 = (G\<turnstile>t1\<preceq>t2 \<or> G\<turnstile>t2\<preceq>t1)" 
"wt_binop G Neq     t1 t2 = (G\<turnstile>t1\<preceq>t2 \<or> G\<turnstile>t2\<preceq>t1)"
"wt_binop G BitAnd  t1 t2 = ((t1 = PrimT Integer) \<and> (t2 = PrimT Integer))"
"wt_binop G And     t1 t2 = ((t1 = PrimT Boolean) \<and> (t2 = PrimT Boolean))"
"wt_binop G BitXor  t1 t2 = ((t1 = PrimT Integer) \<and> (t2 = PrimT Integer))"
"wt_binop G Xor     t1 t2 = ((t1 = PrimT Boolean) \<and> (t2 = PrimT Boolean))"
"wt_binop G BitOr   t1 t2 = ((t1 = PrimT Integer) \<and> (t2 = PrimT Integer))"
"wt_binop G Or      t1 t2 = ((t1 = PrimT Boolean) \<and> (t2 = PrimT Boolean))"
"wt_binop G CondAnd t1 t2 = ((t1 = PrimT Boolean) \<and> (t2 = PrimT Boolean))"
"wt_binop G CondOr  t1 t2 = ((t1 = PrimT Boolean) \<and> (t2 = PrimT Boolean))"

section "Typing for terms"

types tys  =        "ty + ty list"
translations
  "tys"   <= (type) "ty + ty list"

consts
  wt    :: "(env\<spacespace> \<times> dyn_ty\<spacespace> \<times>  term \<times> tys) set"
(*wt    :: " env \<Rightarrow> dyn_ty \<Rightarrow> (term \<times> tys) set" not feasible because of 
					      \<spacespace>  changing env in Try stmt *)

syntax
wt      :: "env \<Rightarrow> dyn_ty \<Rightarrow> [term,tys]  \<Rightarrow> bool" ("_,_|=_::_" [51,51,51,51] 50)
wt_stmt :: "env \<Rightarrow> dyn_ty \<Rightarrow>  stmt       \<Rightarrow> bool" ("_,_|=_:<>" [51,51,51   ] 50)
ty_expr :: "env \<Rightarrow> dyn_ty \<Rightarrow> [expr ,ty ] \<Rightarrow> bool" ("_,_|=_:-_" [51,51,51,51] 50)
ty_var  :: "env \<Rightarrow> dyn_ty \<Rightarrow> [var  ,ty ] \<Rightarrow> bool" ("_,_|=_:=_" [51,51,51,51] 50)
ty_exprs:: "env \<Rightarrow> dyn_ty \<Rightarrow> [expr list,
	         \<spacespace>        \<spacespace>  ty   list] \<Rightarrow> bool" ("_,_|=_:#_" [51,51,51,51] 50)

syntax (xsymbols)
wt      :: "env \<Rightarrow> dyn_ty \<Rightarrow> [term,tys] \<Rightarrow> bool" ("_,_\<Turnstile>_\<Colon>_"  [51,51,51,51] 50)
wt_stmt :: "env \<Rightarrow> dyn_ty \<Rightarrow>  stmt       \<Rightarrow> bool" ("_,_\<Turnstile>_\<Colon>\<surd>"  [51,51,51   ] 50)
ty_expr :: "env \<Rightarrow> dyn_ty \<Rightarrow> [expr ,ty ] \<Rightarrow> bool" ("_,_\<Turnstile>_\<Colon>-_" [51,51,51,51] 50)
ty_var  :: "env \<Rightarrow> dyn_ty \<Rightarrow> [var  ,ty ] \<Rightarrow> bool" ("_,_\<Turnstile>_\<Colon>=_" [51,51,51,51] 50)
ty_exprs:: "env \<Rightarrow> dyn_ty \<Rightarrow> [expr list,
		  \<spacespace>        \<spacespace>  ty   list] \<Rightarrow> bool"("_,_\<Turnstile>_\<Colon>\<doteq>_" [51,51,51,51] 50)

translations
	"E,dt\<Turnstile>t\<Colon>T" == "(E,dt,t,T) \<in> wt"
	"E,dt\<Turnstile>s\<Colon>\<surd>"  == "E,dt\<Turnstile>In1r s\<Colon>Inl (PrimT Void)"
	"E,dt\<Turnstile>e\<Colon>-T" == "E,dt\<Turnstile>In1l e\<Colon>Inl T"
	"E,dt\<Turnstile>e\<Colon>=T" == "E,dt\<Turnstile>In2  e\<Colon>Inl T"
	"E,dt\<Turnstile>e\<Colon>\<doteq>T" == "E,dt\<Turnstile>In3  e\<Colon>Inr T"

syntax (* for purely static typing *)
  wt_      :: "env \<Rightarrow> [term,tys] \<Rightarrow> bool" ("_|-_::_" [51,51,51] 50)
  wt_stmt_ :: "env \<Rightarrow>  stmt       \<Rightarrow> bool" ("_|-_:<>" [51,51   ] 50)
  ty_expr_ :: "env \<Rightarrow> [expr ,ty ] \<Rightarrow> bool" ("_|-_:-_" [51,51,51] 50)
  ty_var_  :: "env \<Rightarrow> [var  ,ty ] \<Rightarrow> bool" ("_|-_:=_" [51,51,51] 50)
  ty_exprs_:: "env \<Rightarrow> [expr list,
		     \<spacespace> ty   list] \<Rightarrow> bool" ("_|-_:#_" [51,51,51] 50)

syntax (xsymbols)
  wt_      :: "env \<Rightarrow> [term,tys] \<Rightarrow> bool" ("_\<turnstile>_\<Colon>_"  [51,51,51] 50)
  wt_stmt_ ::  "env \<Rightarrow>  stmt       \<Rightarrow> bool" ("_\<turnstile>_\<Colon>\<surd>"  [51,51   ] 50)
  ty_expr_ :: "env \<Rightarrow> [expr ,ty ] \<Rightarrow> bool" ("_\<turnstile>_\<Colon>-_" [51,51,51] 50)
  ty_var_  :: "env \<Rightarrow> [var  ,ty ] \<Rightarrow> bool" ("_\<turnstile>_\<Colon>=_" [51,51,51] 50)
  ty_exprs_ :: "env \<Rightarrow> [expr list,
		    \<spacespace>  ty   list] \<Rightarrow> bool" ("_\<turnstile>_\<Colon>\<doteq>_" [51,51,51] 50)

translations
	"E\<turnstile>t\<Colon> T" == "E,empty_dt\<Turnstile>t\<Colon> T"
        "E\<turnstile>s\<Colon>\<surd>"  == "E\<turnstile>In1r s\<Colon>Inl (PrimT Void)"
	"E\<turnstile>e\<Colon>-T" == "E\<turnstile>In1l e\<Colon>Inl T"
	"E\<turnstile>e\<Colon>=T" == "E\<turnstile>In2  e\<Colon>Inl T"
	"E\<turnstile>e\<Colon>\<doteq>T" == "E\<turnstile>In3  e\<Colon>Inr T"


inductive wt intros 


--{* well-typed statements *}

  Skip:					"E,dt\<Turnstile>Skip\<Colon>\<surd>"

  Expr:	"\<lbrakk>E,dt\<Turnstile>e\<Colon>-T\<rbrakk> \<Longrightarrow>
					 E,dt\<Turnstile>Expr e\<Colon>\<surd>"
  --{* cf. 14.6 *}
  Lab:  "E,dt\<Turnstile>c\<Colon>\<surd> \<Longrightarrow>                   
                                         E,dt\<Turnstile>l\<bullet> c\<Colon>\<surd>" 

  Comp:	"\<lbrakk>E,dt\<Turnstile>c1\<Colon>\<surd>; 
	  E,dt\<Turnstile>c2\<Colon>\<surd>\<rbrakk> \<Longrightarrow>
					 E,dt\<Turnstile>c1;; c2\<Colon>\<surd>"

  --{* cf. 14.8 *}
  If:	"\<lbrakk>E,dt\<Turnstile>e\<Colon>-PrimT Boolean;
	  E,dt\<Turnstile>c1\<Colon>\<surd>;
	  E,dt\<Turnstile>c2\<Colon>\<surd>\<rbrakk> \<Longrightarrow>
					 E,dt\<Turnstile>If(e) c1 Else c2\<Colon>\<surd>"

  --{* cf. 14.10 *}
  Loop:	"\<lbrakk>E,dt\<Turnstile>e\<Colon>-PrimT Boolean;
	  E,dt\<Turnstile>c\<Colon>\<surd>\<rbrakk> \<Longrightarrow>
					 E,dt\<Turnstile>l\<bullet> While(e) c\<Colon>\<surd>"
  --{* cf. 14.13, 14.15, 14.16 *}
  Jmp:                                   "E,dt\<Turnstile>Jmp jump\<Colon>\<surd>"

  --{* cf. 14.16 *}
  Throw: "\<lbrakk>E,dt\<Turnstile>e\<Colon>-Class tn;
	  prg E\<turnstile>tn\<preceq>\<^sub>C SXcpt Throwable\<rbrakk> \<Longrightarrow>
					 E,dt\<Turnstile>Throw e\<Colon>\<surd>"
  --{* cf. 14.18 *}
  Try:	"\<lbrakk>E,dt\<Turnstile>c1\<Colon>\<surd>; prg E\<turnstile>tn\<preceq>\<^sub>C SXcpt Throwable;
	  lcl E (VName vn)=None; E \<lparr>lcl := lcl E(VName vn\<mapsto>Class tn)\<rparr>,dt\<Turnstile>c2\<Colon>\<surd>\<rbrakk>
          \<Longrightarrow>
					 E,dt\<Turnstile>Try c1 Catch(tn vn) c2\<Colon>\<surd>"

  --{* cf. 14.18 *}
  Fin:	"\<lbrakk>E,dt\<Turnstile>c1\<Colon>\<surd>; E,dt\<Turnstile>c2\<Colon>\<surd>\<rbrakk> \<Longrightarrow>
					 E,dt\<Turnstile>c1 Finally c2\<Colon>\<surd>"

  Init:	"\<lbrakk>is_class (prg E) C\<rbrakk> \<Longrightarrow>
					 E,dt\<Turnstile>Init C\<Colon>\<surd>"
  --{* @{term Init} is created on the fly during evaluation (see Eval.thy). 
     The class isn't necessarily accessible from the points @{term Init} 
     is called. Therefor we only demand @{term is_class} and not 
     @{term is_acc_class} here. 
   *}

--{* well-typed expressions *}

  --{* cf. 15.8 *}
  NewC:	"\<lbrakk>is_acc_class (prg E) (pkg E) C\<rbrakk> \<Longrightarrow>
					 E,dt\<Turnstile>NewC C\<Colon>-Class C"
  --{* cf. 15.9 *}
  NewA:	"\<lbrakk>is_acc_type (prg E) (pkg E) T;
	  E,dt\<Turnstile>i\<Colon>-PrimT Integer\<rbrakk> \<Longrightarrow>
					 E,dt\<Turnstile>New T[i]\<Colon>-T.[]"

  --{* cf. 15.15 *}
  Cast:	"\<lbrakk>E,dt\<Turnstile>e\<Colon>-T; is_acc_type (prg E) (pkg E) T';
	  prg E\<turnstile>T\<preceq>? T'\<rbrakk> \<Longrightarrow>
					 E,dt\<Turnstile>Cast T' e\<Colon>-T'"

  --{* cf. 15.19.2 *}
  Inst:	"\<lbrakk>E,dt\<Turnstile>e\<Colon>-RefT T; is_acc_type (prg E) (pkg E) (RefT T');
	  prg E\<turnstile>RefT T\<preceq>? RefT T'\<rbrakk> \<Longrightarrow>
					 E,dt\<Turnstile>e InstOf T'\<Colon>-PrimT Boolean"

  --{* cf. 15.7.1 *}
  Lit:	"\<lbrakk>typeof dt x = Some T\<rbrakk> \<Longrightarrow>
					 E,dt\<Turnstile>Lit x\<Colon>-T"

  UnOp: "\<lbrakk>E,dt\<Turnstile>e\<Colon>-Te; wt_unop unop Te; T=PrimT (unop_type unop)\<rbrakk> 
          \<Longrightarrow>
	  E,dt\<Turnstile>UnOp unop e\<Colon>-T"
  
  BinOp: "\<lbrakk>E,dt\<Turnstile>e1\<Colon>-T1; E,dt\<Turnstile>e2\<Colon>-T2; wt_binop (prg E) binop T1 T2; 
           T=PrimT (binop_type binop)\<rbrakk> 
           \<Longrightarrow>
	   E,dt\<Turnstile>BinOp binop e1 e2\<Colon>-T"
  
  --{* cf. 15.10.2, 15.11.1 *}
  Super: "\<lbrakk>lcl E This = Some (Class C); C \<noteq> Object;
	  class (prg E) C = Some c\<rbrakk> \<Longrightarrow>
					 E,dt\<Turnstile>Super\<Colon>-Class (super c)"

  --{* cf. 15.13.1, 15.10.1, 15.12 *}
  Acc:	"\<lbrakk>E,dt\<Turnstile>va\<Colon>=T\<rbrakk> \<Longrightarrow>
					 E,dt\<Turnstile>Acc va\<Colon>-T"

  --{* cf. 15.25, 15.25.1 *}
  Ass:	"\<lbrakk>E,dt\<Turnstile>va\<Colon>=T; va \<noteq> LVar This;
	  E,dt\<Turnstile>v \<Colon>-T';
	  prg E\<turnstile>T'\<preceq>T\<rbrakk> \<Longrightarrow>
					 E,dt\<Turnstile>va:=v\<Colon>-T'"

  --{* cf. 15.24 *}
  Cond:	"\<lbrakk>E,dt\<Turnstile>e0\<Colon>-PrimT Boolean;
	  E,dt\<Turnstile>e1\<Colon>-T1; E,dt\<Turnstile>e2\<Colon>-T2;
	  prg E\<turnstile>T1\<preceq>T2 \<and> T = T2  \<or>  prg E\<turnstile>T2\<preceq>T1 \<and> T = T1\<rbrakk> \<Longrightarrow>
					 E,dt\<Turnstile>e0 ? e1 : e2\<Colon>-T"

  --{* cf. 15.11.1, 15.11.2, 15.11.3 *}
  Call:	"\<lbrakk>E,dt\<Turnstile>e\<Colon>-RefT statT;
	  E,dt\<Turnstile>ps\<Colon>\<doteq>pTs;
	  max_spec (prg E) (cls E) statT \<lparr>name=mn,parTs=pTs\<rparr> 
            = {((statDeclT,m),pTs')}
         \<rbrakk> \<Longrightarrow>
		   E,dt\<Turnstile>{cls E,statT,invmode m e}e\<cdot>mn({pTs'}ps)\<Colon>-(resTy m)"

  Methd: "\<lbrakk>is_class (prg E) C;
	  methd (prg E) C sig = Some m;
	  E,dt\<Turnstile>Body (declclass m) (stmt (mbody (mthd m)))\<Colon>-T\<rbrakk> \<Longrightarrow>
					 E,dt\<Turnstile>Methd C sig\<Colon>-T"
 --{* The class @{term C} is the dynamic class of the method call 
    (cf. Eval.thy). 
    It hasn't got to be directly accessible from the current package 
    @{term "(pkg E)"}. 
    Only the static class must be accessible (enshured indirectly by 
    @{term Call}). 
    Note that l is just a dummy value. It is only used in the smallstep 
    semantics. To proof typesafety directly for the smallstep semantics 
    we would have to assume conformance of l here!
  *}

  Body:	"\<lbrakk>is_class (prg E) D;
	  E,dt\<Turnstile>blk\<Colon>\<surd>;
	  (lcl E) Result = Some T;
          is_type (prg E) T\<rbrakk> \<Longrightarrow>
   					 E,dt\<Turnstile>Body D blk\<Colon>-T"
--{* The class @{term D} implementing the method must not directly be 
     accessible  from the current package @{term "(pkg E)"}, but can also 
     be indirectly accessible due to inheritance (enshured in @{term Call})
    The result type hasn't got to be accessible in Java! (If it is not 
    accessible you can only assign it to Object).
    For dummy value l see rule @{term Methd}. 
   *}

--{* well-typed variables *}

  --{* cf. 15.13.1 *}
  LVar:	"\<lbrakk>lcl E vn = Some T; is_acc_type (prg E) (pkg E) T\<rbrakk> \<Longrightarrow>
					 E,dt\<Turnstile>LVar vn\<Colon>=T"
  --{* cf. 15.10.1 *}
  FVar:	"\<lbrakk>E,dt\<Turnstile>e\<Colon>-Class C; 
	  accfield (prg E) (cls E) C fn = Some (statDeclC,f)\<rbrakk> \<Longrightarrow>
			 E,dt\<Turnstile>{cls E,statDeclC,is_static f}e..fn\<Colon>=(type f)"
  --{* cf. 15.12 *}
  AVar:	"\<lbrakk>E,dt\<Turnstile>e\<Colon>-T.[]; 
	  E,dt\<Turnstile>i\<Colon>-PrimT Integer\<rbrakk> \<Longrightarrow>
					 E,dt\<Turnstile>e.[i]\<Colon>=T"


--{* well-typed expression lists *}

  --{* cf. 15.11.??? *}
  Nil:					"E,dt\<Turnstile>[]\<Colon>\<doteq>[]"

  --{* cf. 15.11.??? *}
  Cons:	"\<lbrakk>E,dt\<Turnstile>e \<Colon>-T;
	  E,dt\<Turnstile>es\<Colon>\<doteq>Ts\<rbrakk> \<Longrightarrow>
					 E,dt\<Turnstile>e#es\<Colon>\<doteq>T#Ts"


declare not_None_eq [simp del] 
declare split_if [split del] split_if_asm [split del]
declare split_paired_All [simp del] split_paired_Ex [simp del]
ML_setup {*
simpset_ref() := simpset() delloop "split_all_tac"
*}

inductive_cases wt_elim_cases [cases set]:
	"E,dt\<Turnstile>In2  (LVar vn)               \<Colon>T"
	"E,dt\<Turnstile>In2  ({accC,statDeclC,s}e..fn)\<Colon>T"
	"E,dt\<Turnstile>In2  (e.[i])                 \<Colon>T"
	"E,dt\<Turnstile>In1l (NewC C)                \<Colon>T"
	"E,dt\<Turnstile>In1l (New T'[i])             \<Colon>T"
	"E,dt\<Turnstile>In1l (Cast T' e)             \<Colon>T"
	"E,dt\<Turnstile>In1l (e InstOf T')           \<Colon>T"
	"E,dt\<Turnstile>In1l (Lit x)                 \<Colon>T"
        "E,dt\<Turnstile>In1l (UnOp unop e)           \<Colon>T"
        "E,dt\<Turnstile>In1l (BinOp binop e1 e2)     \<Colon>T"
	"E,dt\<Turnstile>In1l (Super)                 \<Colon>T"
	"E,dt\<Turnstile>In1l (Acc va)                \<Colon>T"
	"E,dt\<Turnstile>In1l (Ass va v)              \<Colon>T"
	"E,dt\<Turnstile>In1l (e0 ? e1 : e2)          \<Colon>T"
	"E,dt\<Turnstile>In1l ({accC,statT,mode}e\<cdot>mn({pT'}p))\<Colon>T"
	"E,dt\<Turnstile>In1l (Methd C sig)           \<Colon>T"
	"E,dt\<Turnstile>In1l (Body D blk)            \<Colon>T"
	"E,dt\<Turnstile>In3  ([])                    \<Colon>Ts"
	"E,dt\<Turnstile>In3  (e#es)                  \<Colon>Ts"
	"E,dt\<Turnstile>In1r  Skip                   \<Colon>x"
	"E,dt\<Turnstile>In1r (Expr e)                \<Colon>x"
	"E,dt\<Turnstile>In1r (c1;; c2)               \<Colon>x"
        "E,dt\<Turnstile>In1r (l\<bullet> c)                  \<Colon>x" 
	"E,dt\<Turnstile>In1r (If(e) c1 Else c2)      \<Colon>x"
	"E,dt\<Turnstile>In1r (l\<bullet> While(e) c)         \<Colon>x"
        "E,dt\<Turnstile>In1r (Jmp jump)              \<Colon>x"
	"E,dt\<Turnstile>In1r (Throw e)               \<Colon>x"
	"E,dt\<Turnstile>In1r (Try c1 Catch(tn vn) c2)\<Colon>x"
	"E,dt\<Turnstile>In1r (c1 Finally c2)         \<Colon>x"
	"E,dt\<Turnstile>In1r (Init C)                \<Colon>x"
declare not_None_eq [simp] 
declare split_if [split] split_if_asm [split]
declare split_paired_All [simp] split_paired_Ex [simp]
ML_setup {*
simpset_ref() := simpset() addloop ("split_all_tac", split_all_tac)
*}

lemma is_acc_class_is_accessible: 
  "is_acc_class G P C \<Longrightarrow> G\<turnstile>(Class C) accessible_in P"
by (auto simp add: is_acc_class_def)

lemma is_acc_iface_is_iface: "is_acc_iface G P I \<Longrightarrow> is_iface G I"
by (auto simp add: is_acc_iface_def)

lemma is_acc_iface_Iface_is_accessible: 
  "is_acc_iface G P I \<Longrightarrow> G\<turnstile>(Iface I) accessible_in P"
by (auto simp add: is_acc_iface_def)

lemma is_acc_type_is_type: "is_acc_type G P T \<Longrightarrow> is_type G T"
by (auto simp add: is_acc_type_def)

lemma is_acc_iface_is_accessible:
  "is_acc_type G P T \<Longrightarrow> G\<turnstile>T accessible_in P"
by (auto simp add: is_acc_type_def)

lemma wt_Methd_is_methd: 
  "E\<turnstile>In1l (Methd C sig)\<Colon>T \<Longrightarrow> is_methd (prg E) C sig"
apply (erule_tac wt_elim_cases)
apply clarsimp
apply (erule is_methdI, assumption)
done


text {* Special versions of some typing rules, better suited to pattern 
        match the conclusion (no selectors in the conclusion)
*}

lemma wt_Call: 
"\<lbrakk>E,dt\<Turnstile>e\<Colon>-RefT statT; E,dt\<Turnstile>ps\<Colon>\<doteq>pTs;  
  max_spec (prg E) (cls E) statT \<lparr>name=mn,parTs=pTs\<rparr> 
    = {((statDeclC,m),pTs')};rT=(resTy m);accC=cls E;
 mode = invmode m e\<rbrakk> \<Longrightarrow> E,dt\<Turnstile>{accC,statT,mode}e\<cdot>mn({pTs'}ps)\<Colon>-rT"
by (auto elim: wt.Call)


lemma invocationTypeExpr_noClassD: 
"\<lbrakk> E\<turnstile>e\<Colon>-RefT statT\<rbrakk>
 \<Longrightarrow> (\<forall> statC. statT \<noteq> ClassT statC) \<longrightarrow> invmode m e \<noteq> SuperM"
proof -
  assume wt: "E\<turnstile>e\<Colon>-RefT statT"
  show ?thesis
  proof (cases "e=Super")
    case True
    with wt obtain "C" where "statT = ClassT C" by (blast elim: wt_elim_cases)
    then show ?thesis by blast
  next 
    case False then show ?thesis 
      by (auto simp add: invmode_def split: split_if_asm)
  qed
qed

lemma wt_Super: 
"\<lbrakk>lcl E This = Some (Class C); C \<noteq> Object; class (prg E) C = Some c; D=super c\<rbrakk> 
\<Longrightarrow> E,dt\<Turnstile>Super\<Colon>-Class D"
by (auto elim: wt.Super)

lemma wt_FVar:	
"\<lbrakk>E,dt\<Turnstile>e\<Colon>-Class C; accfield (prg E) (cls E) C fn = Some (statDeclC,f);
  sf=is_static f; fT=(type f); accC=cls E\<rbrakk> 
\<Longrightarrow> E,dt\<Turnstile>{accC,statDeclC,sf}e..fn\<Colon>=fT"
by (auto dest: wt.FVar)


lemma wt_init [iff]: "E,dt\<Turnstile>Init C\<Colon>\<surd> = is_class (prg E) C"
by (auto elim: wt_elim_cases intro: "wt.Init")

declare wt.Skip [iff]

lemma wt_StatRef: 
  "is_acc_type (prg E) (pkg E) (RefT rt) \<Longrightarrow> E\<turnstile>StatRef rt\<Colon>-RefT rt"
apply (rule wt.Cast)
apply  (rule wt.Lit)
apply   (simp (no_asm))
apply  (simp (no_asm_simp))
apply (rule cast.widen)
apply (simp (no_asm))
done

lemma wt_Inj_elim: 
  "\<And>E. E,dt\<Turnstile>t\<Colon>U \<Longrightarrow> case t of 
                       In1 ec \<Rightarrow> (case ec of 
                                    Inl e \<Rightarrow> \<exists>T. U=Inl T  
                                  | Inr s \<Rightarrow> U=Inl (PrimT Void))  
                     | In2 e \<Rightarrow> (\<exists>T. U=Inl T) 
                     | In3 e \<Rightarrow> (\<exists>T. U=Inr T)"
apply (erule wt.induct)
apply auto
done

--{* In the special syntax to distinguish the typing judgements for expressions, 
     statements, variables and expression lists the kind of term corresponds
     to the kind of type in the end e.g. An statement (injection @{term In3} 
    into terms, always has type void (injection @{term Inl} into the generalised
    types. The following simplification procedures establish these kinds of
    correlation. 
 *}

ML {*
fun wt_fun name inj rhs =
let
  val lhs = "E,dt\<Turnstile>" ^ inj ^ " t\<Colon>U"
  val () = qed_goal name (the_context()) (lhs ^ " = (" ^ rhs ^ ")") 
	(K [Auto_tac, ALLGOALS (ftac (thm "wt_Inj_elim")) THEN Auto_tac])
  fun is_Inj (Const (inj,_) $ _) = true
    | is_Inj _                   = false
  fun pred (t as (_ $ (Const ("Pair",_) $
     _ $ (Const ("Pair", _) $ _ $ (Const ("Pair", _) $ _ $
       x))) $ _ )) = is_Inj x
in
  cond_simproc name lhs pred (thm name)
end

val wt_expr_proc  = wt_fun "wt_expr_eq"  "In1l" "\<exists>T.  U=Inl T  \<and> E,dt\<Turnstile>t\<Colon>-T"
val wt_var_proc   = wt_fun "wt_var_eq"   "In2"  "\<exists>T.  U=Inl T  \<and> E,dt\<Turnstile>t\<Colon>=T"
val wt_exprs_proc = wt_fun "wt_exprs_eq" "In3"  "\<exists>Ts. U=Inr Ts \<and> E,dt\<Turnstile>t\<Colon>\<doteq>Ts"
val wt_stmt_proc  = wt_fun "wt_stmt_eq"  "In1r" "U=Inl(PrimT Void)\<and>E,dt\<Turnstile>t\<Colon>\<surd>"
*}

ML {*
Addsimprocs [wt_expr_proc,wt_var_proc,wt_exprs_proc,wt_stmt_proc]
*}

lemma wt_elim_BinOp:
  "\<lbrakk>E,dt\<Turnstile>In1l (BinOp binop e1 e2)\<Colon>T;
    \<And>T1 T2 T3.
       \<lbrakk>E,dt\<Turnstile>e1\<Colon>-T1; E,dt\<Turnstile>e2\<Colon>-T2; wt_binop (prg E) binop T1 T2;
          E,dt\<Turnstile>(if b then In1l e2 else In1r Skip)\<Colon>T3;
          T = Inl (PrimT (binop_type binop))\<rbrakk>
       \<Longrightarrow> P\<rbrakk>
\<Longrightarrow> P"
apply (erule wt_elim_cases)
apply (cases b)
apply auto
done

lemma Inj_eq_lemma [simp]: 
  "(\<forall>T. (\<exists>T'. T = Inj T' \<and> P T') \<longrightarrow> Q T) = (\<forall>T'. P T' \<longrightarrow> Q (Inj T'))"
by auto

(* unused *)
lemma single_valued_tys_lemma [rule_format (no_asm)]: 
  "\<forall>S T. G\<turnstile>S\<preceq>T \<longrightarrow> G\<turnstile>T\<preceq>S \<longrightarrow> S = T \<Longrightarrow> E,dt\<Turnstile>t\<Colon>T \<Longrightarrow>  
     G = prg E \<longrightarrow> (\<forall>T'. E,dt\<Turnstile>t\<Colon>T' \<longrightarrow> T  = T')"
apply (cases "E", erule wt.induct)
apply (safe del: disjE)
apply (simp_all (no_asm_use) split del: split_if_asm)
apply (safe del: disjE)
(* 17 subgoals *)
apply (tactic {* ALLGOALS (fn i => if i = 11 then EVERY'[thin_tac "?E,dt\<Turnstile>e0\<Colon>-PrimT Boolean", thin_tac "?E,dt\<Turnstile>e1\<Colon>-?T1", thin_tac "?E,dt\<Turnstile>e2\<Colon>-?T2"] i else thin_tac "All ?P" i) *})
(*apply (safe del: disjE elim!: wt_elim_cases)*)
apply (tactic {*ALLGOALS (eresolve_tac (thms "wt_elim_cases"))*})
apply (simp_all (no_asm_use) split del: split_if_asm)
apply (erule_tac [12] V = "All ?P" in thin_rl) (* Call *)
apply ((blast del: equalityCE dest: sym [THEN trans])+)
done

(* unused *)
lemma single_valued_tys: 
"ws_prog (prg E) \<Longrightarrow> single_valued {(t,T). E,dt\<Turnstile>t\<Colon>T}"
apply (unfold single_valued_def)
apply clarsimp
apply (rule single_valued_tys_lemma)
apply (auto intro!: widen_antisym)
done

lemma typeof_empty_is_type [rule_format (no_asm)]: 
  "typeof (\<lambda>a. None) v = Some T \<longrightarrow> is_type G T"
apply (rule val.induct)
apply    	auto
done

(* unused *)
lemma typeof_is_type [rule_format (no_asm)]: 
 "(\<forall>a. v \<noteq> Addr a) \<longrightarrow> (\<exists>T. typeof dt v = Some T \<and> is_type G T)"
apply (rule val.induct)
prefer 5 
apply     fast
apply  (simp_all (no_asm))
done

end
