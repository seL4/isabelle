(*  Title:      HOL/MicroJava/J/WellType.thy
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   1999 Technische Universitaet Muenchen

Well-typedness of Java programs

the formulation of well-typedness of method calls given below (as well as
the Java Specification 1.0) is a little too restrictive: Is does not allow
methods of class Object to be called upon references of interface type.

simplifications:
* the type rules include all static checks on expressions and statements, e.g.
  definedness of names (of parameters, locals, fields, methods)

*)

WellType = Term + WellForm +

types	lenv (* local variables, including method parameters and This *)
	= "vname \\<leadsto> ty"
        'c env
	= "'c prog \\<times> lenv"

syntax

  prg		:: "'c env \\<Rightarrow> 'c prog"
  localT	:: "'c env \\<Rightarrow> (vname \\<leadsto> ty)"

translations	

  "prg"		=> "fst"
  "localT"	=> "snd"

consts

  more_spec	:: "'c prog \\<Rightarrow> (ty \\<times> 'x) \\<times> ty list \\<Rightarrow>
		               (ty \\<times> 'x) \\<times> ty list \\<Rightarrow> bool"
  m_head	:: "'c prog \\<Rightarrow>  ref_ty \\<Rightarrow> sig \\<Rightarrow>  (ty \\<times> ty) option"
  appl_methds	:: "'c prog \\<Rightarrow>  ref_ty \\<Rightarrow> sig \\<Rightarrow> ((ty \\<times> ty) \\<times> ty list) set"
  max_spec	:: "'c prog \\<Rightarrow>  ref_ty \\<Rightarrow> sig \\<Rightarrow> ((ty \\<times> ty) \\<times> ty list) set"

defs

  m_head_def  "m_head G t sig \\<equiv> case t of NullT \\<Rightarrow> None | ClassT C \\<Rightarrow>
		 option_map (\\<lambda>(md,(rT,mb)). (Class md,rT)) (method (G,C) sig)"
                                                               
  more_spec_def	  "more_spec G \\<equiv> \\<lambda>((d,h),pTs). \\<lambda>((d',h'),pTs'). G\\<turnstile>d\\<preceq>d' \\<and>
		                  list_all2 (\\<lambda>T T'. G\\<turnstile>T\\<preceq>T') pTs pTs'"
  
  (* applicable methods, cf. 15.11.2.1 *)
  appl_methds_def "appl_methds G T \\<equiv> \\<lambda>(mn, pTs). {(mh,pTs') |mh pTs'.
		                  m_head G T (mn, pTs') = Some mh \\<and>
		                  list_all2 (\\<lambda>T T'. G\\<turnstile>T\\<preceq>T') pTs pTs'}"

  (* maximally specific methods, cf. 15.11.2.2 *)
   max_spec_def	  "max_spec G rT sig \\<equiv> {m. m \\<in>appl_methds G rT sig \\<and> 
				          (\\<forall>m'\\<in>appl_methds G rT sig.
				                   more_spec G m' m \\<longrightarrow> m' = m)}"
consts

  typeof :: "(loc \\<Rightarrow> ty option) \\<Rightarrow> val \\<Rightarrow> ty option"

primrec
	"typeof dt  Unit    = Some (PrimT Void)"
	"typeof dt  Null    = Some NT"
	"typeof dt (Bool b) = Some (PrimT Boolean)"
	"typeof dt (Intg i) = Some (PrimT Integer)"
	"typeof dt (Addr a) = dt a"

types
	javam = "vname list \\<times> (vname \\<times> ty) list \\<times> stmt \\<times> expr"
	(* method body with parameter names, local variables, block, result expression *)

consts

  ty_expr :: "javam env \\<Rightarrow> (expr      \\<times> ty     ) set"
  ty_exprs:: "javam env \\<Rightarrow> (expr list \\<times> ty list) set"
  wt_stmt :: "javam env \\<Rightarrow>  stmt                 set"

syntax

ty_expr :: "javam env \\<Rightarrow> [expr     , ty     ] \\<Rightarrow> bool" ("_\\<turnstile>_\\<Colon>_"  [51,51,51]50)
ty_exprs:: "javam env \\<Rightarrow> [expr list, ty list] \\<Rightarrow> bool" ("_\\<turnstile>_[\\<Colon>]_"[51,51,51]50)
wt_stmt :: "javam env \\<Rightarrow>  stmt                \\<Rightarrow> bool" ("_\\<turnstile>_ \\<surd>" [51,51   ]50)

translations
	"E\\<turnstile>e \\<Colon> T" == "(e,T) \\<in> ty_expr  E"
	"E\\<turnstile>e[\\<Colon>]T" == "(e,T) \\<in> ty_exprs E"
	"E\\<turnstile>c \\<surd>"    == "c     \\<in> wt_stmt  E"
  
inductive "ty_expr E" "ty_exprs E" "wt_stmt E" intrs

(* well-typed expressions *)

  (* cf. 15.8 *)
  NewC	"\\<lbrakk>is_class (prg E) C\\<rbrakk> \\<Longrightarrow>
						 E\\<turnstile>NewC C\\<Colon>Class C"

  (* cf. 15.15 *)
  Cast	"\\<lbrakk>E\\<turnstile>e\\<Colon>T;
	  prg E\\<turnstile>T\\<Rightarrow>? T'\\<rbrakk> \\<Longrightarrow>
						 E\\<turnstile>Cast T' e\\<Colon>T'"

  (* cf. 15.7.1 *)
  Lit	"\\<lbrakk>typeof (\\<lambda>v. None) x = Some T\\<rbrakk> \\<Longrightarrow>
						 E\\<turnstile>Lit x\\<Colon>T"

  (* cf. 15.13.1 *)
  LAcc	"\\<lbrakk>localT E v = Some T; is_type (prg E) T\\<rbrakk> \\<Longrightarrow>
						 E\\<turnstile>LAcc v\\<Colon>T"
  
  (* cf. 15.25, 15.25.1 *)
  LAss  "\\<lbrakk>E\\<turnstile>LAcc v\\<Colon>T;
	   E\\<turnstile>e\\<Colon>T';
	   prg E\\<turnstile>T'\\<preceq>T\\<rbrakk> \\<Longrightarrow>
						 E\\<turnstile>v\\<Colon>=e\\<Colon>T'"

  (* cf. 15.10.1 *)
  FAcc	"\\<lbrakk>E\\<turnstile>a\\<Colon>Class C; 
	  field (prg E,C) fn = Some (fd,fT)\\<rbrakk> \\<Longrightarrow>
						 E\\<turnstile>{fd}a..fn\\<Colon>fT"

  (* cf. 15.25, 15.25.1 *)
  FAss  "\\<lbrakk>E\\<turnstile>{fd}a..fn\\<Colon>T;
	  E\\<turnstile>v       \\<Colon>T';
	  prg E\\<turnstile>T'\\<preceq>T\\<rbrakk> \\<Longrightarrow>
					 	 E\\<turnstile>{fd}a..fn\\<in>=v\\<Colon>T'"


  (* cf. 15.11.1, 15.11.2, 15.11.3 *)
  Call	"\\<lbrakk>E\\<turnstile>a\\<Colon>RefT t;
	  E\\<turnstile>ps[\\<Colon>]pTs;
	  max_spec (prg E) t (mn, pTs) = {((md,rT),pTs')}\\<rbrakk> \\<Longrightarrow>
						 E\\<turnstile>a..mn({pTs'}ps)\\<Colon>rT"

(* well-typed expression lists *)

  (* cf. 15.11.??? *)
  Nil						"E\\<turnstile>[][\\<Colon>][]"

  (* cf. 15.11.??? *)
  Cons	"\\<lbrakk>E\\<turnstile>e\\<Colon>T;
	   E\\<turnstile>es[\\<Colon>]Ts\\<rbrakk> \\<Longrightarrow>
						 E\\<turnstile>e#es[\\<Colon>]T#Ts"

(* well-typed statements *)

  Skip					"E\\<turnstile>Skip\\<surd>"

  Expr	"\\<lbrakk>E\\<turnstile>e\\<Colon>T\\<rbrakk> \\<Longrightarrow>
					 E\\<turnstile>Expr e\\<surd>"

 Comp	"\\<lbrakk>E\\<turnstile>s1\\<surd>; 
	  E\\<turnstile>s2\\<surd>\\<rbrakk> \\<Longrightarrow>
					 E\\<turnstile>s1;; s2\\<surd>"

  (* cf. 14.8 *)
  Cond	"\\<lbrakk>E\\<turnstile>e\\<Colon>PrimT Boolean;
	  E\\<turnstile>s1\\<surd>;
	  E\\<turnstile>s2\\<surd>\\<rbrakk> \\<Longrightarrow>
					 E\\<turnstile>If(e) s1 Else s2\\<surd>"

  (* cf. 14.10 *)
  Loop "\\<lbrakk>E\\<turnstile>e\\<Colon>PrimT Boolean;
	 E\\<turnstile>s\\<surd>\\<rbrakk> \\<Longrightarrow>
					 E\\<turnstile>While(e) s\\<surd>"

constdefs

 wt_java_mdecl :: javam prog => cname => javam mdecl => bool
"wt_java_mdecl G C \\<equiv> \\<lambda>((mn,pTs),rT,(pns,lvars,blk,res)).
	length pTs = length pns \\<and>
	nodups pns \\<and>
	unique lvars \\<and>
	(\\<forall>pn\\<in>set pns. map_of lvars pn = None) \\<and>
	(\\<forall>(vn,T)\\<in>set lvars. is_type G T) &
	(let E = (G,map_of lvars(pns[\\<mapsto>]pTs)(This\\<mapsto>Class C)) in
	 E\\<turnstile>blk\\<surd> \\<and> (\\<exists>T. E\\<turnstile>res\\<Colon>T \\<and> G\\<turnstile>T\\<preceq>rT))"

 wf_java_prog :: javam prog => bool
"wf_java_prog G \\<equiv> wf_prog wt_java_mdecl G"

end
