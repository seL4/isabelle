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

  prg		:: "'c env => 'c prog"
  localT	:: "'c env => (vname \\<leadsto> ty)"

translations	

  "prg"		=> "fst"
  "localT"	=> "snd"

consts

  more_spec	:: "'c prog => (ty \\<times> 'x) \\<times> ty list =>
		               (ty \\<times> 'x) \\<times> ty list => bool"
  appl_methds	:: "'c prog =>  cname => sig => ((ty \\<times> ty) \\<times> ty list) set"
  max_spec	:: "'c prog =>  cname => sig => ((ty \\<times> ty) \\<times> ty list) set"

defs

  more_spec_def	  "more_spec G == \\<lambda>((d,h),pTs). \\<lambda>((d',h'),pTs'). G\\<turnstile>d\\<preceq>d' \\<and>
		                  list_all2 (\\<lambda>T T'. G\\<turnstile>T\\<preceq>T') pTs pTs'"
  
  (* applicable methods, cf. 15.11.2.1 *)
  appl_methds_def "appl_methds G C == \\<lambda>(mn, pTs).
		                 {((Class md,rT),pTs') |md rT mb pTs'.
		                  method (G,C)  (mn, pTs') = Some (md,rT,mb) \\<and>
		                  list_all2 (\\<lambda>T T'. G\\<turnstile>T\\<preceq>T') pTs pTs'}"

  (* maximally specific methods, cf. 15.11.2.2 *)
   max_spec_def	  "max_spec G C sig == {m. m \\<in>appl_methds G C sig \\<and> 
				          (\\<forall>m'\\<in>appl_methds G C sig.
				                   more_spec G m' m --> m' = m)}"
consts

  typeof :: "(loc => ty option) => val => ty option"

primrec
	"typeof dt  Unit    = Some (PrimT Void)"
	"typeof dt  Null    = Some NT"
	"typeof dt (Bool b) = Some (PrimT Boolean)"
	"typeof dt (Intg i) = Some (PrimT Integer)"
	"typeof dt (Addr a) = dt a"

types
	java_mb = "vname list \\<times> (vname \\<times> ty) list \\<times> stmt \\<times> expr"
	(* method body with parameter names, local variables, block, result expression *)

consts

  ty_expr :: "java_mb env => (expr      \\<times> ty     ) set"
  ty_exprs:: "java_mb env => (expr list \\<times> ty list) set"
  wt_stmt :: "java_mb env =>  stmt                 set"

syntax

ty_expr :: "java_mb env => [expr     , ty     ] => bool" ("_\\<turnstile>_::_"  [51,51,51]50)
ty_exprs:: "java_mb env => [expr list, ty list] => bool" ("_\\<turnstile>_[::]_"[51,51,51]50)
wt_stmt :: "java_mb env =>  stmt                => bool" ("_\\<turnstile>_ \\<surd>" [51,51   ]50)

translations
	"E\\<turnstile>e :: T" == "(e,T) \\<in> ty_expr  E"
	"E\\<turnstile>e[::]T" == "(e,T) \\<in> ty_exprs E"
	"E\\<turnstile>c \\<surd>"    == "c     \\<in> wt_stmt  E"
  
inductive "ty_expr E" "ty_exprs E" "wt_stmt E" intrs

(* well-typed expressions *)

  (* cf. 15.8 *)
  NewC	"[|is_class (prg E) C|] ==>
						 E\\<turnstile>NewC C::Class C"

  (* cf. 15.15 *)
  Cast	"[|E\\<turnstile>e::Class C;
	  prg E\\<turnstile>C\\<preceq>? D|] ==>
						 E\\<turnstile>Cast D e::Class D"

  (* cf. 15.7.1 *)
  Lit	"[|typeof (\\<lambda>v. None) x = Some T|] ==>
						 E\\<turnstile>Lit x::T"

  
  (* cf. 15.13.1 *)
  LAcc	"[|localT E v = Some T; is_type (prg E) T|] ==>
						 E\\<turnstile>LAcc v::T"

  BinOp "[|E\\<turnstile>e1::T;
	  E\\<turnstile>e2::T;
	  if bop = Eq then T' = PrimT Boolean
	              else T' = T \\<and> T = PrimT Integer|] ==>
						 E\\<turnstile>BinOp bop e1 e2::T'"

  (* cf. 15.25, 15.25.1 *)
  LAss  "[|E\\<turnstile>LAcc v::T;
	  E\\<turnstile>e::T';
	  prg E\\<turnstile>T'\\<preceq>T|] ==>
						 E\\<turnstile>v::=e::T'"

  (* cf. 15.10.1 *)
  FAcc	"[|E\\<turnstile>a::Class C; 
	  field (prg E,C) fn = Some (fd,fT)|] ==>
						 E\\<turnstile>{fd}a..fn::fT"

  (* cf. 15.25, 15.25.1 *)
  FAss  "[|E\\<turnstile>{fd}a..fn::T;
	  E\\<turnstile>v       ::T';
	  prg E\\<turnstile>T'\\<preceq>T|] ==>
					 	 E\\<turnstile>{fd}a..fn:=v::T'"


  (* cf. 15.11.1, 15.11.2, 15.11.3 *)
  Call	"[|E\\<turnstile>a::Class C;
	  E\\<turnstile>ps[::]pTs;
	  max_spec (prg E) C (mn, pTs) = {((md,rT),pTs')}|] ==>
						 E\\<turnstile>a..mn({pTs'}ps)::rT"

(* well-typed expression lists *)

  (* cf. 15.11.??? *)
  Nil						"E\\<turnstile>[][::][]"

  (* cf. 15.11.??? *)
  Cons	"[|E\\<turnstile>e::T;
	   E\\<turnstile>es[::]Ts|] ==>
						 E\\<turnstile>e#es[::]T#Ts"

(* well-typed statements *)

  Skip					"E\\<turnstile>Skip\\<surd>"

  Expr	"[|E\\<turnstile>e::T|] ==>
					 E\\<turnstile>Expr e\\<surd>"

  Comp	"[|E\\<turnstile>s1\\<surd>; 
	  E\\<turnstile>s2\\<surd>|] ==>
					 E\\<turnstile>s1;; s2\\<surd>"

  (* cf. 14.8 *)
  Cond	"[|E\\<turnstile>e::PrimT Boolean;
	  E\\<turnstile>s1\\<surd>;
	  E\\<turnstile>s2\\<surd>|] ==>
					 E\\<turnstile>If(e) s1 Else s2\\<surd>"

  (* cf. 14.10 *)
  Loop "[|E\\<turnstile>e::PrimT Boolean;
	 E\\<turnstile>s\\<surd>|] ==>
					 E\\<turnstile>While(e) s\\<surd>"

constdefs

 wf_java_mdecl :: java_mb prog => cname => java_mb mdecl => bool
"wf_java_mdecl G C == \\<lambda>((mn,pTs),rT,(pns,lvars,blk,res)).
	length pTs = length pns \\<and>
	nodups pns \\<and>
	unique lvars \\<and>
	(\\<forall>pn\\<in>set pns. map_of lvars pn = None) \\<and>
	(\\<forall>(vn,T)\\<in>set lvars. is_type G T) &
	(let E = (G,map_of lvars(pns[\\<mapsto>]pTs)(This\\<mapsto>Class C)) in
	 E\\<turnstile>blk\\<surd> \\<and> (\\<exists>T. E\\<turnstile>res::T \\<and> G\\<turnstile>T\\<preceq>rT))"

 wf_java_prog :: java_mb prog => bool
"wf_java_prog G == wf_prog wf_java_mdecl G"

end
