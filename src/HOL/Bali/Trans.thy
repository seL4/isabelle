(*  Title:      HOL/Bali/Trans.thy
    ID:         $Id$
    Author:     David von Oheimb
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Operational transition (small-step) semantics of the 
execution of Java expressions and statements

PRELIMINARY!!!!!!!!

improvements over Java Specification 1.0 (cf. 15.11.4.4):
* dynamic method lookup does not need to check the return type
* throw raises a NullPointer exception if a null reference is given, and each
  throw of a system exception yield a fresh exception object (was not specified)
* if there is not enough memory even to allocate an OutOfMemory exception,
  evaluation/execution fails, i.e. simply stops (was not specified)

design issues:
* Lit expressions and Skip statements are considered completely evaluated.
* the expr entry in rules is redundant in case of exceptions, but its full
  inclusion helps to make the rule structure independent of exception occurence.
* the rule format is such that the start state may contain an exception.
  ++ faciliates exception handling (to be added later)
  +  symmetry
* the rules are defined carefully in order to be applicable even in not
  type-correct situations (yielding undefined values),
  e.g. the_Adr (Val (Bool b)) = arbitrary.
  ++ fewer rules 
  -  less readable because of auxiliary functions like the_Adr
  Alternative: "defensive" evaluation throwing some InternalError exception
               in case of (impossible, for correct programs) type mismatches

simplifications:
* just simple handling (i.e. propagation) of exceptions so far
* dynamic method lookup does not check return type (should not be necessary)
*)

Trans = Eval +

consts
  texpr_tstmt	:: "prog л (((expr т state) т (expr т state)) +
		            ((stmt т state) т (stmt т state))) set"

syntax (symbols)
  texpr :: "[prog, expr т state, expr т state] л bool "("_Й_ и1 _"[61,82,82] 81)
  tstmt :: "[prog, stmt т state, stmt т state] л bool "("_Й_ н1 _"[61,82,82] 81)
  Ref   :: "loc л expr"

translations

  "GЙe_s и1 ex_s'" == "Inl (e_s, ex_s') О texpr_tstmt G"
  "GЙs_s н1 s'_s'" == "Inr (s_s, s'_s') О texpr_tstmt G"
  "Ref a" == "Lit (Addr a)"

constdefs
  
  sub_expr_expr :: "(expr л expr) л prop"
  "sub_expr_expr ef Ъ (ДG e s e' s'. GЙ(   e,s) и1 (   e',s') кл
				     GЙ(ef e,s) и1 (ef e',s'))"

inductive "texpr_tstmt G" intrs 

(* evaluation of expression *)
  (* cf. 15.5 *)
  XcptE	"ЛВv. e Ы Lit vМ кл
				  GЙ(e,Some xc,s) и1 (Lit arbitrary,Some xc,s)"

 CastXX "PROP sub_expr_expr (Cast T)"

(*
  (* cf. 15.8.1 *)
  NewC	"Лnew_Addr (heap s) = Some (a,x);
	  s' = assign (hupd[aнinit_Obj G C]s) (x,s)М кл
				GЙ(NewC C,None,s) и1 (Ref a,s')"

  (* cf. 15.9.1 *)
(*NewA1	"sub_expr_expr (NewA T)"*)
  NewA1	"ЛGЙ(e,None,s) и1 (e',s')М кл
			      GЙ(New T[e],None,s) и1 (New T[e'],s')"
  NewA	"Лi = the_Intg i'; new_Addr (heap s) = Some (a, x);
	  s' = assign (hupd[aнinit_Arr T i]s)(raise_if (i<#0) NegArrSize x,s)М кл
			GЙ(New T[Lit i'],None,s) и1 (Ref a,s')"
  (* cf. 15.15 *)
  Cast1	"ЛGЙ(e,None,s) и1 (e',s')М кл
			      GЙ(Cast T e,None,s) и1 (Cast T e',s')"
  Cast	"Лx'= raise_if (\<questiondown>G,sЙv fits T) ClassCast NoneМ кл
		        GЙ(Cast T (Lit v),None,s) и1 (Lit v,x',s)"

  (* cf. 15.7.1 *)
(*Lit				"GЙ(Lit v,None,s) и1 (Lit v,None,s)"*)

  (* cf. 15.13.1, 15.2 *)
  LAcc	"Лv = the (locals s vn)М кл
			       GЙ(LAcc vn,None,s) и1 (Lit v,None,s)"

  (* cf. 15.25.1 *)
  LAss1	"ЛGЙ(e,None,s) и1 (e',s')М кл
				 GЙ(f vn:=e,None,s) и1 (vn:=e',s')"
  LAss			    "GЙ(f vn:=Lit v,None,s) и1 (Lit v,None,lupd[vnнv]s)"

  (* cf. 15.10.1, 15.2 *)
  FAcc1	"ЛGЙ(e,None,s) и1 (e',s')М кл
			       GЙ({T}e..fn,None,s) и1 ({T}e'..fn,s')"
  FAcc	"Лv = the (snd (the_Obj (heap s (the_Addr a'))) (fn,T))М кл
			  GЙ({T}Lit a'..fn,None,s) и1 (Lit v,np a' None,s)"

  (* cf. 15.25.1 *)
  FAss1	"ЛGЙ(e1,None,s) и1 (e1',s')М кл
			  GЙ(f ({T}e1..fn):=e2,None,s) и1 (f({T}e1'..fn):=e2,s')"
  FAss2	"ЛGЙ(e2,np a' None,s) и1 (e2',s')М кл
		      GЙ(f({T}Lit a'..fn):=e2,None,s) и1 (f({T}Lit a'..fn):=e2',s')"
  FAss	"Лa = the_Addr a'; (c,fs) = the_Obj (heap s a);
	  s'= assign (hupd[aнObj c (fs[(fn,T)нv])]s) (None,s)М кл
		   GЙ(f({T}Lit a'..fn):=Lit v,None,s) и1 (Lit v,s')"





  (* cf. 15.12.1 *)
  AAcc1	"ЛGЙ(e1,None,s) и1 (e1',s')М кл
				GЙ(e1[e2],None,s) и1 (e1'[e2],s')"
  AAcc2	"ЛGЙ(e2,None,s) и1 (e2',s')М кл
			    GЙ(Lit a'[e2],None,s) и1 (Lit a'[e2'],s')"
  AAcc	"Лvo = snd (the_Arr (heap s (the_Addr a'))) (the_Intg i');
	  x' = raise_if (vo = None) IndOutBound (np a' None)М кл
			GЙ(Lit a'[Lit i'],None,s) и1 (Lit (the vo),x',s)"


  (* cf. 15.11.4.1, 15.11.4.2, 15.11.4.4, 15.11.4.5, 14.15 *)
  Call1	"ЛGЙ(e,None,s) и1 (e',s')М кл
			  GЙ(e..mn({pT}p),None,s) и1 (e'..mn({pT}p),s')"
  Call2	"ЛGЙ(p,None,s) и1 (p',s')М кл
		     GЙ(Lit a'..mn({pT}p),None,s) и1 (Lit a'..mn({pT}p'),s')"
  Call	"Лa = the_Addr a'; (md,(pn,rT),lvars,blk,res) = 
 			   the (cmethd G (fst (the_Obj (h a))) (mn,pT))М кл
	    GЙ(Lit a'..mn({pT}Lit pv),None,(h,l)) и1 
      (Body blk res l,np a' x,(h,init_vals lvars[Thisнa'][Superнa'][pnнpv]))"
  Body1	"ЛGЙ(s0,None,s) н1 (s0',s')М кл
		   GЙ(Body s0    e      l,None,s) и1 (Body s0'  e  l,s')"
  Body2	"ЛGЙ(e ,None,s) и1 (e',s')М кл
		   GЙ(Body Skip  e      l,None,s) и1 (Body Skip e' l,s')"
  Body		  "GЙ(Body Skip (Lit v) l,None,s) и1 (Lit v,None,(heap s,l))"

(* execution of statements *)

  (* cf. 14.1 *)
  XcptS	"Лs0 Ы SkipМ кл
				 GЙ(s0,Some xc,s) н1 (Skip,Some xc,s)"

  (* cf. 14.5 *)
(*Skip	 			 "GЙ(Skip,None,s) н1 (Skip,None,s)"*)

  (* cf. 14.2 *)
  Comp1	"ЛGЙ(s1,None,s) н1 (s1',s')М кл
			       GЙ(s1;; s2,None,s) н1 (s1';; s2,s')"
  Comp			    "GЙ(Skip;; s2,None,s) н1 (s2,None,s)"






  (* cf. 14.7 *)
  Expr1	"ЛGЙ(e ,None,s) и1 (e',s')М кл
				GЙ(Expr e,None,s) н1 (Expr e',s')"
  Expr			 "GЙ(Expr (Lit v),None,s) н1 (Skip,None,s)"

  (* cf. 14.8.2 *)
  If1	"ЛGЙ(e ,None,s) и1 (e',s')М кл
		      GЙ(If(e) s1 Else s2,None,s) н1 (If(e') s1 Else s2,s')"
  If		 "GЙ(If(Lit v) s1 Else s2,None,s) н1 
		    (if the_Bool v then s1 else s2,None,s)"

  (* cf. 14.10, 14.10.1 *)
  Loop			  "GЙ(While(e) s0,None,s) н1 
			     (If(e) (s0;; While(e) s0) Else Skip,None,s)"
*)
  con_defs "[sub_expr_expr_def]"

end
