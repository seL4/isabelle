(*  Title:      HOL/Bali/Trans.thy
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   1997 Technische Universitaet Muenchen

Operational transition (small-step) semantics of the 
execution of Java expressions and statements

PRELIMINARY!!!!!!!!

*)

Trans = Eval +

consts
  texpr_tstmt	:: "prog \<Rightarrow> (((expr \<times> state) \<times> (expr \<times> state)) +
		            ((stmt \<times> state) \<times> (stmt \<times> state))) set"

syntax (symbols)
  texpr :: "[prog, expr \<times> state, expr \<times> state] \<Rightarrow> bool "("_\<turnstile>_ \<rightarrow>1 _"[61,82,82] 81)
  tstmt :: "[prog, stmt \<times> state, stmt \<times> state] \<Rightarrow> bool "("_\<turnstile>_ \<mapsto>1 _"[61,82,82] 81)
  Ref   :: "loc \<Rightarrow> expr"

translations

  "G\<turnstile>e_s \<rightarrow>1 ex_s'" == "Inl (e_s, ex_s') \<in> texpr_tstmt G"
  "G\<turnstile>s_s \<mapsto>1 s'_s'" == "Inr (s_s, s'_s') \<in> texpr_tstmt G"
  "Ref a" == "Lit (Addr a)"

inductive "texpr_tstmt G" intrs 

(* evaluation of expression *)
  (* cf. 15.5 *)
  XcptE	"\<lbrakk>\<forall>v. e \<noteq> Lit v\<rbrakk> \\<Longrightarrow>
				  G\<turnstile>(e,Some xc,s) \<rightarrow>1 (Lit arbitrary,Some xc,s)"

  (* cf. 15.8.1 *)
  NewC	"\<lbrakk>new_Addr (heap s) = Some (a,x);
	  s' = assign (hupd[a\<mapsto>init_Obj G C]s) (x,s)\<rbrakk> \\<Longrightarrow>
				G\<turnstile>(NewC C,None,s) \<rightarrow>1 (Ref a,s')"

  (* cf. 15.9.1 *)
  NewA1	"\<lbrakk>G\<turnstile>(e,None,s) \<rightarrow>1 (e',s')\<rbrakk> \\<Longrightarrow>
			      G\<turnstile>(New T[e],None,s) \<rightarrow>1 (New T[e'],s')"
  NewA	"\<lbrakk>i = the_Intg i'; new_Addr (heap s) = Some (a, x);
	  s' = assign (hupd[a\<mapsto>init_Arr T i]s)(raise_if (i<#0) NegArrSize x,s)\<rbrakk> \\<Longrightarrow>
			G\<turnstile>(New T[Lit i'],None,s) \<rightarrow>1 (Ref a,s')"
  (* cf. 15.15 *)
  Cast1	"\<lbrakk>G\<turnstile>(e,None,s) \<rightarrow>1 (e',s')\<rbrakk> \\<Longrightarrow>
			      G\<turnstile>(Cast T e,None,s) \<rightarrow>1 (Cast T e',s')"
  Cast	"\<lbrakk>x'= raise_if (\<questiondown>G,s\<turnstile>v fits T) ClassCast None\<rbrakk> \\<Longrightarrow>
		        G\<turnstile>(Cast T (Lit v),None,s) \<rightarrow>1 (Lit v,x',s)"

  (* cf. 15.7.1 *)
(*Lit				"G\<turnstile>(Lit v,None,s) \<rightarrow>1 (Lit v,None,s)"*)

  (* cf. 15.13.1, 15.2 *)
  LAcc	"\<lbrakk>v = the (locals s vn)\<rbrakk> \\<Longrightarrow>
			       G\<turnstile>(LAcc vn,None,s) \<rightarrow>1 (Lit v,None,s)"

  (* cf. 15.25.1 *)
  LAss1	"\<lbrakk>G\<turnstile>(e,None,s) \<rightarrow>1 (e',s')\<rbrakk> \\<Longrightarrow>
				 G\<turnstile>(f vn:=e,None,s) \<rightarrow>1 (vn:=e',s')"
  LAss			    "G\<turnstile>(f vn:=Lit v,None,s) \<rightarrow>1 (Lit v,None,lupd[vn\<mapsto>v]s)"

  (* cf. 15.10.1, 15.2 *)
  FAcc1	"\<lbrakk>G\<turnstile>(e,None,s) \<rightarrow>1 (e',s')\<rbrakk> \\<Longrightarrow>
			       G\<turnstile>({T}e..fn,None,s) \<rightarrow>1 ({T}e'..fn,s')"
  FAcc	"\<lbrakk>v = the (snd (the_Obj (heap s (the_Addr a'))) (fn,T))\<rbrakk> \\<Longrightarrow>
			  G\<turnstile>({T}Lit a'..fn,None,s) \<rightarrow>1 (Lit v,np a' None,s)"

  (* cf. 15.25.1 *)
  FAss1	"\<lbrakk>G\<turnstile>(e1,None,s) \<rightarrow>1 (e1',s')\<rbrakk> \\<Longrightarrow>
			  G\<turnstile>(f ({T}e1..fn):=e2,None,s) \<rightarrow>1 (f({T}e1'..fn):=e2,s')"
  FAss2	"\<lbrakk>G\<turnstile>(e2,np a' None,s) \<rightarrow>1 (e2',s')\<rbrakk> \\<Longrightarrow>
		      G\<turnstile>(f({T}Lit a'..fn):=e2,None,s) \<rightarrow>1 (f({T}Lit a'..fn):=e2',s')"
  FAss	"\<lbrakk>a = the_Addr a'; (c,fs) = the_Obj (heap s a);
	  s'= assign (hupd[a\<mapsto>Obj c (fs[(fn,T)\<mapsto>v])]s) (None,s)\<rbrakk> \\<Longrightarrow>
		   G\<turnstile>(f({T}Lit a'..fn):=Lit v,None,s) \<rightarrow>1 (Lit v,s')"





  (* cf. 15.12.1 *)
  AAcc1	"\<lbrakk>G\<turnstile>(e1,None,s) \<rightarrow>1 (e1',s')\<rbrakk> \\<Longrightarrow>
				G\<turnstile>(e1[e2],None,s) \<rightarrow>1 (e1'[e2],s')"
  AAcc2	"\<lbrakk>G\<turnstile>(e2,None,s) \<rightarrow>1 (e2',s')\<rbrakk> \\<Longrightarrow>
			    G\<turnstile>(Lit a'[e2],None,s) \<rightarrow>1 (Lit a'[e2'],s')"
  AAcc	"\<lbrakk>vo = snd (the_Arr (heap s (the_Addr a'))) (the_Intg i');
	  x' = raise_if (vo = None) IndOutBound (np a' None)\<rbrakk> \\<Longrightarrow>
			G\<turnstile>(Lit a'[Lit i'],None,s) \<rightarrow>1 (Lit (the vo),x',s)"


  (* cf. 15.11.4.1, 15.11.4.2, 15.11.4.4, 15.11.4.5, 14.15 *)
  Call1	"\<lbrakk>G\<turnstile>(e,None,s) \<rightarrow>1 (e',s')\<rbrakk> \\<Longrightarrow>
			  G\<turnstile>(e..mn({pT}p),None,s) \<rightarrow>1 (e'..mn({pT}p),s')"
  Call2	"\<lbrakk>G\<turnstile>(p,None,s) \<rightarrow>1 (p',s')\<rbrakk> \\<Longrightarrow>
		     G\<turnstile>(Lit a'..mn({pT}p),None,s) \<rightarrow>1 (Lit a'..mn({pT}p'),s')"
  Call	"\<lbrakk>a = the_Addr a'; (md,(pn,rT),lvars,blk,res) = 
 			   the (cmethd G (fst (the_Obj (h a))) (mn,pT))\<rbrakk> \\<Longrightarrow>
	    G\<turnstile>(Lit a'..mn({pT}Lit pv),None,(h,l)) \<rightarrow>1 
      (Body blk res l,np a' x,(h,init_vals lvars[This\<mapsto>a'][Super\<mapsto>a'][pn\<mapsto>pv]))"
  Body1	"\<lbrakk>G\<turnstile>(s0,None,s) \<mapsto>1 (s0',s')\<rbrakk> \\<Longrightarrow>
		   G\<turnstile>(Body s0    e      l,None,s) \<rightarrow>1 (Body s0'  e  l,s')"
  Body2	"\<lbrakk>G\<turnstile>(e ,None,s) \<rightarrow>1 (e',s')\<rbrakk> \\<Longrightarrow>
		   G\<turnstile>(Body Skip  e      l,None,s) \<rightarrow>1 (Body Skip e' l,s')"
  Body		  "G\<turnstile>(Body Skip (Lit v) l,None,s) \<rightarrow>1 (Lit v,None,(heap s,l))"

(* execution of statements *)

  (* cf. 14.1 *)
  XcptS	"\<lbrakk>s0 \<noteq> Skip\<rbrakk> \\<Longrightarrow>
				 G\<turnstile>(s0,Some xc,s) \<mapsto>1 (Skip,Some xc,s)"

  (* cf. 14.5 *)
(*Skip	 			 "G\<turnstile>(Skip,None,s) \<mapsto>1 (Skip,None,s)"*)

  (* cf. 14.2 *)
  Comp1	"\<lbrakk>G\<turnstile>(s1,None,s) \<mapsto>1 (s1',s')\<rbrakk> \\<Longrightarrow>
			       G\<turnstile>(s1;; s2,None,s) \<mapsto>1 (s1';; s2,s')"
  Comp			    "G\<turnstile>(Skip;; s2,None,s) \<mapsto>1 (s2,None,s)"






  (* cf. 14.7 *)
  Expr1	"\<lbrakk>G\<turnstile>(e ,None,s) \<rightarrow>1 (e',s')\<rbrakk> \\<Longrightarrow>
				G\<turnstile>(Expr e,None,s) \<mapsto>1 (Expr e',s')"
  Expr			 "G\<turnstile>(Expr (Lit v),None,s) \<mapsto>1 (Skip,None,s)"

  (* cf. 14.8.2 *)
  If1	"\<lbrakk>G\<turnstile>(e ,None,s) \<rightarrow>1 (e',s')\<rbrakk> \\<Longrightarrow>
		      G\<turnstile>(If(e) s1 Else s2,None,s) \<mapsto>1 (If(e') s1 Else s2,s')"
  If		 "G\<turnstile>(If(Lit v) s1 Else s2,None,s) \<mapsto>1 
		    (if the_Bool v then s1 else s2,None,s)"

  (* cf. 14.10, 14.10.1 *)
  Loop			  "G\<turnstile>(While(e) s0,None,s) \<mapsto>1 
			     (If(e) (s0;; While(e) s0) Else Skip,None,s)"

end
