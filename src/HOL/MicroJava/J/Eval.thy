(*  Title:      HOL/MicroJava/J/Eval.thy
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   1999 Technische Universitaet Muenchen

Operational evaluation (big-step) semantics of the 
execution of Java expressions and statements
*)

Eval = State + WellType +

consts
  eval  :: "java_mb prog \\<Rightarrow> (xstate \\<times> expr      \\<times> val      \\<times> xstate) set"
  evals :: "java_mb prog \\<Rightarrow> (xstate \\<times> expr list \\<times> val list \\<times> xstate) set"
  exec  :: "java_mb prog \\<Rightarrow> (xstate \\<times> stmt                 \\<times> xstate) set"

syntax
  eval :: "[java_mb prog,xstate,expr,val,xstate] \\<Rightarrow> bool "("_\\<turnstile>_ -_\\<succ>_\\<rightarrow> _"[51,82,82,82,82]81)
  evals:: "[java_mb prog,xstate,expr list,
	                      val list,xstate] \\<Rightarrow> bool "("_\\<turnstile>_ -_[\\<succ>]_\\<rightarrow> _"[51,82,51,51,82]81)
  exec :: "[java_mb prog,xstate,stmt,    xstate] \\<Rightarrow> bool "("_\\<turnstile>_ -_\\<rightarrow> _"  [51,82,82,   82]81)

translations
  "G\\<turnstile>s -e \\<succ> v\\<rightarrow> (x,s')" <= "(s, e, v, x, s') \\<in> eval  G"
  "G\\<turnstile>s -e \\<succ> v\\<rightarrow>    s' " == "(s, e, v,    s' ) \\<in> eval  G"
  "G\\<turnstile>s -e[\\<succ>]v\\<rightarrow> (x,s')" <= "(s, e, v, x, s') \\<in> evals G"
  "G\\<turnstile>s -e[\\<succ>]v\\<rightarrow>    s' " == "(s, e, v,    s' ) \\<in> evals G"
  "G\\<turnstile>s -c    \\<rightarrow> (x,s')" <= "(s, c, x, s') \\<in> exec  G"
  "G\\<turnstile>s -c    \\<rightarrow>    s' " == "(s, c,    s') \\<in> exec  G"

inductive "eval G" "evals G" "exec G" intrs

(* evaluation of expressions *)

  (* cf. 15.5 *)
  XcptE				  "G\\<turnstile>(Some xc,s) -e\\<succ>arbitrary\\<rightarrow> (Some xc,s)"

  (* cf. 15.8.1 *)
  NewC	"\\<lbrakk>h = heap s; (a,x) = new_Addr h;
	  h'= h(a\\<mapsto>(C,init_vars (fields (G,C))))\\<rbrakk> \\<Longrightarrow>
				   G\\<turnstile>Norm s -NewC C\\<succ>Addr a\\<rightarrow> c_hupd h' (x,s)"

  (* cf. 15.15 *)
  Cast	"\\<lbrakk>G\\<turnstile>Norm s0 -e\\<succ>v\\<rightarrow> (x1,s1);
	  x2=raise_if (\\<not> cast_ok G C (heap s1) v) ClassCast x1\\<rbrakk> \\<Longrightarrow>
			        G\\<turnstile>Norm s0 -Cast C e\\<succ>v\\<rightarrow> (x2,s1)"

  (* cf. 15.7.1 *)
  Lit				   "G\\<turnstile>Norm s -Lit v\\<succ>v\\<rightarrow> Norm s"

  BinOp "\\<lbrakk>G\\<turnstile>Norm s -e1\\<succ>v1\\<rightarrow> s1;
	  G\\<turnstile>s1     -e2\\<succ>v2\\<rightarrow> s2;
	  v = (case bop of Eq  \\<Rightarrow> Bool (v1 = v2)
	                 | Add \\<Rightarrow> Intg (the_Intg v1 + the_Intg v2))\\<rbrakk> \\<Longrightarrow>
				   G\\<turnstile>Norm s -BinOp bop e1 e2\\<succ>v\\<rightarrow> s2"

  (* cf. 15.13.1, 15.2 *)
  LAcc				  "G\\<turnstile>Norm s -LAcc v\\<succ>the (locals s v)\\<rightarrow> Norm s"

  (* cf. 15.25.1 *)
  LAss  "\\<lbrakk>G\\<turnstile>Norm s -e\\<succ>v\\<rightarrow>  (x,(h,l));
	  l' = (if x = None then l(va\\<mapsto>v) else l)\\<rbrakk> \\<Longrightarrow>
				   G\\<turnstile>Norm s -va\\<Colon>=e\\<succ>v\\<rightarrow> (x,(h,l'))"


  (* cf. 15.10.1, 15.2 *)
  FAcc	"\\<lbrakk>G\\<turnstile>Norm s0 -e\\<succ>a'\\<rightarrow> (x1,s1); 
	  v = the (snd (the (heap s1 (the_Addr a'))) (fn,T))\\<rbrakk> \\<Longrightarrow>
				 G\\<turnstile>Norm s0 -{T}e..fn\\<succ>v\\<rightarrow> (np a' x1,s1)"

  (* cf. 15.25.1 *)
  FAss  "\\<lbrakk>G\\<turnstile>     Norm s0  -e1\\<succ>a'\\<rightarrow> (x1,s1); a = the_Addr a';
	  G\\<turnstile>(np a' x1,s1) -e2\\<succ>v \\<rightarrow> (x2,s2);
	  h = heap s2; (c,fs) = the (h a);
	  h' = h(a\\<mapsto>(c,(fs((fn,T)\\<mapsto>v))))\\<rbrakk> \\<Longrightarrow>
			  G\\<turnstile>Norm s0 -{T}e1..fn:=e2\\<succ>v\\<rightarrow> c_hupd h' (x2,s2)"

  (* cf. 15.11.4.1, 15.11.4.2, 15.11.4.4, 15.11.4.5, 14.15 *)
  Call	"\\<lbrakk>G\\<turnstile>Norm s0 -e\\<succ>a'\\<rightarrow> s1; a = the_Addr a';
	   G\\<turnstile>s1 -ps[\\<succ>]pvs\\<rightarrow> (x,(h,l)); dynT = fst (the (h a));
	   (md,rT,pns,lvars,blk,res) = the (method (G,dynT) (mn,pTs));
	   G\\<turnstile>(np a' x,(h,(init_vars lvars)(pns[\\<mapsto>]pvs)(This\\<mapsto>a'))) -blk\\<rightarrow> s3;
	   G\\<turnstile>     s3 -res\\<succ>v \\<rightarrow> (x4,s4)\\<rbrakk> \\<Longrightarrow>
			    G\\<turnstile>Norm s0 -e..mn({pTs}ps)\\<succ>v\\<rightarrow> (x4,(heap s4,l))"


(* evaluation of expression lists *)

  (* cf. 15.5 *)
  XcptEs			  "G\\<turnstile>(Some xc,s) -e[\\<succ>]arbitrary\\<rightarrow> (Some xc,s)"

  (* cf. 15.11.??? *)
  Nil
				    "G\\<turnstile>Norm s0 -[][\\<succ>][]\\<rightarrow> Norm s0"

  (* cf. 15.6.4 *)
  Cons	"\\<lbrakk>G\\<turnstile>Norm s0 -e  \\<succ> v \\<rightarrow> s1;
           G\\<turnstile>     s1 -es[\\<succ>]vs\\<rightarrow> s2\\<rbrakk> \\<Longrightarrow>
				   G\\<turnstile>Norm s0 -e#es[\\<succ>]v#vs\\<rightarrow> s2"

(* execution of statements *)

  (* cf. 14.1 *)
  XcptS				 "G\\<turnstile>(Some xc,s) -s0\\<rightarrow> (Some xc,s)"

  (* cf. 14.5 *)
  Skip	 			    "G\\<turnstile>Norm s -Skip\\<rightarrow> Norm s"

  (* cf. 14.7 *)
  Expr	"\\<lbrakk>G\\<turnstile>Norm s0 -e\\<succ>v\\<rightarrow> s1\\<rbrakk> \\<Longrightarrow>
				  G\\<turnstile>Norm s0 -Expr e\\<rightarrow> s1"

  (* cf. 14.2 *)
  Comp	"\\<lbrakk>G\\<turnstile>Norm s0 -s \\<rightarrow> s1;
	  G\\<turnstile>     s1 -t \\<rightarrow> s2\\<rbrakk> \\<Longrightarrow>
				 G\\<turnstile>Norm s0 -(s;; t)\\<rightarrow> s2"

  (* cf. 14.8.2 *)
  Cond	"\\<lbrakk>G\\<turnstile>Norm s0  -e \\<succ>v\\<rightarrow> s1;
	  G\\<turnstile>     s1 -(if  the_Bool v then s else t)\\<rightarrow> s2\\<rbrakk> \\<Longrightarrow>
		        G\\<turnstile>Norm s0 -(If(e) s Else t)\\<rightarrow> s2"

  (* cf. 14.10, 14.10.1 *)
  Loop	"\\<lbrakk>G\\<turnstile>Norm s0 -(If(e) (s;; While(e) s) Else Skip)\\<rightarrow> s1\\<rbrakk> \\<Longrightarrow>
			    G\\<turnstile>Norm s0 -(While(e) s)\\<rightarrow> s1"

end
