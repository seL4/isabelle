(*  Title:      HOL/Bali/Evaln.thy
    ID:         $Id$
    Author:     David von Oheimb and Norbert Schirmer
    License:    GPL (GNU GENERAL PUBLIC LICENSE)
*)
header {* Operational evaluation (big-step) semantics of Java expressions and 
          statements
*}

theory Evaln = Eval + TypeSafe:

text {*
Variant of eval relation with counter for bounded recursive depth.
Evaln omits the technical accessibility tests @{term check_field_access}
and @{term check_method_access}, since we proved the absence of errors for
wellformed programs.
*}

consts

  evaln	:: "prog \<Rightarrow> (state \<times> term \<times> nat \<times> vals \<times> state) set"

syntax

  evaln	:: "[prog, state, term,        nat, vals * state] => bool"
				("_|-_ -_>-_-> _"   [61,61,80,   61,61] 60)
  evarn	:: "[prog, state, var  , vvar        , nat, state] => bool"
				("_|-_ -_=>_-_-> _" [61,61,90,61,61,61] 60)
  eval_n:: "[prog, state, expr , val         , nat, state] => bool"
				("_|-_ -_->_-_-> _" [61,61,80,61,61,61] 60)
  evalsn:: "[prog, state, expr list, val list, nat, state] => bool"
				("_|-_ -_#>_-_-> _" [61,61,61,61,61,61] 60)
  execn	:: "[prog, state, stmt ,               nat, state] => bool"
				("_|-_ -_-_-> _"    [61,61,65,   61,61] 60)

syntax (xsymbols)

  evaln	:: "[prog, state, term,         nat, vals \<times> state] \<Rightarrow> bool"
				("_\<turnstile>_ \<midarrow>_\<succ>\<midarrow>_\<rightarrow> _"   [61,61,80,   61,61] 60)
  evarn	:: "[prog, state, var  , vvar         , nat, state] \<Rightarrow> bool"
				("_\<turnstile>_ \<midarrow>_=\<succ>_\<midarrow>_\<rightarrow> _" [61,61,90,61,61,61] 60)
  eval_n:: "[prog, state, expr , val ,          nat, state] \<Rightarrow> bool"
				("_\<turnstile>_ \<midarrow>_-\<succ>_\<midarrow>_\<rightarrow> _" [61,61,80,61,61,61] 60)
  evalsn:: "[prog, state, expr list, val  list, nat, state] \<Rightarrow> bool"
				("_\<turnstile>_ \<midarrow>_\<doteq>\<succ>_\<midarrow>_\<rightarrow> _" [61,61,61,61,61,61] 60)
  execn	:: "[prog, state, stmt ,                nat, state] \<Rightarrow> bool"
				("_\<turnstile>_ \<midarrow>_\<midarrow>_\<rightarrow> _"     [61,61,65,   61,61] 60)

translations

  "G\<turnstile>s \<midarrow>t    \<succ>\<midarrow>n\<rightarrow>  w___s' " == "(s,t,n,w___s') \<in> evaln G"
  "G\<turnstile>s \<midarrow>t    \<succ>\<midarrow>n\<rightarrow> (w,  s')" <= "(s,t,n,w,  s') \<in> evaln G"
  "G\<turnstile>s \<midarrow>t    \<succ>\<midarrow>n\<rightarrow> (w,x,s')" <= "(s,t,n,w,x,s') \<in> evaln G"
  "G\<turnstile>s \<midarrow>c     \<midarrow>n\<rightarrow> (x,s')" <= "G\<turnstile>s \<midarrow>In1r  c\<succ>\<midarrow>n\<rightarrow> (\<diamondsuit>    ,x,s')"
  "G\<turnstile>s \<midarrow>c     \<midarrow>n\<rightarrow>    s' " == "G\<turnstile>s \<midarrow>In1r  c\<succ>\<midarrow>n\<rightarrow> (\<diamondsuit>    ,  s')"
  "G\<turnstile>s \<midarrow>e-\<succ>v  \<midarrow>n\<rightarrow> (x,s')" <= "G\<turnstile>s \<midarrow>In1l e\<succ>\<midarrow>n\<rightarrow> (In1 v ,x,s')"
  "G\<turnstile>s \<midarrow>e-\<succ>v  \<midarrow>n\<rightarrow>    s' " == "G\<turnstile>s \<midarrow>In1l e\<succ>\<midarrow>n\<rightarrow> (In1 v ,  s')"
  "G\<turnstile>s \<midarrow>e=\<succ>vf \<midarrow>n\<rightarrow> (x,s')" <= "G\<turnstile>s \<midarrow>In2  e\<succ>\<midarrow>n\<rightarrow> (In2 vf,x,s')"
  "G\<turnstile>s \<midarrow>e=\<succ>vf \<midarrow>n\<rightarrow>    s' " == "G\<turnstile>s \<midarrow>In2  e\<succ>\<midarrow>n\<rightarrow> (In2 vf,  s')"
  "G\<turnstile>s \<midarrow>e\<doteq>\<succ>v  \<midarrow>n\<rightarrow> (x,s')" <= "G\<turnstile>s \<midarrow>In3  e\<succ>\<midarrow>n\<rightarrow> (In3 v ,x,s')"
  "G\<turnstile>s \<midarrow>e\<doteq>\<succ>v  \<midarrow>n\<rightarrow>    s' " == "G\<turnstile>s \<midarrow>In3  e\<succ>\<midarrow>n\<rightarrow> (In3 v ,  s')"


inductive "evaln G" intros

(* propagation of abrupt completion *)

  Abrupt:   "G\<turnstile>(Some xc,s) \<midarrow>t\<succ>\<midarrow>n\<rightarrow> (arbitrary3 t,(Some xc,s))"


(* evaluation of variables *)

  LVar:	"G\<turnstile>Norm s \<midarrow>LVar vn=\<succ>lvar vn s\<midarrow>n\<rightarrow> Norm s"

  FVar:	"\<lbrakk>G\<turnstile>Norm s0 \<midarrow>Init statDeclC\<midarrow>n\<rightarrow> s1; G\<turnstile>s1 \<midarrow>e-\<succ>a'\<midarrow>n\<rightarrow> s2;
	  (v,s2') = fvar statDeclC stat fn a' s2\<rbrakk> \<Longrightarrow>
	  G\<turnstile>Norm s0 \<midarrow>{accC,statDeclC,stat}e..fn=\<succ>v\<midarrow>n\<rightarrow> s2'"

  AVar:	"\<lbrakk>G\<turnstile> Norm s0 \<midarrow>e1-\<succ>a\<midarrow>n\<rightarrow> s1 ; G\<turnstile>s1 \<midarrow>e2-\<succ>i\<midarrow>n\<rightarrow> s2; 
	  (v,s2') = avar G i a s2\<rbrakk> \<Longrightarrow>
	              G\<turnstile>Norm s0 \<midarrow>e1.[e2]=\<succ>v\<midarrow>n\<rightarrow> s2'"




(* evaluation of expressions *)

  NewC:	"\<lbrakk>G\<turnstile>Norm s0 \<midarrow>Init C\<midarrow>n\<rightarrow> s1;
	  G\<turnstile>     s1 \<midarrow>halloc (CInst C)\<succ>a\<rightarrow> s2\<rbrakk> \<Longrightarrow>
	                          G\<turnstile>Norm s0 \<midarrow>NewC C-\<succ>Addr a\<midarrow>n\<rightarrow> s2"

  NewA:	"\<lbrakk>G\<turnstile>Norm s0 \<midarrow>init_comp_ty T\<midarrow>n\<rightarrow> s1; G\<turnstile>s1 \<midarrow>e-\<succ>i'\<midarrow>n\<rightarrow> s2; 
	  G\<turnstile>abupd (check_neg i') s2 \<midarrow>halloc (Arr T (the_Intg i'))\<succ>a\<rightarrow> s3\<rbrakk> \<Longrightarrow>
	                        G\<turnstile>Norm s0 \<midarrow>New T[e]-\<succ>Addr a\<midarrow>n\<rightarrow> s3"

  Cast:	"\<lbrakk>G\<turnstile>Norm s0 \<midarrow>e-\<succ>v\<midarrow>n\<rightarrow> s1;
	  s2 = abupd (raise_if (\<not>G,snd s1\<turnstile>v fits T) ClassCast) s1\<rbrakk> \<Longrightarrow>
			        G\<turnstile>Norm s0 \<midarrow>Cast T e-\<succ>v\<midarrow>n\<rightarrow> s2"

  Inst:	"\<lbrakk>G\<turnstile>Norm s0 \<midarrow>e-\<succ>v\<midarrow>n\<rightarrow> s1;
	  b = (v\<noteq>Null \<and> G,store s1\<turnstile>v fits RefT T)\<rbrakk> \<Longrightarrow>
			      G\<turnstile>Norm s0 \<midarrow>e InstOf T-\<succ>Bool b\<midarrow>n\<rightarrow> s1"

  Lit:			   "G\<turnstile>Norm s \<midarrow>Lit v-\<succ>v\<midarrow>n\<rightarrow> Norm s"

  Super:		   "G\<turnstile>Norm s \<midarrow>Super-\<succ>val_this s\<midarrow>n\<rightarrow> Norm s"

  Acc:	"\<lbrakk>G\<turnstile>Norm s0 \<midarrow>va=\<succ>(v,f)\<midarrow>n\<rightarrow> s1\<rbrakk> \<Longrightarrow>
	                          G\<turnstile>Norm s0 \<midarrow>Acc va-\<succ>v\<midarrow>n\<rightarrow> s1"

  Ass:	"\<lbrakk>G\<turnstile>Norm s0 \<midarrow>va=\<succ>(w,f)\<midarrow>n\<rightarrow> s1;
          G\<turnstile>     s1 \<midarrow>e-\<succ>v     \<midarrow>n\<rightarrow> s2\<rbrakk> \<Longrightarrow>
				   G\<turnstile>Norm s0 \<midarrow>va:=e-\<succ>v\<midarrow>n\<rightarrow> assign f v s2"

  Cond:	"\<lbrakk>G\<turnstile>Norm s0 \<midarrow>e0-\<succ>b\<midarrow>n\<rightarrow> s1;
          G\<turnstile>     s1 \<midarrow>(if the_Bool b then e1 else e2)-\<succ>v\<midarrow>n\<rightarrow> s2\<rbrakk> \<Longrightarrow>
			    G\<turnstile>Norm s0 \<midarrow>e0 ? e1 : e2-\<succ>v\<midarrow>n\<rightarrow> s2"

  Call:	
  "\<lbrakk>G\<turnstile>Norm s0 \<midarrow>e-\<succ>a'\<midarrow>n\<rightarrow> s1; G\<turnstile>s1 \<midarrow>args\<doteq>\<succ>vs\<midarrow>n\<rightarrow> s2;
    D = invocation_declclass G mode (store s2) a' statT \<lparr>name=mn,parTs=pTs\<rparr>; 
    G\<turnstile>init_lvars G D \<lparr>name=mn,parTs=pTs\<rparr> mode a' vs s2
            \<midarrow>Methd D \<lparr>name=mn,parTs=pTs\<rparr>-\<succ>v\<midarrow>n\<rightarrow> s3\<rbrakk>
   \<Longrightarrow> 
    G\<turnstile>Norm s0 \<midarrow>{accC,statT,mode}e\<cdot>mn({pTs}args)-\<succ>v\<midarrow>n\<rightarrow> (restore_lvars s2 s3)"

  Methd:"\<lbrakk>G\<turnstile>Norm s0 \<midarrow>body G D sig-\<succ>v\<midarrow>n\<rightarrow> s1\<rbrakk> \<Longrightarrow>
				G\<turnstile>Norm s0 \<midarrow>Methd D sig-\<succ>v\<midarrow>Suc n\<rightarrow> s1"

  Body:	"\<lbrakk>G\<turnstile>Norm s0\<midarrow>Init D\<midarrow>n\<rightarrow> s1; G\<turnstile>s1 \<midarrow>c\<midarrow>n\<rightarrow> s2\<rbrakk>\<Longrightarrow>
 G\<turnstile>Norm s0 \<midarrow>Body D c-\<succ>the (locals (store s2) Result)\<midarrow>n\<rightarrow>abupd (absorb Ret) s2"

(* evaluation of expression lists *)

  Nil:
				"G\<turnstile>Norm s0 \<midarrow>[]\<doteq>\<succ>[]\<midarrow>n\<rightarrow> Norm s0"

  Cons:	"\<lbrakk>G\<turnstile>Norm s0 \<midarrow>e -\<succ> v \<midarrow>n\<rightarrow> s1;
          G\<turnstile>     s1 \<midarrow>es\<doteq>\<succ>vs\<midarrow>n\<rightarrow> s2\<rbrakk> \<Longrightarrow>
			     G\<turnstile>Norm s0 \<midarrow>e#es\<doteq>\<succ>v#vs\<midarrow>n\<rightarrow> s2"


(* execution of statements *)

  Skip:	 			    "G\<turnstile>Norm s \<midarrow>Skip\<midarrow>n\<rightarrow> Norm s"

  Expr:	"\<lbrakk>G\<turnstile>Norm s0 \<midarrow>e-\<succ>v\<midarrow>n\<rightarrow> s1\<rbrakk> \<Longrightarrow>
				  G\<turnstile>Norm s0 \<midarrow>Expr e\<midarrow>n\<rightarrow> s1"

  Lab:  "\<lbrakk>G\<turnstile>Norm s0 \<midarrow>c \<midarrow>n\<rightarrow> s1\<rbrakk> \<Longrightarrow>
                             G\<turnstile>Norm s0 \<midarrow>l\<bullet> c\<midarrow>n\<rightarrow> abupd (absorb (Break l)) s1"

  Comp:	"\<lbrakk>G\<turnstile>Norm s0 \<midarrow>c1 \<midarrow>n\<rightarrow> s1;
	  G\<turnstile>     s1 \<midarrow>c2 \<midarrow>n\<rightarrow> s2\<rbrakk> \<Longrightarrow>
				 G\<turnstile>Norm s0 \<midarrow>c1;; c2\<midarrow>n\<rightarrow> s2"

  If:	"\<lbrakk>G\<turnstile>Norm s0 \<midarrow>e-\<succ>b\<midarrow>n\<rightarrow> s1;
	  G\<turnstile>     s1\<midarrow>(if the_Bool b then c1 else c2)\<midarrow>n\<rightarrow> s2\<rbrakk> \<Longrightarrow>
		       G\<turnstile>Norm s0 \<midarrow>If(e) c1 Else c2 \<midarrow>n\<rightarrow> s2"

  Loop:	"\<lbrakk>G\<turnstile>Norm s0 \<midarrow>e-\<succ>b\<midarrow>n\<rightarrow> s1;
	  if normal s1 \<and> the_Bool b 
             then (G\<turnstile>s1 \<midarrow>c\<midarrow>n\<rightarrow> s2 \<and> 
                   G\<turnstile>(abupd (absorb (Cont l)) s2) \<midarrow>l\<bullet> While(e) c\<midarrow>n\<rightarrow> s3)
	     else s3 = s1\<rbrakk> \<Longrightarrow>
			      G\<turnstile>Norm s0 \<midarrow>l\<bullet> While(e) c\<midarrow>n\<rightarrow> s3"
  
  Do: "G\<turnstile>Norm s \<midarrow>Do j\<midarrow>n\<rightarrow> (Some (Jump j), s)"
  
  Throw:"\<lbrakk>G\<turnstile>Norm s0 \<midarrow>e-\<succ>a'\<midarrow>n\<rightarrow> s1\<rbrakk> \<Longrightarrow>
				 G\<turnstile>Norm s0 \<midarrow>Throw e\<midarrow>n\<rightarrow> abupd (throw a') s1"

  Try:	"\<lbrakk>G\<turnstile>Norm s0 \<midarrow>c1\<midarrow>n\<rightarrow> s1; G\<turnstile>s1 \<midarrow>sxalloc\<rightarrow> s2;
	  if G,s2\<turnstile>catch tn then G\<turnstile>new_xcpt_var vn s2 \<midarrow>c2\<midarrow>n\<rightarrow> s3 else s3 = s2\<rbrakk>
          \<Longrightarrow>
		  G\<turnstile>Norm s0 \<midarrow>Try c1 Catch(tn vn) c2\<midarrow>n\<rightarrow> s3"

  Fin:	"\<lbrakk>G\<turnstile>Norm s0 \<midarrow>c1\<midarrow>n\<rightarrow> (x1,s1);
	  G\<turnstile>Norm s1 \<midarrow>c2\<midarrow>n\<rightarrow> s2\<rbrakk> \<Longrightarrow>
              G\<turnstile>Norm s0 \<midarrow>c1 Finally c2\<midarrow>n\<rightarrow> abupd (abrupt_if (x1\<noteq>None) x1) s2"
  
  Init:	"\<lbrakk>the (class G C) = c;
	  if inited C (globs s0) then s3 = Norm s0
	  else (G\<turnstile>Norm (init_class_obj G C s0)
	          \<midarrow>(if C = Object then Skip else Init (super c))\<midarrow>n\<rightarrow> s1 \<and>
	        G\<turnstile>set_lvars empty s1 \<midarrow>init c\<midarrow>n\<rightarrow> s2 \<and> 
                s3 = restore_lvars s1 s2)\<rbrakk>
          \<Longrightarrow>
		 G\<turnstile>Norm s0 \<midarrow>Init C\<midarrow>n\<rightarrow> s3"
monos
  if_def2


declare split_if     [split del] split_if_asm     [split del]
        option.split [split del] option.split_asm [split del]
inductive_cases evaln_cases: "G\<turnstile>s \<midarrow>t\<succ>\<midarrow>n\<rightarrow> vs'"

inductive_cases evaln_elim_cases:
	"G\<turnstile>(Some xc, s) \<midarrow>t                        \<succ>\<midarrow>n\<rightarrow> vs'"
	"G\<turnstile>Norm s \<midarrow>In1r Skip                      \<succ>\<midarrow>n\<rightarrow> xs'"
        "G\<turnstile>Norm s \<midarrow>In1r (Do j)                    \<succ>\<midarrow>n\<rightarrow> xs'"
        "G\<turnstile>Norm s \<midarrow>In1r (l\<bullet> c)                    \<succ>\<midarrow>n\<rightarrow> xs'"
	"G\<turnstile>Norm s \<midarrow>In3  ([])                      \<succ>\<midarrow>n\<rightarrow> vs'"
	"G\<turnstile>Norm s \<midarrow>In3  (e#es)                    \<succ>\<midarrow>n\<rightarrow> vs'"
	"G\<turnstile>Norm s \<midarrow>In1l (Lit w)                   \<succ>\<midarrow>n\<rightarrow> vs'"
	"G\<turnstile>Norm s \<midarrow>In2  (LVar vn)                 \<succ>\<midarrow>n\<rightarrow> vs'"
	"G\<turnstile>Norm s \<midarrow>In1l (Cast T e)                \<succ>\<midarrow>n\<rightarrow> vs'"
	"G\<turnstile>Norm s \<midarrow>In1l (e InstOf T)              \<succ>\<midarrow>n\<rightarrow> vs'"
	"G\<turnstile>Norm s \<midarrow>In1l (Super)                   \<succ>\<midarrow>n\<rightarrow> vs'"
	"G\<turnstile>Norm s \<midarrow>In1l (Acc va)                  \<succ>\<midarrow>n\<rightarrow> vs'"
	"G\<turnstile>Norm s \<midarrow>In1r (Expr e)                  \<succ>\<midarrow>n\<rightarrow> xs'"
	"G\<turnstile>Norm s \<midarrow>In1r (c1;; c2)                 \<succ>\<midarrow>n\<rightarrow> xs'"
	"G\<turnstile>Norm s \<midarrow>In1l (Methd C sig)             \<succ>\<midarrow>n\<rightarrow> xs'"
	"G\<turnstile>Norm s \<midarrow>In1l (Body D c)                \<succ>\<midarrow>n\<rightarrow> xs'"
	"G\<turnstile>Norm s \<midarrow>In1l (e0 ? e1 : e2)            \<succ>\<midarrow>n\<rightarrow> vs'"
	"G\<turnstile>Norm s \<midarrow>In1r (If(e) c1 Else c2)        \<succ>\<midarrow>n\<rightarrow> xs'"
	"G\<turnstile>Norm s \<midarrow>In1r (l\<bullet> While(e) c)           \<succ>\<midarrow>n\<rightarrow> xs'"
	"G\<turnstile>Norm s \<midarrow>In1r (c1 Finally c2)           \<succ>\<midarrow>n\<rightarrow> xs'"
	"G\<turnstile>Norm s \<midarrow>In1r (Throw e)                 \<succ>\<midarrow>n\<rightarrow> xs'"
	"G\<turnstile>Norm s \<midarrow>In1l (NewC C)                  \<succ>\<midarrow>n\<rightarrow> vs'"
	"G\<turnstile>Norm s \<midarrow>In1l (New T[e])                \<succ>\<midarrow>n\<rightarrow> vs'"
	"G\<turnstile>Norm s \<midarrow>In1l (Ass va e)                \<succ>\<midarrow>n\<rightarrow> vs'"
	"G\<turnstile>Norm s \<midarrow>In1r (Try c1 Catch(tn vn) c2)  \<succ>\<midarrow>n\<rightarrow> xs'"
	"G\<turnstile>Norm s \<midarrow>In2  ({accC,statDeclC,stat}e..fn) \<succ>\<midarrow>n\<rightarrow> vs'"
	"G\<turnstile>Norm s \<midarrow>In2  (e1.[e2])                 \<succ>\<midarrow>n\<rightarrow> vs'"
	"G\<turnstile>Norm s \<midarrow>In1l ({accC,statT,mode}e\<cdot>mn({pT}p)) \<succ>\<midarrow>n\<rightarrow> vs'"
	"G\<turnstile>Norm s \<midarrow>In1r (Init C)                  \<succ>\<midarrow>n\<rightarrow> xs'"
declare split_if     [split] split_if_asm     [split] 
        option.split [split] option.split_asm [split]

lemma evaln_Inj_elim: "G\<turnstile>s \<midarrow>t\<succ>\<midarrow>n\<rightarrow> (w,s') \<Longrightarrow> case t of In1 ec \<Rightarrow>  
  (case ec of Inl e \<Rightarrow> (\<exists>v. w = In1 v) | Inr c \<Rightarrow> w = \<diamondsuit>)  
  | In2 e \<Rightarrow> (\<exists>v. w = In2 v) | In3 e \<Rightarrow> (\<exists>v. w = In3 v)"
apply (erule evaln_cases , auto)
apply (induct_tac "t")
apply   (induct_tac "a")
apply auto
done

ML_setup {*
fun enf nam inj rhs =
let
  val name = "evaln_" ^ nam ^ "_eq"
  val lhs = "G\<turnstile>s \<midarrow>" ^ inj ^ " t\<succ>\<midarrow>n\<rightarrow> (w, s')"
  val () = qed_goal name (the_context()) (lhs ^ " = (" ^ rhs ^ ")") 
	(K [Auto_tac, ALLGOALS (ftac (thm "evaln_Inj_elim")) THEN Auto_tac])
  fun is_Inj (Const (inj,_) $ _) = true
    | is_Inj _                   = false
  fun pred (_ $ (Const ("Pair",_) $ _ $ (Const ("Pair", _) $ _ $ 
    (Const ("Pair", _) $ _ $ (Const ("Pair", _) $ x $ _ )))) $ _ ) = is_Inj x
in
  make_simproc name lhs pred (thm name)
end;

val evaln_expr_proc = enf "expr" "In1l" "\<exists>v.  w=In1 v  \<and> G\<turnstile>s \<midarrow>t-\<succ>v \<midarrow>n\<rightarrow> s'";
val evaln_var_proc  = enf "var"  "In2"  "\<exists>vf. w=In2 vf \<and> G\<turnstile>s \<midarrow>t=\<succ>vf\<midarrow>n\<rightarrow> s'";
val evaln_exprs_proc= enf "exprs""In3"  "\<exists>vs. w=In3 vs \<and> G\<turnstile>s \<midarrow>t\<doteq>\<succ>vs\<midarrow>n\<rightarrow> s'";
val evaln_stmt_proc = enf "stmt" "In1r" "     w=\<diamondsuit>      \<and> G\<turnstile>s \<midarrow>t     \<midarrow>n\<rightarrow> s'";
Addsimprocs [evaln_expr_proc,evaln_var_proc,evaln_exprs_proc,evaln_stmt_proc];

bind_thms ("evaln_AbruptIs", sum3_instantiate (thm "evaln.Abrupt"))
*}
declare evaln_AbruptIs [intro!]

lemma evaln_abrupt_lemma: "G\<turnstile>s \<midarrow>e\<succ>\<midarrow>n\<rightarrow> (v,s') \<Longrightarrow> 
 fst s = Some xc \<longrightarrow> s' = s \<and> v = arbitrary3 e"
apply (erule evaln_cases , auto)
done

lemma evaln_abrupt: 
 "\<And>s'. G\<turnstile>(Some xc,s) \<midarrow>e\<succ>\<midarrow>n\<rightarrow> (w,s') = (s' = (Some xc,s) \<and>  
  w=arbitrary3 e \<and> G\<turnstile>(Some xc,s) \<midarrow>e\<succ>\<midarrow>n\<rightarrow> (arbitrary3 e,(Some xc,s)))"
apply auto
apply (frule evaln_abrupt_lemma, auto)+
done

ML {*
local
  fun is_Some (Const ("Pair",_) $ (Const ("Datatype.option.Some",_) $ _)$ _) =true
    | is_Some _ = false
  fun pred (_ $ (Const ("Pair",_) $
     _ $ (Const ("Pair", _) $ _ $ (Const ("Pair", _) $ _ $
       (Const ("Pair", _) $ _ $ x)))) $ _ ) = is_Some x
in
  val evaln_abrupt_proc = 
 make_simproc "evaln_abrupt" "G\<turnstile>(Some xc,s) \<midarrow>e\<succ>\<midarrow>n\<rightarrow> (w,s')" pred (thm "evaln_abrupt")
end;
Addsimprocs [evaln_abrupt_proc]
*}

lemma evaln_LitI: "G\<turnstile>s \<midarrow>Lit v-\<succ>(if normal s then v else arbitrary)\<midarrow>n\<rightarrow> s"
apply (case_tac "s", case_tac "a = None")
by (auto intro!: evaln.Lit)

lemma CondI: 
 "\<And>s1. \<lbrakk>G\<turnstile>s \<midarrow>e-\<succ>b\<midarrow>n\<rightarrow> s1; G\<turnstile>s1 \<midarrow>(if the_Bool b then e1 else e2)-\<succ>v\<midarrow>n\<rightarrow> s2\<rbrakk> \<Longrightarrow> 
  G\<turnstile>s \<midarrow>e ? e1 : e2-\<succ>(if normal s1 then v else arbitrary)\<midarrow>n\<rightarrow> s2"
apply (case_tac "s", case_tac "a = None")
by (auto intro!: evaln.Cond)

lemma evaln_SkipI [intro!]: "G\<turnstile>s \<midarrow>Skip\<midarrow>n\<rightarrow> s"
apply (case_tac "s", case_tac "a = None")
by (auto intro!: evaln.Skip)

lemma evaln_ExprI: "G\<turnstile>s \<midarrow>e-\<succ>v\<midarrow>n\<rightarrow> s' \<Longrightarrow> G\<turnstile>s \<midarrow>Expr e\<midarrow>n\<rightarrow> s'"
apply (case_tac "s", case_tac "a = None")
by (auto intro!: evaln.Expr)

lemma evaln_CompI: "\<lbrakk>G\<turnstile>s \<midarrow>c1\<midarrow>n\<rightarrow> s1; G\<turnstile>s1 \<midarrow>c2\<midarrow>n\<rightarrow> s2\<rbrakk> \<Longrightarrow> G\<turnstile>s \<midarrow>c1;; c2\<midarrow>n\<rightarrow> s2"
apply (case_tac "s", case_tac "a = None")
by (auto intro!: evaln.Comp)

lemma evaln_IfI: 
 "\<lbrakk>G\<turnstile>s \<midarrow>e-\<succ>v\<midarrow>n\<rightarrow> s1; G\<turnstile>s1 \<midarrow>(if the_Bool v then c1 else c2)\<midarrow>n\<rightarrow> s2\<rbrakk> \<Longrightarrow> 
  G\<turnstile>s \<midarrow>If(e) c1 Else c2\<midarrow>n\<rightarrow> s2"
apply (case_tac "s", case_tac "a = None")
by (auto intro!: evaln.If)

lemma evaln_SkipD [dest!]: "G\<turnstile>s \<midarrow>Skip\<midarrow>n\<rightarrow> s' \<Longrightarrow> s' = s" 
by (erule evaln_cases, auto)

lemma evaln_Skip_eq [simp]: "G\<turnstile>s \<midarrow>Skip\<midarrow>n\<rightarrow> s' = (s = s')"
apply auto
done

lemma evaln_eval:  
 (assumes evaln: "G\<turnstile>s0 \<midarrow>t\<succ>\<midarrow>n\<rightarrow> (v,s1)" and
             wt: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>t\<Colon>T" and  
        conf_s0: "s0\<Colon>\<preceq>(G, L)" and
             wf: "wf_prog G" 
       
 )  "G\<turnstile>s0 \<midarrow>t\<succ>\<rightarrow> (v,s1)"
proof -
  from evaln 
  show "\<And> L accC T. \<lbrakk>s0\<Colon>\<preceq>(G, L);\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>t\<Colon>T\<rbrakk>
                    \<Longrightarrow> G\<turnstile>s0 \<midarrow>t\<succ>\<rightarrow> (v,s1)"
       (is "PROP ?EqEval s0 s1 t v")
  proof (induct)
    case Abrupt
    show ?case by (rule eval.Abrupt)
  next
    case LVar
    show ?case by (rule eval.LVar)
  next
    case (FVar a accC' e fn n s0 s1 s2 s2' stat statDeclC v L accC T)
    have eval_initn: "G\<turnstile>Norm s0 \<midarrow>Init statDeclC\<midarrow>n\<rightarrow> s1" .
    have eval_en: "G\<turnstile>s1 \<midarrow>e-\<succ>a\<midarrow>n\<rightarrow> s2" .
    have hyp_init: "PROP ?EqEval (Norm s0) s1 (In1r (Init statDeclC)) \<diamondsuit>" .
    have hyp_e: "PROP ?EqEval s1 s2 (In1l e) (In1 a)" .
    have fvar: "(v, s2') = fvar statDeclC stat fn a s2" .
    have conf_s0: "Norm s0\<Colon>\<preceq>(G, L)" .
    have wt: "\<lparr>prg=G, cls=accC, lcl=L\<rparr>\<turnstile>In2 ({accC',statDeclC,stat}e..fn)\<Colon>T" .
    then obtain statC f where
                wt_e: "\<lparr>prg=G, cls=accC, lcl=L\<rparr>\<turnstile>e\<Colon>-Class statC" and
            accfield: "accfield G accC statC fn = Some (statDeclC,f)" and
                stat: "stat=is_static f" and
               accC': "accC'=accC" and
	           T: "T=(Inl (type f))"
       by (rule wt_elim_cases) (auto simp add: member_is_static_simp)
    from wf wt_e 
    have iscls_statC: "is_class G statC"
      by (auto dest: ty_expr_is_type type_is_class)
    with wf accfield 
    have iscls_statDeclC: "is_class G statDeclC"
      by (auto dest!: accfield_fields dest: fields_declC)
    then 
    have wt_init: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>(Init statDeclC)\<Colon>\<surd>"
      by simp
    from conf_s0 wt_init
    have eval_init: "G\<turnstile>Norm s0 \<midarrow>Init statDeclC\<rightarrow> s1"
      by (rule hyp_init)
    with wt_init conf_s0 wf 
    have conf_s1: "s1\<Colon>\<preceq>(G, L)"
      by (blast dest: exec_ts)
    with hyp_e wt_e
    have eval_e: "G\<turnstile>s1 \<midarrow>e-\<succ>a\<rightarrow> s2"
      by blast
    with wf conf_s1 wt_e
    obtain conf_s2: "s2\<Colon>\<preceq>(G, L)" and
            conf_a: "normal s2 \<longrightarrow> G,store s2\<turnstile>a\<Colon>\<preceq>Class statC"
      by (auto dest!: eval_type_sound)
    obtain s3 where
      check: "s3 = check_field_access G accC statDeclC fn stat a s2'"
      by simp
    from accfield wt_e eval_init eval_e conf_s2 conf_a fvar stat check  wf
    have eq_s3_s2': "s3=s2'"  
      by (auto dest!: error_free_field_access)
    with eval_init eval_e fvar check accC'
    show "G\<turnstile>Norm s0 \<midarrow>{accC',statDeclC,stat}e..fn=\<succ>v\<rightarrow> s2'"
      by (auto intro: eval.FVar)
  next
    case AVar
    with wf show ?case
      apply -
      apply (erule wt_elim_cases)
      apply (blast intro!: eval.AVar dest: eval_type_sound)
      done
  next
    case NewC
    with wf show ?case
      apply - 
      apply (erule wt_elim_cases)
      apply (blast intro!: eval.NewC dest: eval_type_sound is_acc_classD)
      done
  next
    case (NewA T a e i n s0 s1 s2 s3 L accC Ta) 
    have hyp_init: "PROP ?EqEval (Norm s0) s1 (In1r (init_comp_ty T)) \<diamondsuit>" .
    have hyp_size: "PROP ?EqEval s1 s2 (In1l e) (In1 i)" .
    have "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>In1l (New T[e])\<Colon>Ta" .
    then obtain
       wt_init: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>init_comp_ty T\<Colon>\<surd>" and
       wt_size: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>e\<Colon>-PrimT Integer"
      by (rule wt_elim_cases) (auto intro: wt_init_comp_ty dest: is_acc_typeD)
    have conf_s0: "Norm s0\<Colon>\<preceq>(G, L)" .
    from this wt_init 
    have eval_init: "G\<turnstile>Norm s0 \<midarrow>init_comp_ty T\<rightarrow> s1"
      by (rule hyp_init)
    moreover
    from eval_init wt_init wf conf_s0
    have "s1\<Colon>\<preceq>(G, L)"
      by (auto dest: eval_type_sound)
    from this wt_size 
    have "G\<turnstile>s1 \<midarrow>e-\<succ>i\<rightarrow> s2"
      by (rule hyp_size)
    moreover note NewA
    ultimately show ?case
      by (blast intro!: eval.NewA)
  next
    case Cast
    with wf show ?case
      by - (erule wt_elim_cases, rule eval.Cast,auto dest: eval_type_sound)
  next
    case Inst
    with wf show ?case
      by - (erule wt_elim_cases, rule eval.Inst,auto dest: eval_type_sound)
  next
    case Lit
    show ?case by (rule eval.Lit)
  next
    case Super
    show ?case by (rule eval.Super)
  next
    case Acc
    then show ?case
      by - (erule wt_elim_cases, rule eval.Acc,auto dest: eval_type_sound)
  next
    case Ass
    with wf show ?case
      by - (erule wt_elim_cases, blast intro!: eval.Ass dest: eval_type_sound) 
  next
    case (Cond b e0 e1 e2 n s0 s1 s2 v L accC T)
    have hyp_e0: "PROP ?EqEval (Norm s0) s1 (In1l e0) (In1 b)" .
    have hyp_if: "PROP ?EqEval s1 s2 
                              (In1l (if the_Bool b then e1 else e2)) (In1 v)" .
    have conf_s0: "Norm s0\<Colon>\<preceq>(G, L)" .
    have wt: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>In1l (e0 ? e1 : e2)\<Colon>T" .
    then obtain T1 T2 statT where
       wt_e0: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>e0\<Colon>-PrimT Boolean" and
       wt_e1: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>e1\<Colon>-T1" and
       wt_e2: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>e2\<Colon>-T2" and 
       statT: "G\<turnstile>T1\<preceq>T2 \<and> statT = T2  \<or>  G\<turnstile>T2\<preceq>T1 \<and> statT =  T1" and
       T    : "T=Inl statT"
      by (rule wt_elim_cases) auto
    from conf_s0 wt_e0
    have eval_e0: "G\<turnstile>Norm s0 \<midarrow>e0-\<succ>b\<rightarrow> s1"
      by (rule hyp_e0)
    moreover
    from eval_e0 conf_s0 wf wt_e0
    have "s1\<Colon>\<preceq>(G, L)"
      by (blast dest: eval_type_sound)
    with wt_e1 wt_e2 statT hyp_if
    have "G\<turnstile>s1 \<midarrow>(if the_Bool b then e1 else e2)-\<succ>v\<rightarrow> s2"
      by (cases "the_Bool b") auto
    ultimately
    show ?case
      by (rule eval.Cond)
  next
    case (Call invDeclC a' accC' args e mn mode n pTs' s0 s1 s2 s4 statT 
           v vs L accC T)
    (* Repeats large parts of the type soundness proof. One should factor
       out some lemmata about the relations and conformance of s2, s3 and s3'*)
    have evaln_e: "G\<turnstile>Norm s0 \<midarrow>e-\<succ>a'\<midarrow>n\<rightarrow> s1" .
    have evaln_args: "G\<turnstile>s1 \<midarrow>args\<doteq>\<succ>vs\<midarrow>n\<rightarrow> s2" .
    have invDeclC: "invDeclC 
                      = invocation_declclass G mode (store s2) a' statT 
                           \<lparr>name = mn, parTs = pTs'\<rparr>" .
    let ?InitLvars 
         = "init_lvars G invDeclC \<lparr>name = mn, parTs = pTs'\<rparr> mode a' vs s2"
    obtain s3 s3' where 
      init_lvars: "s3 = 
             init_lvars G invDeclC \<lparr>name = mn, parTs = pTs'\<rparr> mode a' vs s2" and
      check: "s3' =
         check_method_access G accC' statT mode \<lparr>name = mn, parTs = pTs'\<rparr> a' s3"
      by simp
    have evaln_methd: 
           "G\<turnstile>?InitLvars \<midarrow>Methd invDeclC \<lparr>name = mn, parTs = pTs'\<rparr>-\<succ>v\<midarrow>n\<rightarrow> s4" .
    have     hyp_e: "PROP ?EqEval (Norm s0) s1 (In1l e) (In1 a')" .
    have  hyp_args: "PROP ?EqEval s1 s2 (In3 args) (In3 vs)" .
    have hyp_methd: "PROP ?EqEval ?InitLvars s4 
                     (In1l (Methd invDeclC \<lparr>name = mn, parTs = pTs'\<rparr>)) (In1 v)".
    have conf_s0: "Norm s0\<Colon>\<preceq>(G, L)" .
    have      wt: "\<lparr>prg=G, cls=accC, lcl=L\<rparr>
                    \<turnstile>In1l ({accC',statT,mode}e\<cdot>mn( {pTs'}args))\<Colon>T" .
    from wt obtain pTs statDeclT statM where
                 wt_e: "\<lparr>prg=G, cls=accC, lcl=L\<rparr>\<turnstile>e\<Colon>-RefT statT" and
              wt_args: "\<lparr>prg=G, cls=accC, lcl=L\<rparr>\<turnstile>args\<Colon>\<doteq>pTs" and
                statM: "max_spec G accC statT \<lparr>name=mn,parTs=pTs\<rparr> 
                         = {((statDeclT,statM),pTs')}" and
                 mode: "mode = invmode statM e" and
                    T: "T =Inl (resTy statM)" and
        eq_accC_accC': "accC=accC'"
      by (rule wt_elim_cases) auto
    from conf_s0 wt_e hyp_e
    have eval_e: "G\<turnstile>Norm s0 \<midarrow>e-\<succ>a'\<rightarrow> s1"
      by blast
    with wf conf_s0 wt_e
    obtain conf_s1: "s1\<Colon>\<preceq>(G, L)" and
           conf_a': "normal s1 \<Longrightarrow> G, store s1\<turnstile>a'\<Colon>\<preceq>RefT statT" 
      by (auto dest!: eval_type_sound)
    from conf_s1 wt_args hyp_args
    have eval_args: "G\<turnstile>s1 \<midarrow>args\<doteq>\<succ>vs\<rightarrow> s2"
      by blast
    with wt_args conf_s1 wf 
    obtain    conf_s2: "s2\<Colon>\<preceq>(G, L)" and
            conf_args: "normal s2 
                         \<Longrightarrow>  list_all2 (conf G (store s2)) vs pTs" 
      by (auto dest!: eval_type_sound)
    from statM 
    obtain
       statM': "(statDeclT,statM)\<in>mheads G accC statT \<lparr>name=mn,parTs=pTs'\<rparr>" and
       pTs_widen: "G\<turnstile>pTs[\<preceq>]pTs'"
      by (blast dest: max_spec2mheads)
    from check
    have eq_store_s3'_s3: "store s3'=store s3"
      by (cases s3) (simp add: check_method_access_def Let_def)
    obtain invC
      where invC: "invC = invocation_class mode (store s2) a' statT"
      by simp
    with init_lvars
    have invC': "invC = (invocation_class mode (store s3) a' statT)"
      by (cases s2,cases mode) (auto simp add: init_lvars_def2 )
    show "G\<turnstile>Norm s0 \<midarrow>{accC',statT,mode}e\<cdot>mn( {pTs'}args)
             -\<succ>v\<rightarrow> (set_lvars (locals (store s2))) s4"
    proof (cases "normal s2")
      case False
      with init_lvars 
      obtain keep_abrupt: "abrupt s3 = abrupt s2" and
             "store s3 = store (init_lvars G invDeclC \<lparr>name = mn, parTs = pTs'\<rparr> 
                                            mode a' vs s2)" 
	by (auto simp add: init_lvars_def2)
      moreover
      from keep_abrupt False check
      have eq_s3'_s3: "s3'=s3" 
	by (auto simp add: check_method_access_def Let_def)
      moreover
      from eq_s3'_s3 False keep_abrupt evaln_methd init_lvars
      obtain "s4=s3'"
	 "In1 v=arbitrary3 (In1l (Methd invDeclC \<lparr>name = mn, parTs = pTs'\<rparr>))"
	by auto
      moreover note False
      ultimately have
	"G\<turnstile>s3' \<midarrow>Methd invDeclC \<lparr>name = mn, parTs = pTs'\<rparr>-\<succ>v\<rightarrow> s4"
	by (auto)
      from eval_e eval_args invDeclC init_lvars check this
      show ?thesis
	by (rule eval.Call)
    next
      case True
      note normal_s2 = True
      with eval_args
      have normal_s1: "normal s1"
	by (cases "normal s1") auto
      with conf_a' eval_args 
      have conf_a'_s2: "G, store s2\<turnstile>a'\<Colon>\<preceq>RefT statT"
	by (auto dest: eval_gext intro: conf_gext)
      show ?thesis
      proof (cases "a'=Null \<longrightarrow> is_static statM")
	case False
	then obtain not_static: "\<not> is_static statM" and Null: "a'=Null" 
	  by blast
	with normal_s2 init_lvars mode
	obtain np: "abrupt s3 = Some (Xcpt (Std NullPointer))" and
                   "store s3 = store (init_lvars G invDeclC 
                                       \<lparr>name = mn, parTs = pTs'\<rparr> mode a' vs s2)"
	  by (auto simp add: init_lvars_def2)
	moreover
	from np check
	have eq_s3'_s3: "s3'=s3" 
	  by (auto simp add: check_method_access_def Let_def)
	moreover
	from eq_s3'_s3 np evaln_methd init_lvars
	obtain "s4=s3'"
	  "In1 v=arbitrary3 (In1l (Methd invDeclC \<lparr>name = mn, parTs = pTs'\<rparr>))"
	  by auto
	moreover note np 
	ultimately have
	  "G\<turnstile>s3' \<midarrow>Methd invDeclC \<lparr>name = mn, parTs = pTs'\<rparr>-\<succ>v\<rightarrow> s4"
	  by (auto)
	from eval_e eval_args invDeclC init_lvars check this
	show ?thesis
	  by (rule eval.Call)
      next
	case True
	with mode have notNull: "mode = IntVir \<longrightarrow> a' \<noteq> Null"
	  by (auto dest!: Null_staticD)
	with conf_s2 conf_a'_s2 wf invC 
	have dynT_prop: "G\<turnstile>mode\<rightarrow>invC\<preceq>statT"
	  by (cases s2) (auto intro: DynT_propI)
	with wt_e statM' invC mode wf 
	obtain dynM where 
           dynM: "dynlookup G statT invC  \<lparr>name=mn,parTs=pTs'\<rparr> = Some dynM" and
           acc_dynM: "G \<turnstile>Methd  \<lparr>name=mn,parTs=pTs'\<rparr> dynM 
                          in invC dyn_accessible_from accC"
	  by (force dest!: call_access_ok)
	with invC' check eq_accC_accC'
	have eq_s3'_s3: "s3'=s3"
	  by (auto simp add: check_method_access_def Let_def)
	from dynT_prop wf wt_e statM' mode invC invDeclC dynM 
	obtain 
	   wf_dynM: "wf_mdecl G invDeclC (\<lparr>name=mn,parTs=pTs'\<rparr>,mthd dynM)" and
	     dynM': "methd G invDeclC \<lparr>name=mn,parTs=pTs'\<rparr> = Some dynM" and
           iscls_invDeclC: "is_class G invDeclC" and
	        invDeclC': "invDeclC = declclass dynM" and
	     invC_widen: "G\<turnstile>invC\<preceq>\<^sub>C invDeclC" and
	   is_static_eq: "is_static dynM = is_static statM" and
	   involved_classes_prop:
             "(if invmode statM e = IntVir
               then \<forall>statC. statT = ClassT statC \<longrightarrow> G\<turnstile>invC\<preceq>\<^sub>C statC
               else ((\<exists>statC. statT = ClassT statC \<and> G\<turnstile>statC\<preceq>\<^sub>C invDeclC) \<or>
                     (\<forall>statC. statT \<noteq> ClassT statC \<and> invDeclC = Object)) \<and>
                      statDeclT = ClassT invDeclC)"
	  by (auto dest: DynT_mheadsD)
	obtain L' where 
	   L':"L'=(\<lambda> k. 
                 (case k of
                    EName e
                    \<Rightarrow> (case e of 
                          VNam v 
                          \<Rightarrow>(table_of (lcls (mbody (mthd dynM)))
                             (pars (mthd dynM)[\<mapsto>]pTs')) v
                        | Res \<Rightarrow> Some (resTy dynM))
                  | This \<Rightarrow> if is_static statM 
                            then None else Some (Class invDeclC)))"
	  by simp
	from wf_dynM [THEN wf_mdeclD1, THEN conjunct1] normal_s2 conf_s2 wt_e
              wf eval_args conf_a' mode notNull wf_dynM involved_classes_prop
	have conf_s3: "s3\<Colon>\<preceq>(G,L')"
	   apply - 
          (*FIXME confomrs_init_lvars should be 
                adjusted to be more directy applicable *)
	   apply (drule conforms_init_lvars [of G invDeclC 
                  "\<lparr>name=mn,parTs=pTs'\<rparr>" dynM "store s2" vs pTs "abrupt s2" 
                  L statT invC a' "(statDeclT,statM)" e])
	     apply (rule wf)
	     apply (rule conf_args,assumption)
	     apply (simp add: pTs_widen)
	     apply (cases s2,simp)
	     apply (rule dynM')
	     apply (force dest: ty_expr_is_type)
	     apply (rule invC_widen)
	     apply (force intro: conf_gext dest: eval_gext)
	     apply simp
	     apply simp
	     apply (simp add: invC)
	     apply (simp add: invDeclC)
	     apply (force dest: wf_mdeclD1 is_acc_typeD)
	     apply (cases s2, simp add: L' init_lvars
	                      cong add: lname.case_cong ename.case_cong)
	   done
	from is_static_eq wf_dynM L'
	obtain mthdT where
	   "\<lparr>prg=G,cls=invDeclC,lcl=L'\<rparr>
            \<turnstile>Body invDeclC (stmt (mbody (mthd dynM)))\<Colon>-mthdT" and
	   mthdT_widen: "G\<turnstile>mthdT\<preceq>resTy dynM"
	  by - (drule wf_mdecl_bodyD,
                simp cong add: lname.case_cong ename.case_cong)
	with dynM' iscls_invDeclC invDeclC'
	have
	   "\<lparr>prg=G,cls=invDeclC,lcl=L'\<rparr>
            \<turnstile>(Methd invDeclC \<lparr>name = mn, parTs = pTs'\<rparr>)\<Colon>-mthdT"
	  by (auto intro: wt.Methd)
	with conf_s3 hyp_methd init_lvars eq_s3'_s3
	have "G\<turnstile>s3' \<midarrow>Methd invDeclC \<lparr>name = mn, parTs = pTs'\<rparr>-\<succ>v\<rightarrow> s4"
	  by auto
	from eval_e eval_args invDeclC init_lvars check this
	show ?thesis
	  by (rule eval.Call)
      qed
    qed
  next
    case Methd
    with wf show ?case
      by - (erule wt_elim_cases, rule eval.Methd, 
            auto dest: eval_type_sound simp add: body_def2)
  next
    case Body
    with wf show ?case
       by - (erule wt_elim_cases, blast intro!: eval.Body dest: eval_type_sound)
  next
    case Nil
    show ?case by (rule eval.Nil)
  next
    case Cons
    with wf show ?case
      by - (erule wt_elim_cases, blast intro!: eval.Cons dest: eval_type_sound)
  next
    case Skip
    show ?case by (rule eval.Skip)
  next
    case Expr
    with wf show ?case
      by - (erule wt_elim_cases, rule eval.Expr,auto dest: eval_type_sound)
  next
    case Lab
    with wf show ?case
      by - (erule wt_elim_cases, rule eval.Lab,auto dest: eval_type_sound)
  next
    case Comp
    with wf show ?case
      by - (erule wt_elim_cases, blast intro!: eval.Comp dest: eval_type_sound)
  next
    case (If b c1 c2 e n s0 s1 s2 L accC T)
    have hyp_e: "PROP ?EqEval (Norm s0) s1 (In1l e) (In1 b)" .
    have hyp_then_else: 
      "PROP ?EqEval s1 s2 (In1r (if the_Bool b then c1 else c2)) \<diamondsuit>" .
    have conf_s0: "Norm s0\<Colon>\<preceq>(G, L)" .
    have      wt: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>In1r (If(e) c1 Else c2)\<Colon>T" .
    then obtain 
              wt_e: "\<lparr>prg=G, cls=accC, lcl=L\<rparr>\<turnstile>e\<Colon>-PrimT Boolean" and
      wt_then_else: "\<lparr>prg=G, cls=accC, lcl=L\<rparr>\<turnstile>(if the_Bool b then c1 else c2)\<Colon>\<surd>"
      by (rule wt_elim_cases) (auto split add: split_if)
    from conf_s0 wt_e
    have eval_e: "G\<turnstile>Norm s0 \<midarrow>e-\<succ>b\<rightarrow> s1"
      by (rule hyp_e)
    moreover
    from eval_e wt_e conf_s0 wf
    have "s1\<Colon>\<preceq>(G, L)"
      by (blast dest: eval_type_sound)
    from this wt_then_else
    have "G\<turnstile>s1 \<midarrow>(if the_Bool b then c1 else c2)\<rightarrow> s2"
      by (rule hyp_then_else)
    ultimately
    show ?case
      by (rule eval.If)
  next
    case (Loop b c e l n s0 s1 s2 s3 L accC T)
    have hyp_e: "PROP ?EqEval (Norm s0) s1 (In1l e) (In1 b)" .
    have conf_s0: "Norm s0\<Colon>\<preceq>(G, L)" .
    have      wt: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>In1r (l\<bullet> While(e) c)\<Colon>T" .
    then obtain wt_e: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>e\<Colon>-PrimT Boolean" and
                wt_c: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>c\<Colon>\<surd>"
      by (rule wt_elim_cases) (blast)
    from conf_s0 wt_e 
    have eval_e: "G\<turnstile>Norm s0 \<midarrow>e-\<succ>b\<rightarrow> s1"
      by (rule hyp_e)
    moreover
    from eval_e wt_e conf_s0 wf
    have conf_s1: "s1\<Colon>\<preceq>(G, L)"
      by (blast dest: eval_type_sound)
    have "if normal s1 \<and> the_Bool b 
             then (G\<turnstile>s1 \<midarrow>c\<rightarrow> s2 \<and> 
                   G\<turnstile>(abupd (absorb (Cont l)) s2) \<midarrow>l\<bullet> While(e) c\<rightarrow> s3)
	     else s3 = s1"
    proof (cases "normal s1 \<and> the_Bool b")
      case True 
      from Loop True have hyp_c: "PROP ?EqEval s1 s2 (In1r c) \<diamondsuit>"
	by (auto)
      from Loop True have hyp_w: "PROP ?EqEval (abupd (absorb (Cont l)) s2)
                                        s3 (In1r (l\<bullet> While(e) c)) \<diamondsuit>"
	by (auto)
      from conf_s1 wt_c
      have eval_c: "G\<turnstile>s1 \<midarrow>c\<rightarrow> s2"
	by (rule hyp_c)
      moreover
      from eval_c conf_s1 wt_c wf
      have "s2\<Colon>\<preceq>(G, L)"
	by (blast dest: eval_type_sound)
      then
      have "abupd (absorb (Cont l)) s2 \<Colon>\<preceq>(G, L)"
	by (cases s2) (auto intro: conforms_absorb)
      from this and wt
      have "G\<turnstile>abupd (absorb (Cont l)) s2 \<midarrow>l\<bullet> While(e) c\<rightarrow> s3"
	by (rule hyp_w)
      moreover note True
      ultimately
      show ?thesis
	by simp
    next
      case False
      with Loop have "s3 = s1" by simp
      with False
      show ?thesis 
	by auto
    qed
    ultimately
    show ?case
      by (rule eval.Loop)
  next
    case Do
    show ?case by (rule eval.Do)
  next
    case Throw
    with wf show ?case
      by - (erule wt_elim_cases, rule eval.Throw,auto dest: eval_type_sound)
  next
    case (Try c1 c2 n s0 s1 s2 s3 catchC vn L accC T)
    have  hyp_c1: "PROP ?EqEval (Norm s0) s1 (In1r c1) \<diamondsuit>" .
    have conf_s0:"Norm s0\<Colon>\<preceq>(G, L)" .
    have      wt:"\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>In1r (Try c1 Catch(catchC vn) c2)\<Colon>T" .
    then obtain 
      wt_c1: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>c1\<Colon>\<surd>" and
      wt_c2: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<lparr>lcl := L(VName vn\<mapsto>Class catchC)\<rparr>\<turnstile>c2\<Colon>\<surd>"
      by (rule wt_elim_cases) (auto)
    from conf_s0 wt_c1
    have eval_c1: "G\<turnstile>Norm s0 \<midarrow>c1\<rightarrow> s1"
      by (rule hyp_c1)
    moreover
    have sxalloc: "G\<turnstile>s1 \<midarrow>sxalloc\<rightarrow> s2" .
    moreover
    from eval_c1 wt_c1 conf_s0 wf
    have "s1\<Colon>\<preceq>(G, L)"
      by (blast dest: eval_type_sound)
    with sxalloc wf
    have conf_s2: "s2\<Colon>\<preceq>(G, L)" 
      by (auto dest: sxalloc_type_sound split: option.splits)
    have "if G,s2\<turnstile>catch catchC then G\<turnstile>new_xcpt_var vn s2 \<midarrow>c2\<rightarrow> s3 else s3 = s2"
    proof (cases "G,s2\<turnstile>catch catchC")
      case True
      note Catch = this
      with Try have hyp_c2: "PROP ?EqEval (new_xcpt_var vn s2) s3 (In1r c2) \<diamondsuit>"
	by auto
      show ?thesis
      proof (cases "normal s1")
	case True
	with sxalloc wf 
	have eq_s2_s1: "s2=s1"
	  by (auto dest: sxalloc_type_sound split: option.splits)
	with True 
	have "\<not>  G,s2\<turnstile>catch catchC"
	  by (simp add: catch_def)
	with Catch show ?thesis 
	  by (contradiction)
      next 
	case False
	with sxalloc wf
	obtain a 
	  where xcpt_s2: "abrupt s2 = Some (Xcpt (Loc a))"
	  by (auto dest!: sxalloc_type_sound split: option.splits)
	with Catch
	have "G\<turnstile>obj_ty (the (globs (store s2) (Heap a)))\<preceq>Class catchC"
	  by (cases s2) simp
	with xcpt_s2 conf_s2 wf 
	have "new_xcpt_var vn s2\<Colon>\<preceq>(G, L(VName vn\<mapsto>Class catchC))"
	  by (auto dest: Try_lemma)
	from this wt_c2
	have "G\<turnstile>new_xcpt_var vn s2 \<midarrow>c2\<rightarrow> s3"
	  by (auto intro: hyp_c2)
	with Catch 
	show ?thesis
	  by simp
      qed
    next
      case False
      with Try
      have "s3=s2"
	by simp
      with False
      show ?thesis
	by simp
    qed
    ultimately
    show ?case
      by (rule eval.Try)
  next
    case Fin
    with wf show ?case
      by -(erule wt_elim_cases, blast intro!: eval.Fin
           dest: eval_type_sound intro: conforms_NormI)
  next
    case (Init C c n s0 s1 s2 s3 L accC T)
    have     cls: "the (class G C) = c" .
    have conf_s0: "Norm s0\<Colon>\<preceq>(G, L)" .
    have      wt: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>In1r (Init C)\<Colon>T" .
    with cls
    have cls_C: "class G C = Some c"
      by - (erule wt_elim_cases,auto)
    have "if inited C (globs s0) then s3 = Norm s0
	  else (G\<turnstile>Norm (init_class_obj G C s0) 
		  \<midarrow>(if C = Object then Skip else Init (super c))\<rightarrow> s1 \<and>
	       G\<turnstile>set_lvars empty s1 \<midarrow>init c\<rightarrow> s2 \<and> s3 = restore_lvars s1 s2)"
    proof (cases "inited C (globs s0)")
      case True
      with Init have "s3 = Norm s0"
	by simp
      with True show ?thesis 
	by simp
    next
      case False
      with Init
      obtain 
	hyp_init_super: 
        "PROP ?EqEval (Norm ((init_class_obj G C) s0)) s1
	               (In1r (if C = Object then Skip else Init (super c))) \<diamondsuit>"
	and 
        hyp_init_c:
	   "PROP ?EqEval ((set_lvars empty) s1) s2 (In1r (init c)) \<diamondsuit>" and
	s3: "s3 = (set_lvars (locals (store s1))) s2"
	by (simp only: if_False)
      from conf_s0 wf cls_C False
      have conf_s0': "(Norm ((init_class_obj G C) s0))\<Colon>\<preceq>(G, L)"
	by (auto dest: conforms_init_class_obj)
      moreover
      from wf cls_C 
      have wt_init_super:
           "\<lparr>prg = G, cls = accC, lcl = L\<rparr>
                  \<turnstile>(if C = Object then Skip else Init (super c))\<Colon>\<surd>"
	by (cases "C=Object")
           (auto dest: wf_prog_cdecl wf_cdecl_supD is_acc_classD)
      ultimately
      have eval_init_super: 
	   "G\<turnstile>Norm ((init_class_obj G C) s0) 
            \<midarrow>(if C = Object then Skip else Init (super c))\<rightarrow> s1"
	by (rule hyp_init_super)
      with conf_s0' wt_init_super wf
      have "s1\<Colon>\<preceq>(G, L)"
	by (blast dest: eval_type_sound)
      then
      have "(set_lvars empty) s1\<Colon>\<preceq>(G, empty)"
	by (cases s1) (auto dest: conforms_set_locals )
      with wf cls_C 
      have eval_init_c: "G\<turnstile>(set_lvars empty) s1 \<midarrow>init c\<rightarrow> s2"
	by (auto intro!: hyp_init_c dest: wf_prog_cdecl wf_cdecl_wt_init)
      from False eval_init_super eval_init_c s3
      show ?thesis
	by simp
    qed
    from cls this
    show ?case
      by (rule eval.Init)
  qed 
qed

lemma Suc_le_D_lemma: "\<lbrakk>Suc n <= m'; (\<And>m. n <= m \<Longrightarrow> P (Suc m)) \<rbrakk> \<Longrightarrow> P m'"
apply (frule Suc_le_D)
apply fast
done

lemma evaln_nonstrict [rule_format (no_asm), elim]: 
  "\<And>ws. G\<turnstile>s \<midarrow>t\<succ>\<midarrow>n\<rightarrow> ws \<Longrightarrow> \<forall>m. n\<le>m \<longrightarrow> G\<turnstile>s \<midarrow>t\<succ>\<midarrow>m\<rightarrow> ws"
apply (simp (no_asm_simp) only: split_tupled_all)
apply (erule evaln.induct)
apply (tactic {* ALLGOALS (EVERY'[strip_tac, TRY o etac (thm "Suc_le_D_lemma"),
  REPEAT o smp_tac 1, 
  resolve_tac (thms "evaln.intros") THEN_ALL_NEW TRY o atac]) *})
(* 3 subgoals *)
apply (auto split del: split_if)
done

lemmas evaln_nonstrict_Suc = evaln_nonstrict [OF _ le_refl [THEN le_SucI]]

lemma evaln_max2: "\<lbrakk>G\<turnstile>s1 \<midarrow>t1\<succ>\<midarrow>n1\<rightarrow> ws1; G\<turnstile>s2 \<midarrow>t2\<succ>\<midarrow>n2\<rightarrow> ws2\<rbrakk> \<Longrightarrow> 
             G\<turnstile>s1 \<midarrow>t1\<succ>\<midarrow>max n1 n2\<rightarrow> ws1 \<and> G\<turnstile>s2 \<midarrow>t2\<succ>\<midarrow>max n1 n2\<rightarrow> ws2"
apply (fast intro: le_maxI1 le_maxI2)
done

lemma evaln_max3: 
"\<lbrakk>G\<turnstile>s1 \<midarrow>t1\<succ>\<midarrow>n1\<rightarrow> ws1; G\<turnstile>s2 \<midarrow>t2\<succ>\<midarrow>n2\<rightarrow> ws2; G\<turnstile>s3 \<midarrow>t3\<succ>\<midarrow>n3\<rightarrow> ws3\<rbrakk> \<Longrightarrow>
 G\<turnstile>s1 \<midarrow>t1\<succ>\<midarrow>max (max n1 n2) n3\<rightarrow> ws1 \<and>
 G\<turnstile>s2 \<midarrow>t2\<succ>\<midarrow>max (max n1 n2) n3\<rightarrow> ws2 \<and> 
 G\<turnstile>s3 \<midarrow>t3\<succ>\<midarrow>max (max n1 n2) n3\<rightarrow> ws3"
apply (drule (1) evaln_max2, erule thin_rl)
apply (fast intro!: le_maxI1 le_maxI2)
done

lemma le_max3I1: "(n2::nat) \<le> max n1 (max n2 n3)"
proof -
  have "n2 \<le> max n2 n3"
    by (rule le_maxI1)
  also
  have "max n2 n3 \<le> max n1 (max n2 n3)"
    by (rule le_maxI2)
  finally
  show ?thesis .
qed

lemma le_max3I2: "(n3::nat) \<le> max n1 (max n2 n3)"
proof -
  have "n3 \<le> max n2 n3"
    by (rule le_maxI2)
  also
  have "max n2 n3 \<le> max n1 (max n2 n3)"
    by (rule le_maxI2)
  finally
  show ?thesis .
qed


lemma eval_evaln: 
 (assumes eval: "G\<turnstile>s0 \<midarrow>t\<succ>\<rightarrow> (v,s1)" and
          wt: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>t\<Colon>T" and  
     conf_s0: "s0\<Colon>\<preceq>(G, L)" and
          wf: "wf_prog G"  
 )  "\<exists>n. G\<turnstile>s0 \<midarrow>t\<succ>\<midarrow>n\<rightarrow> (v,s1)"
proof -
  from eval 
  show "\<And> L accC T. \<lbrakk>s0\<Colon>\<preceq>(G, L);\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>t\<Colon>T\<rbrakk>
                     \<Longrightarrow> \<exists> n. G\<turnstile>s0 \<midarrow>t\<succ>\<midarrow>n\<rightarrow> (v,s1)"
       (is "PROP ?EqEval s0 s1 t v")
  proof (induct)
    case (Abrupt s t xc L accC T)
    obtain n where
      "G\<turnstile>(Some xc, s) \<midarrow>t\<succ>\<midarrow>n\<rightarrow> (arbitrary3 t, Some xc, s)"
      by (rules intro: evaln.Abrupt)
    then show ?case ..
  next
    case Skip
    show ?case by (blast intro: evaln.Skip)
  next
    case (Expr e s0 s1 v L accC T)
    then obtain n where
      "G\<turnstile>Norm s0 \<midarrow>e-\<succ>v\<midarrow>n\<rightarrow> s1"
      by (rules elim!: wt_elim_cases)
    then have "G\<turnstile>Norm s0 \<midarrow>Expr e\<midarrow>n\<rightarrow> s1"
      by (rule evaln.Expr) 
    then show ?case ..
  next
    case (Lab c l s0 s1 L accC T)
    then obtain n where
      "G\<turnstile>Norm s0 \<midarrow>c\<midarrow>n\<rightarrow> s1"
      by (rules elim!: wt_elim_cases)
    then have "G\<turnstile>Norm s0 \<midarrow>l\<bullet> c\<midarrow>n\<rightarrow> abupd (absorb (Break l)) s1"
      by (rule evaln.Lab)
    then show ?case ..
  next
    case (Comp c1 c2 s0 s1 s2 L accC T)
    with wf obtain n1 n2 where
      "G\<turnstile>Norm s0 \<midarrow>c1\<midarrow>n1\<rightarrow> s1"
      "G\<turnstile>s1 \<midarrow>c2\<midarrow>n2\<rightarrow> s2"
      by (blast elim!: wt_elim_cases dest: eval_type_sound)
    then have "G\<turnstile>Norm s0 \<midarrow>c1;; c2\<midarrow>max n1 n2\<rightarrow> s2"
      by (blast intro: evaln.Comp dest: evaln_max2 )
    then show ?case ..
  next
    case (If b c1 c2 e s0 s1 s2 L accC T)
    with wf obtain
      "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>e\<Colon>-PrimT Boolean"
      "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>(if the_Bool b then c1 else c2)\<Colon>\<surd>"
      by (cases "the_Bool b") (auto elim!: wt_elim_cases)
    with If wf obtain n1 n2 where
      "G\<turnstile>Norm s0 \<midarrow>e-\<succ>b\<midarrow>n1\<rightarrow> s1"
      "G\<turnstile>s1 \<midarrow>(if the_Bool b then c1 else c2)\<midarrow>n2\<rightarrow> s2"
      by (blast dest: eval_type_sound)
    then have "G\<turnstile>Norm s0 \<midarrow>If(e) c1 Else c2\<midarrow>max n1 n2\<rightarrow> s2"
      by (blast intro: evaln.If dest: evaln_max2)
    then show ?case ..
  next
    case (Loop b c e l s0 s1 s2 s3 L accC T)
    have eval_e: "G\<turnstile>Norm s0 \<midarrow>e-\<succ>b\<rightarrow> s1" .
    have hyp_e: "PROP ?EqEval (Norm s0) s1 (In1l e) (In1 b)" .
    have conf_s0: "Norm s0\<Colon>\<preceq>(G, L)" .
    have      wt: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>In1r (l\<bullet> While(e) c)\<Colon>T" .
    then obtain wt_e: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>e\<Colon>-PrimT Boolean" and
                wt_c: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>c\<Colon>\<surd>"
      by (rule wt_elim_cases) (blast)
    from conf_s0 wt_e 
    obtain n1 where
      "G\<turnstile>Norm s0 \<midarrow>e-\<succ>b\<midarrow>n1\<rightarrow> s1"
      by (rules dest: hyp_e)
    moreover
    from eval_e wt_e conf_s0 wf
    have conf_s1: "s1\<Colon>\<preceq>(G, L)"
      by (rules dest: eval_type_sound)
    obtain n2 where
      "if normal s1 \<and> the_Bool b 
             then (G\<turnstile>s1 \<midarrow>c\<midarrow>n2\<rightarrow> s2 \<and> 
                   G\<turnstile>(abupd (absorb (Cont l)) s2)\<midarrow>l\<bullet> While(e) c\<midarrow>n2\<rightarrow> s3)
	     else s3 = s1"
    proof (cases "normal s1 \<and> the_Bool b")
      case True
      from Loop True have hyp_c: "PROP ?EqEval s1 s2 (In1r c) \<diamondsuit>"
	by (auto)
      from Loop True have hyp_w: "PROP ?EqEval (abupd (absorb (Cont l)) s2)
                                        s3 (In1r (l\<bullet> While(e) c)) \<diamondsuit>"
	by (auto)
      from Loop True have eval_c: "G\<turnstile>s1 \<midarrow>c\<rightarrow> s2"
	by simp
      from conf_s1 wt_c
      obtain m1 where 
	evaln_c: "G\<turnstile>s1 \<midarrow>c\<midarrow>m1\<rightarrow> s2"
	by (rules dest: hyp_c)
      moreover
      from eval_c conf_s1 wt_c wf
      have "s2\<Colon>\<preceq>(G, L)"
	by (rules dest: eval_type_sound)
      then
      have "abupd (absorb (Cont l)) s2 \<Colon>\<preceq>(G, L)"
	by (cases s2) (auto intro: conforms_absorb)
      from this and wt
      obtain m2 where 
	"G\<turnstile>abupd (absorb (Cont l)) s2 \<midarrow>l\<bullet> While(e) c\<midarrow>m2\<rightarrow> s3"
	by (blast dest: hyp_w)
      moreover note True and that
      ultimately show ?thesis
	by simp (rules intro: evaln_nonstrict le_maxI1 le_maxI2)
    next
      case False
      with Loop have "s3 = s1"
	by simp
      with False that
      show ?thesis
	by auto 
    qed
    ultimately
    have "G\<turnstile>Norm s0 \<midarrow>l\<bullet> While(e) c\<midarrow>max n1 n2\<rightarrow> s3"
      apply -
      apply (rule evaln.Loop)
      apply   (rules intro: evaln_nonstrict intro: le_maxI1)

      apply   (auto intro: evaln_nonstrict intro: le_maxI2)
      done
    then show ?case ..
  next
    case (Do j s L accC T)
    have "G\<turnstile>Norm s \<midarrow>Do j\<midarrow>n\<rightarrow> (Some (Jump j), s)"
      by (rule evaln.Do)
    then show ?case ..
  next
    case (Throw a e s0 s1 L accC T)
    then obtain n where
      "G\<turnstile>Norm s0 \<midarrow>e-\<succ>a\<midarrow>n\<rightarrow> s1"
      by (rules elim!: wt_elim_cases)
    then have "G\<turnstile>Norm s0 \<midarrow>Throw e\<midarrow>n\<rightarrow> abupd (throw a) s1"
      by (rule evaln.Throw)
    then show ?case ..
  next 
    case (Try catchC c1 c2 s0 s1 s2 s3 vn L accC T)
    have  hyp_c1: "PROP ?EqEval (Norm s0) s1 (In1r c1) \<diamondsuit>" .
    have eval_c1: "G\<turnstile>Norm s0 \<midarrow>c1\<rightarrow> s1" .
    have conf_s0: "Norm s0\<Colon>\<preceq>(G, L)" .
    have      wt: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>In1r (Try c1 Catch(catchC vn) c2)\<Colon>T" .
    then obtain 
      wt_c1: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>c1\<Colon>\<surd>" and
      wt_c2: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<lparr>lcl := L(VName vn\<mapsto>Class catchC)\<rparr>\<turnstile>c2\<Colon>\<surd>"
      by (rule wt_elim_cases) (auto)
    from conf_s0 wt_c1
    obtain n1 where
      "G\<turnstile>Norm s0 \<midarrow>c1\<midarrow>n1\<rightarrow> s1"
      by (blast dest: hyp_c1)
    moreover 
    have sxalloc: "G\<turnstile>s1 \<midarrow>sxalloc\<rightarrow> s2" .
    moreover
    from eval_c1 wt_c1 conf_s0 wf
    have "s1\<Colon>\<preceq>(G, L)"
      by (blast dest: eval_type_sound)
    with sxalloc wf
    have conf_s2: "s2\<Colon>\<preceq>(G, L)" 
      by (auto dest: sxalloc_type_sound split: option.splits)
    obtain n2 where
      "if G,s2\<turnstile>catch catchC then G\<turnstile>new_xcpt_var vn s2 \<midarrow>c2\<midarrow>n2\<rightarrow> s3 else s3 = s2"
    proof (cases "G,s2\<turnstile>catch catchC")
      case True
      note Catch = this
      with Try have hyp_c2: "PROP ?EqEval (new_xcpt_var vn s2) s3 (In1r c2) \<diamondsuit>"
	by auto
      show ?thesis
      proof (cases "normal s1")
	case True
	with sxalloc wf 
	have eq_s2_s1: "s2=s1"
	  by (auto dest: sxalloc_type_sound split: option.splits)
	with True 
	have "\<not>  G,s2\<turnstile>catch catchC"
	  by (simp add: catch_def)
	with Catch show ?thesis 
	  by (contradiction)
      next 
	case False
	with sxalloc wf
	obtain a 
	  where xcpt_s2: "abrupt s2 = Some (Xcpt (Loc a))"
	  by (auto dest!: sxalloc_type_sound split: option.splits)
	with Catch
	have "G\<turnstile>obj_ty (the (globs (store s2) (Heap a)))\<preceq>Class catchC"
	  by (cases s2) simp
	with xcpt_s2 conf_s2 wf 
	have "new_xcpt_var vn s2\<Colon>\<preceq>(G, L(VName vn\<mapsto>Class catchC))"
	  by (auto dest: Try_lemma)
	(* FIXME extract lemma for this conformance, also usefull for
               eval_type_sound and evaln_eval *)
	from this wt_c2
	obtain m where "G\<turnstile>new_xcpt_var vn s2 \<midarrow>c2\<midarrow>m\<rightarrow> s3"
	  by (auto dest: hyp_c2)
	with True that
	show ?thesis
	  by simp
      qed
    next
      case False
      with Try
      have "s3=s2"
	by simp
      with False and that
      show ?thesis
	by simp
    qed
    ultimately
    have "G\<turnstile>Norm s0 \<midarrow>Try c1 Catch(catchC vn) c2\<midarrow>max n1 n2\<rightarrow> s3"
      by (auto intro!: evaln.Try le_maxI1 le_maxI2)
    then show ?case ..
  next
    case (Fin c1 c2 s0 s1 s2 x1 L accC T)
    with wf obtain n1 n2 where 
      "G\<turnstile>Norm s0 \<midarrow>c1\<midarrow>n1\<rightarrow> (x1, s1)"
      "G\<turnstile>Norm s1 \<midarrow>c2\<midarrow>n2\<rightarrow> s2"
      by (blast elim!: wt_elim_cases 
	         dest: eval_type_sound intro: conforms_NormI)
    then have 
     "G\<turnstile>Norm s0 \<midarrow>c1 Finally c2\<midarrow>max n1 n2\<rightarrow> abupd (abrupt_if (x1 \<noteq> None) x1) s2"
      by (blast intro: evaln.Fin dest: evaln_max2)
    then show ?case ..
  next
    case (Init C c s0 s1 s2 s3 L accC T)
    have     cls: "the (class G C) = c" .
    have conf_s0: "Norm s0\<Colon>\<preceq>(G, L)" .
    have      wt: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>In1r (Init C)\<Colon>T" .
    with cls
    have cls_C: "class G C = Some c"
      by - (erule wt_elim_cases,auto)
    obtain n where
      "if inited C (globs s0) then s3 = Norm s0
       else (G\<turnstile>Norm (init_class_obj G C s0)
	      \<midarrow>(if C = Object then Skip else Init (super c))\<midarrow>n\<rightarrow> s1 \<and>
	           G\<turnstile>set_lvars empty s1 \<midarrow>init c\<midarrow>n\<rightarrow> s2 \<and> 
                   s3 = restore_lvars s1 s2)"
    proof (cases "inited C (globs s0)")
      case True
      with Init have "s3 = Norm s0"
	by simp
      with True that show ?thesis 
	by simp
    next
      case False
      with Init
      obtain 
	hyp_init_super: 
        "PROP ?EqEval (Norm ((init_class_obj G C) s0)) s1
	               (In1r (if C = Object then Skip else Init (super c))) \<diamondsuit>"
	and 
        hyp_init_c:
	   "PROP ?EqEval ((set_lvars empty) s1) s2 (In1r (init c)) \<diamondsuit>" and
	s3: "s3 = (set_lvars (locals (store s1))) s2" and
	eval_init_super: 
	"G\<turnstile>Norm ((init_class_obj G C) s0) 
           \<midarrow>(if C = Object then Skip else Init (super c))\<rightarrow> s1"
	by (simp only: if_False)
      from conf_s0 wf cls_C False
      have conf_s0': "(Norm ((init_class_obj G C) s0))\<Colon>\<preceq>(G, L)"
	by (auto dest: conforms_init_class_obj)
      moreover
      from wf cls_C 
      have wt_init_super:
           "\<lparr>prg = G, cls = accC, lcl = L\<rparr>
                  \<turnstile>(if C = Object then Skip else Init (super c))\<Colon>\<surd>"
	by (cases "C=Object")
           (auto dest: wf_prog_cdecl wf_cdecl_supD is_acc_classD)
      ultimately
      obtain m1 where  
	   "G\<turnstile>Norm ((init_class_obj G C) s0) 
            \<midarrow>(if C = Object then Skip else Init (super c))\<midarrow>m1\<rightarrow> s1"
	by (rules dest: hyp_init_super)
      moreover
      from eval_init_super conf_s0' wt_init_super wf
      have "s1\<Colon>\<preceq>(G, L)"
	by (rules dest: eval_type_sound)
      then
      have "(set_lvars empty) s1\<Colon>\<preceq>(G, empty)"
	by (cases s1) (auto dest: conforms_set_locals )
      with wf cls_C 
      obtain m2 where
	"G\<turnstile>(set_lvars empty) s1 \<midarrow>init c\<midarrow>m2\<rightarrow> s2"
	by (blast dest!: hyp_init_c 
                   dest: wf_prog_cdecl intro!: wf_cdecl_wt_init)
      moreover note s3 and False and that
      ultimately show ?thesis
	by simp (rules intro: evaln_nonstrict le_maxI1 le_maxI2)
    qed
    from cls this have "G\<turnstile>Norm s0 \<midarrow>Init C\<midarrow>n\<rightarrow> s3"
      by (rule evaln.Init)
    then show ?case ..
  next
    case (NewC C a s0 s1 s2 L accC T)
    with wf obtain n where 
     "G\<turnstile>Norm s0 \<midarrow>Init C\<midarrow>n\<rightarrow> s1"
      by (blast elim!: wt_elim_cases dest: is_acc_classD)
    with NewC 
    have "G\<turnstile>Norm s0 \<midarrow>NewC C-\<succ>Addr a\<midarrow>n\<rightarrow> s2"
      by (rules intro: evaln.NewC)
    then show ?case ..
  next
    case (NewA T a e i s0 s1 s2 s3 L accC Ta)
    hence "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>init_comp_ty T\<Colon>\<surd>" 
      by (auto elim!: wt_elim_cases 
              intro!: wt_init_comp_ty dest: is_acc_typeD)
    with NewA wf obtain n1 n2 where 
      "G\<turnstile>Norm s0 \<midarrow>init_comp_ty T\<midarrow>n1\<rightarrow> s1"
      "G\<turnstile>s1 \<midarrow>e-\<succ>i\<midarrow>n2\<rightarrow> s2"      
      by (blast elim!: wt_elim_cases dest: eval_type_sound)
    moreover
    have "G\<turnstile>abupd (check_neg i) s2 \<midarrow>halloc Arr T (the_Intg i)\<succ>a\<rightarrow> s3" .
    ultimately
    have "G\<turnstile>Norm s0 \<midarrow>New T[e]-\<succ>Addr a\<midarrow>max n1 n2\<rightarrow> s3"
      by (blast intro: evaln.NewA dest: evaln_max2)
    then show ?case ..
  next
    case (Cast castT e s0 s1 s2 v L accC T)
    with wf obtain n where
      "G\<turnstile>Norm s0 \<midarrow>e-\<succ>v\<midarrow>n\<rightarrow> s1"
      by (rules elim!: wt_elim_cases)
    moreover 
    have "s2 = abupd (raise_if (\<not> G,snd s1\<turnstile>v fits castT) ClassCast) s1" .
    ultimately
    have "G\<turnstile>Norm s0 \<midarrow>Cast castT e-\<succ>v\<midarrow>n\<rightarrow> s2"
      by (rule evaln.Cast)
    then show ?case ..
  next
    case (Inst T b e s0 s1 v L accC T')
    with wf obtain n where
      "G\<turnstile>Norm s0 \<midarrow>e-\<succ>v\<midarrow>n\<rightarrow> s1"
      by (rules elim!: wt_elim_cases)
    moreover 
    have "b = (v \<noteq> Null \<and> G,snd s1\<turnstile>v fits RefT T)" .
    ultimately
    have "G\<turnstile>Norm s0 \<midarrow>e InstOf T-\<succ>Bool b\<midarrow>n\<rightarrow> s1"
      by (rule evaln.Inst)
    then show ?case ..
  next
    case (Lit s v L accC T)
    have "G\<turnstile>Norm s \<midarrow>Lit v-\<succ>v\<midarrow>n\<rightarrow> Norm s"
      by (rule evaln.Lit)
    then show ?case ..
  next
    case (Super s L accC T)
    have "G\<turnstile>Norm s \<midarrow>Super-\<succ>val_this s\<midarrow>n\<rightarrow> Norm s"
      by (rule evaln.Super)
    then show ?case ..
  next
    case (Acc f s0 s1 v va L accC T)
    with wf obtain n where
      "G\<turnstile>Norm s0 \<midarrow>va=\<succ>(v, f)\<midarrow>n\<rightarrow> s1"
      by (rules elim!: wt_elim_cases)
    then
    have "G\<turnstile>Norm s0 \<midarrow>Acc va-\<succ>v\<midarrow>n\<rightarrow> s1"
      by (rule evaln.Acc)
    then show ?case ..
  next
    case (Ass e f s0 s1 s2 v var w L accC T)
    with wf obtain n1 n2 where 
      "G\<turnstile>Norm s0 \<midarrow>var=\<succ>(w, f)\<midarrow>n1\<rightarrow> s1"
      "G\<turnstile>s1 \<midarrow>e-\<succ>v\<midarrow>n2\<rightarrow> s2"      
      by (blast elim!: wt_elim_cases dest: eval_type_sound)
    then
    have "G\<turnstile>Norm s0 \<midarrow>var:=e-\<succ>v\<midarrow>max n1 n2\<rightarrow> assign f v s2"
      by (blast intro: evaln.Ass dest: evaln_max2)
    then show ?case ..
  next
    case (Cond b e0 e1 e2 s0 s1 s2 v L accC T)
    have hyp_e0: "PROP ?EqEval (Norm s0) s1 (In1l e0) (In1 b)" .
    have hyp_if: "PROP ?EqEval s1 s2 
                              (In1l (if the_Bool b then e1 else e2)) (In1 v)" .
    have conf_s0: "Norm s0\<Colon>\<preceq>(G, L)" .
    have wt: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>In1l (e0 ? e1 : e2)\<Colon>T" .
    then obtain T1 T2 statT where
       wt_e0: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>e0\<Colon>-PrimT Boolean" and
       wt_e1: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>e1\<Colon>-T1" and
       wt_e2: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>e2\<Colon>-T2" and 
       statT: "G\<turnstile>T1\<preceq>T2 \<and> statT = T2  \<or>  G\<turnstile>T2\<preceq>T1 \<and> statT =  T1" and
       T    : "T=Inl statT"
      by (rule wt_elim_cases) auto
    have eval_e0: "G\<turnstile>Norm s0 \<midarrow>e0-\<succ>b\<rightarrow> s1" .
    from conf_s0 wt_e0
    obtain n1 where 
      "G\<turnstile>Norm s0 \<midarrow>e0-\<succ>b\<midarrow>n1\<rightarrow> s1"
      by (rules dest: hyp_e0)
    moreover
    from eval_e0 conf_s0 wf wt_e0
    have "s1\<Colon>\<preceq>(G, L)"
      by (blast dest: eval_type_sound)
    with wt_e1 wt_e2 statT hyp_if obtain n2 where
      "G\<turnstile>s1 \<midarrow>(if the_Bool b then e1 else e2)-\<succ>v\<midarrow>n2\<rightarrow> s2"
      by  (cases "the_Bool b") force+
    ultimately
    have "G\<turnstile>Norm s0 \<midarrow>e0 ? e1 : e2-\<succ>v\<midarrow>max n1 n2\<rightarrow> s2"
      by (blast intro: evaln.Cond dest: evaln_max2)
    then show ?case ..
  next
    case (Call invDeclC a' accC' args e mn mode pTs' s0 s1 s2 s3 s3' s4 statT 
      v vs L accC T)
    (* Repeats large parts of the type soundness proof. One should factor
       out some lemmata about the relations and conformance of s2, s3 and s3'*)
    have eval_e: "G\<turnstile>Norm s0 \<midarrow>e-\<succ>a'\<rightarrow> s1" .
    have eval_args: "G\<turnstile>s1 \<midarrow>args\<doteq>\<succ>vs\<rightarrow> s2" .
    have invDeclC: "invDeclC 
                      = invocation_declclass G mode (store s2) a' statT 
                           \<lparr>name = mn, parTs = pTs'\<rparr>" .
    have
      init_lvars: "s3 = 
             init_lvars G invDeclC \<lparr>name = mn, parTs = pTs'\<rparr> mode a' vs s2" .
    have
      check: "s3' =
       check_method_access G accC' statT mode \<lparr>name = mn, parTs = pTs'\<rparr> a' s3" .
    have eval_methd: 
           "G\<turnstile>s3' \<midarrow>Methd invDeclC \<lparr>name = mn, parTs = pTs'\<rparr>-\<succ>v\<rightarrow> s4" .
    have     hyp_e: "PROP ?EqEval (Norm s0) s1 (In1l e) (In1 a')" .
    have  hyp_args: "PROP ?EqEval s1 s2 (In3 args) (In3 vs)" .
    have hyp_methd: "PROP ?EqEval s3' s4 
                     (In1l (Methd invDeclC \<lparr>name = mn, parTs = pTs'\<rparr>)) (In1 v)".
    have conf_s0: "Norm s0\<Colon>\<preceq>(G, L)" .
    have      wt: "\<lparr>prg=G, cls=accC, lcl=L\<rparr>
                    \<turnstile>In1l ({accC',statT,mode}e\<cdot>mn( {pTs'}args))\<Colon>T" .
    from wt obtain pTs statDeclT statM where
                 wt_e: "\<lparr>prg=G, cls=accC, lcl=L\<rparr>\<turnstile>e\<Colon>-RefT statT" and
              wt_args: "\<lparr>prg=G, cls=accC, lcl=L\<rparr>\<turnstile>args\<Colon>\<doteq>pTs" and
                statM: "max_spec G accC statT \<lparr>name=mn,parTs=pTs\<rparr> 
                         = {((statDeclT,statM),pTs')}" and
                 mode: "mode = invmode statM e" and
                    T: "T =Inl (resTy statM)" and
        eq_accC_accC': "accC=accC'"
      by (rule wt_elim_cases) auto
    from conf_s0 wt_e
    obtain n1 where
      evaln_e: "G\<turnstile>Norm s0 \<midarrow>e-\<succ>a'\<midarrow>n1\<rightarrow> s1"
      by (rules dest: hyp_e)
    from wf eval_e conf_s0 wt_e
    obtain conf_s1: "s1\<Colon>\<preceq>(G, L)" and
           conf_a': "normal s1 \<Longrightarrow> G, store s1\<turnstile>a'\<Colon>\<preceq>RefT statT"  
      by (auto dest!: eval_type_sound)
    from conf_s1 wt_args
    obtain n2 where
      evaln_args: "G\<turnstile>s1 \<midarrow>args\<doteq>\<succ>vs\<midarrow>n2\<rightarrow> s2"
      by (blast dest: hyp_args)
    from wt_args conf_s1 eval_args wf 
    obtain    conf_s2: "s2\<Colon>\<preceq>(G, L)" and
            conf_args: "normal s2 
                         \<Longrightarrow>  list_all2 (conf G (store s2)) vs pTs"  
      by (auto dest!: eval_type_sound)
    from statM 
    obtain
       statM': "(statDeclT,statM)\<in>mheads G accC statT \<lparr>name=mn,parTs=pTs'\<rparr>" and
       pTs_widen: "G\<turnstile>pTs[\<preceq>]pTs'"
      by (blast dest: max_spec2mheads)
    from check
    have eq_store_s3'_s3: "store s3'=store s3"
      by (cases s3) (simp add: check_method_access_def Let_def)
    obtain invC
      where invC: "invC = invocation_class mode (store s2) a' statT"
      by simp
    with init_lvars
    have invC': "invC = (invocation_class mode (store s3) a' statT)"
      by (cases s2,cases mode) (auto simp add: init_lvars_def2 )
    obtain n3 where
     "G\<turnstile>Norm s0 \<midarrow>{accC',statT,mode}e\<cdot>mn( {pTs'}args)-\<succ>v\<midarrow>n3\<rightarrow> 
          (set_lvars (locals (store s2))) s4"
    proof (cases "normal s2")
      case False
      with init_lvars 
      obtain keep_abrupt: "abrupt s3 = abrupt s2" and
             "store s3 = store (init_lvars G invDeclC \<lparr>name = mn, parTs = pTs'\<rparr> 
                                            mode a' vs s2)" 
	by (auto simp add: init_lvars_def2)
      moreover
      from keep_abrupt False check
      have eq_s3'_s3: "s3'=s3" 
	by (auto simp add: check_method_access_def Let_def)
      moreover
      from eq_s3'_s3 False keep_abrupt eval_methd init_lvars
      obtain "s4=s3'"
	 "In1 v=arbitrary3 (In1l (Methd invDeclC \<lparr>name = mn, parTs = pTs'\<rparr>))"
	by auto
      moreover note False evaln.Abrupt
      ultimately obtain m where 
	"G\<turnstile>s3' \<midarrow>Methd invDeclC \<lparr>name = mn, parTs = pTs'\<rparr>-\<succ>v\<midarrow>m\<rightarrow> s4"
	by force
      from evaln_e evaln_args invDeclC init_lvars eq_s3'_s3 this
      have 
       "G\<turnstile>Norm s0 \<midarrow>{accC',statT,mode}e\<cdot>mn( {pTs'}args)-\<succ>v\<midarrow>max n1 (max n2 m)\<rightarrow> 
            (set_lvars (locals (store s2))) s4"
	by (auto intro!: evaln.Call le_maxI1 le_max3I1 le_max3I2)
      with that show ?thesis 
	by rules
    next
      case True
      note normal_s2 = True
      with eval_args
      have normal_s1: "normal s1"
	by (cases "normal s1") auto
      with conf_a' eval_args 
      have conf_a'_s2: "G, store s2\<turnstile>a'\<Colon>\<preceq>RefT statT"
	by (auto dest: eval_gext intro: conf_gext)
      show ?thesis
      proof (cases "a'=Null \<longrightarrow> is_static statM")
	case False
	then obtain not_static: "\<not> is_static statM" and Null: "a'=Null" 
	  by blast
	with normal_s2 init_lvars mode
	obtain np: "abrupt s3 = Some (Xcpt (Std NullPointer))" and
                   "store s3 = store (init_lvars G invDeclC 
                                       \<lparr>name = mn, parTs = pTs'\<rparr> mode a' vs s2)"
	  by (auto simp add: init_lvars_def2)
	moreover
	from np check
	have eq_s3'_s3: "s3'=s3" 
	  by (auto simp add: check_method_access_def Let_def)
	moreover
	from eq_s3'_s3 np eval_methd init_lvars
	obtain "s4=s3'"
	  "In1 v=arbitrary3 (In1l (Methd invDeclC \<lparr>name = mn, parTs = pTs'\<rparr>))"
	  by auto
	moreover note np
	ultimately obtain m where 
	  "G\<turnstile>s3' \<midarrow>Methd invDeclC \<lparr>name = mn, parTs = pTs'\<rparr>-\<succ>v\<midarrow>m\<rightarrow> s4"
	  by force
	from evaln_e evaln_args invDeclC init_lvars eq_s3'_s3 this
	have 
        "G\<turnstile>Norm s0 \<midarrow>{accC',statT,mode}e\<cdot>mn( {pTs'}args)-\<succ>v\<midarrow>max n1 (max n2 m)\<rightarrow> 
            (set_lvars (locals (store s2))) s4"
	  by (auto intro!: evaln.Call le_maxI1 le_max3I1 le_max3I2)
	with that show ?thesis 
	  by rules
      next
	case True
	with mode have notNull: "mode = IntVir \<longrightarrow> a' \<noteq> Null"
	  by (auto dest!: Null_staticD)
	with conf_s2 conf_a'_s2 wf invC 
	have dynT_prop: "G\<turnstile>mode\<rightarrow>invC\<preceq>statT"
	  by (cases s2) (auto intro: DynT_propI)
	with wt_e statM' invC mode wf 
	obtain dynM where 
           dynM: "dynlookup G statT invC  \<lparr>name=mn,parTs=pTs'\<rparr> = Some dynM" and
           acc_dynM: "G \<turnstile>Methd  \<lparr>name=mn,parTs=pTs'\<rparr> dynM 
                          in invC dyn_accessible_from accC"
	  by (force dest!: call_access_ok)
	with invC' check eq_accC_accC'
	have eq_s3'_s3: "s3'=s3"
	  by (auto simp add: check_method_access_def Let_def)
	from dynT_prop wf wt_e statM' mode invC invDeclC dynM 
	obtain 
	   wf_dynM: "wf_mdecl G invDeclC (\<lparr>name=mn,parTs=pTs'\<rparr>,mthd dynM)" and
	     dynM': "methd G invDeclC \<lparr>name=mn,parTs=pTs'\<rparr> = Some dynM" and
           iscls_invDeclC: "is_class G invDeclC" and
	        invDeclC': "invDeclC = declclass dynM" and
	     invC_widen: "G\<turnstile>invC\<preceq>\<^sub>C invDeclC" and
	   is_static_eq: "is_static dynM = is_static statM" and
	   involved_classes_prop:
             "(if invmode statM e = IntVir
               then \<forall>statC. statT = ClassT statC \<longrightarrow> G\<turnstile>invC\<preceq>\<^sub>C statC
               else ((\<exists>statC. statT = ClassT statC \<and> G\<turnstile>statC\<preceq>\<^sub>C invDeclC) \<or>
                     (\<forall>statC. statT \<noteq> ClassT statC \<and> invDeclC = Object)) \<and>
                      statDeclT = ClassT invDeclC)"
	  by (auto dest: DynT_mheadsD)
	obtain L' where 
	   L':"L'=(\<lambda> k. 
                 (case k of
                    EName e
                    \<Rightarrow> (case e of 
                          VNam v 
                          \<Rightarrow>(table_of (lcls (mbody (mthd dynM)))
                             (pars (mthd dynM)[\<mapsto>]pTs')) v
                        | Res \<Rightarrow> Some (resTy dynM))
                  | This \<Rightarrow> if is_static statM 
                            then None else Some (Class invDeclC)))"
	  by simp
	from wf_dynM [THEN wf_mdeclD1, THEN conjunct1] normal_s2 conf_s2 wt_e
              wf eval_args conf_a' mode notNull wf_dynM involved_classes_prop
	have conf_s3: "s3\<Colon>\<preceq>(G,L')"
	   apply - 
          (*FIXME confomrs_init_lvars should be 
                adjusted to be more directy applicable *)
	   apply (drule conforms_init_lvars [of G invDeclC 
                  "\<lparr>name=mn,parTs=pTs'\<rparr>" dynM "store s2" vs pTs "abrupt s2" 
                  L statT invC a' "(statDeclT,statM)" e])
	     apply (rule wf)
	     apply (rule conf_args,assumption)
	     apply (simp add: pTs_widen)
	     apply (cases s2,simp)
	     apply (rule dynM')
	     apply (force dest: ty_expr_is_type)
	     apply (rule invC_widen)
	     apply (force intro: conf_gext dest: eval_gext)
	     apply simp
	     apply simp
	     apply (simp add: invC)
	     apply (simp add: invDeclC)
	     apply (force dest: wf_mdeclD1 is_acc_typeD)
	     apply (cases s2, simp add: L' init_lvars
	                      cong add: lname.case_cong ename.case_cong)
	   done
	with is_static_eq wf_dynM L'
	obtain mthdT where
	   "\<lparr>prg=G,cls=invDeclC,lcl=L'\<rparr>
            \<turnstile>Body invDeclC (stmt (mbody (mthd dynM)))\<Colon>-mthdT" 
	  by - (drule wf_mdecl_bodyD,
                simp cong add: lname.case_cong ename.case_cong)
	with dynM' iscls_invDeclC invDeclC'
	have
	   "\<lparr>prg=G,cls=invDeclC,lcl=L'\<rparr>
            \<turnstile>(Methd invDeclC \<lparr>name = mn, parTs = pTs'\<rparr>)\<Colon>-mthdT"
	  by (auto intro: wt.Methd)
	with conf_s3 eq_s3'_s3 hyp_methd
	obtain m where
	   "G\<turnstile>s3' \<midarrow>Methd invDeclC \<lparr>name = mn, parTs = pTs'\<rparr>-\<succ>v\<midarrow>m\<rightarrow> s4"
	  by (blast)
	from evaln_e evaln_args invDeclC init_lvars  eq_s3'_s3 this
	have 
        "G\<turnstile>Norm s0 \<midarrow>{accC',statT,mode}e\<cdot>mn( {pTs'}args)-\<succ>v\<midarrow>max n1 (max n2 m)\<rightarrow> 
            (set_lvars (locals (store s2))) s4"
	  by (auto intro!: evaln.Call le_maxI1 le_max3I1 le_max3I2)
	with that show ?thesis 
	  by rules
      qed
    qed
    then show ?case ..
  next
    case (Methd D s0 s1 sig v L accC T)
    then obtain n where
      "G\<turnstile>Norm s0 \<midarrow>body G D sig-\<succ>v\<midarrow>n\<rightarrow> s1"
      by - (erule wt_elim_cases, force simp add: body_def2)
    then have "G\<turnstile>Norm s0 \<midarrow>Methd D sig-\<succ>v\<midarrow>Suc n\<rightarrow> s1"
      by (rule evaln.Methd)
    then show ?case ..
  next
    case (Body D c s0 s1 s2 L accC T)
    with wf obtain n1 n2 where 
      "G\<turnstile>Norm s0 \<midarrow>Init D\<midarrow>n1\<rightarrow> s1"
      "G\<turnstile>s1 \<midarrow>c\<midarrow>n2\<rightarrow> s2"
      by (blast elim!: wt_elim_cases dest: eval_type_sound)
    then have 
     "G\<turnstile>Norm s0 \<midarrow>Body D c-\<succ>the (locals (store s2) Result)\<midarrow>max n1 n2
       \<rightarrow> abupd (absorb Ret) s2"
      by (blast intro: evaln.Body dest: evaln_max2)
    then show ?case ..
  next
    case (LVar s vn L accC T)
    obtain n where
      "G\<turnstile>Norm s \<midarrow>LVar vn=\<succ>lvar vn s\<midarrow>n\<rightarrow> Norm s"
      by (rules intro: evaln.LVar)
    then show ?case ..
  next
    case (FVar a accC e fn s0 s1 s2 s2' s3 stat statDeclC v L accC' T)
    have eval_init: "G\<turnstile>Norm s0 \<midarrow>Init statDeclC\<rightarrow> s1" .
    have eval_e: "G\<turnstile>s1 \<midarrow>e-\<succ>a\<rightarrow> s2" .
    have check: "s3 = check_field_access G accC statDeclC fn stat a s2'" .
    have hyp_init: "PROP ?EqEval (Norm s0) s1 (In1r (Init statDeclC)) \<diamondsuit>" .
    have hyp_e: "PROP ?EqEval s1 s2 (In1l e) (In1 a)" .
    have fvar: "(v, s2') = fvar statDeclC stat fn a s2" .
    have conf_s0: "Norm s0\<Colon>\<preceq>(G, L)" .
    have wt: "\<lparr>prg=G, cls=accC', lcl=L\<rparr>\<turnstile>In2 ({accC,statDeclC,stat}e..fn)\<Colon>T" .
    then obtain statC f where
                wt_e: "\<lparr>prg=G, cls=accC, lcl=L\<rparr>\<turnstile>e\<Colon>-Class statC" and
            accfield: "accfield G accC statC fn = Some (statDeclC,f)" and
                stat: "stat=is_static f" and
               accC': "accC'=accC" and
	           T: "T=(Inl (type f))"
       by (rule wt_elim_cases) (auto simp add: member_is_static_simp)
    from wf wt_e 
    have iscls_statC: "is_class G statC"
      by (auto dest: ty_expr_is_type type_is_class)
    with wf accfield 
    have iscls_statDeclC: "is_class G statDeclC"
      by (auto dest!: accfield_fields dest: fields_declC)
    then 
    have wt_init: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>(Init statDeclC)\<Colon>\<surd>"
      by simp
    from conf_s0 wt_init
    obtain n1 where
      evaln_init: "G\<turnstile>Norm s0 \<midarrow>Init statDeclC\<midarrow>n1\<rightarrow> s1"
      by (rules dest: hyp_init)
    from eval_init wt_init conf_s0 wf 
    have conf_s1: "s1\<Colon>\<preceq>(G, L)"
      by (blast dest: eval_type_sound)
    with wt_e
    obtain n2 where
      evaln_e: "G\<turnstile>s1 \<midarrow>e-\<succ>a\<midarrow>n2\<rightarrow> s2"
      by (blast dest: hyp_e)
    from eval_e wf conf_s1 wt_e
    obtain conf_s2: "s2\<Colon>\<preceq>(G, L)" and
            conf_a: "normal s2 \<longrightarrow> G,store s2\<turnstile>a\<Colon>\<preceq>Class statC"
      by (auto dest!: eval_type_sound)
    from accfield wt_e eval_init eval_e conf_s2 conf_a fvar stat check  wf
    have eq_s3_s2': "s3=s2'"  
      by (auto dest!: error_free_field_access)
    with evaln_init evaln_e fvar accC'
    have "G\<turnstile>Norm s0 \<midarrow>{accC,statDeclC,stat}e..fn=\<succ>v\<midarrow>max n1 n2\<rightarrow> s3"
      by (auto intro: evaln.FVar dest: evaln_max2)
    then show ?case ..
  next
    case (AVar a e1 e2 i s0 s1 s2 s2' v L accC T)
    with wf obtain n1 n2 where 
      "G\<turnstile>Norm s0 \<midarrow>e1-\<succ>a\<midarrow>n1\<rightarrow> s1"
      "G\<turnstile>s1 \<midarrow>e2-\<succ>i\<midarrow>n2\<rightarrow> s2"      
      by (blast elim!: wt_elim_cases dest: eval_type_sound)
    moreover 
    have "(v, s2') = avar G i a s2" .
    ultimately 
    have "G\<turnstile>Norm s0 \<midarrow>e1.[e2]=\<succ>v\<midarrow>max n1 n2\<rightarrow> s2'"
      by (blast intro!: evaln.AVar dest: evaln_max2)
    then show ?case ..
  next
    case (Nil s0 L accC T)
    show ?case by (rules intro: evaln.Nil)
  next
    case (Cons e es s0 s1 s2 v vs L accC T)
    with wf obtain n1 n2 where 
      "G\<turnstile>Norm s0 \<midarrow>e-\<succ>v\<midarrow>n1\<rightarrow> s1"
      "G\<turnstile>s1 \<midarrow>es\<doteq>\<succ>vs\<midarrow>n2\<rightarrow> s2"      
      by (blast elim!: wt_elim_cases dest: eval_type_sound)
    then
    have "G\<turnstile>Norm s0 \<midarrow>e # es\<doteq>\<succ>v # vs\<midarrow>max n1 n2\<rightarrow> s2"
      by (blast intro!: evaln.Cons dest: evaln_max2)
    then show ?case ..
  qed
qed

end
