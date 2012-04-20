(*  Title:      HOL/MicroJava/J/Eval.thy
    Author:     David von Oheimb
    Copyright   1999 Technische Universitaet Muenchen
*)

header {* \isaheader{Operational Evaluation (big step) Semantics} *}

theory Eval imports State WellType begin


  -- "Auxiliary notions"

definition fits :: "java_mb prog \<Rightarrow> state \<Rightarrow> val \<Rightarrow> ty \<Rightarrow> bool" ("_,_\<turnstile>_ fits _"[61,61,61,61]60) where
 "G,s\<turnstile>a' fits T  \<equiv> case T of PrimT T' \<Rightarrow> False | RefT T' \<Rightarrow> a'=Null \<or> G\<turnstile>obj_ty(lookup_obj s a')\<preceq>T"

definition catch :: "java_mb prog \<Rightarrow> xstate \<Rightarrow> cname \<Rightarrow> bool" ("_,_\<turnstile>catch _"[61,61,61]60) where
 "G,s\<turnstile>catch C\<equiv>  case abrupt s of None \<Rightarrow> False | Some a \<Rightarrow> G,store s\<turnstile> a fits Class C"

definition lupd :: "vname \<Rightarrow> val \<Rightarrow> state \<Rightarrow> state" ("lupd'(_\<mapsto>_')"[10,10]1000) where
 "lupd vn v   \<equiv> \<lambda> (hp,loc). (hp, (loc(vn\<mapsto>v)))"

definition new_xcpt_var :: "vname \<Rightarrow> xstate \<Rightarrow> xstate" where
 "new_xcpt_var vn \<equiv>  \<lambda>(x,s). Norm (lupd(vn\<mapsto>the x) s)"


  -- "Evaluation relations"

inductive
  eval :: "[java_mb prog,xstate,expr,val,xstate] => bool "
          ("_ \<turnstile> _ -_\<succ>_-> _" [51,82,60,82,82] 81)
  and evals :: "[java_mb prog,xstate,expr list,
                        val list,xstate] => bool "
          ("_ \<turnstile> _ -_[\<succ>]_-> _" [51,82,60,51,82] 81)
  and exec :: "[java_mb prog,xstate,stmt,    xstate] => bool "
          ("_ \<turnstile> _ -_-> _" [51,82,60,82] 81)
  for G :: "java_mb prog"
where

  -- "evaluation of expressions"

  XcptE:"G\<turnstile>(Some xc,s) -e\<succ>undefined-> (Some xc,s)"  -- "cf. 15.5"

  -- "cf. 15.8.1"
| NewC: "[| h = heap s; (a,x) = new_Addr h;
            h'= h(a\<mapsto>(C,init_vars (fields (G,C)))) |] ==>
         G\<turnstile>Norm s -NewC C\<succ>Addr a-> c_hupd h' (x,s)"

  -- "cf. 15.15"
| Cast: "[| G\<turnstile>Norm s0 -e\<succ>v-> (x1,s1);
            x2 = raise_if (\<not> cast_ok G C (heap s1) v) ClassCast x1 |] ==>
         G\<turnstile>Norm s0 -Cast C e\<succ>v-> (x2,s1)"

  -- "cf. 15.7.1"
| Lit:  "G\<turnstile>Norm s -Lit v\<succ>v-> Norm s"

| BinOp:"[| G\<turnstile>Norm s -e1\<succ>v1-> s1;
            G\<turnstile>s1     -e2\<succ>v2-> s2;
            v = (case bop of Eq  => Bool (v1 = v2)
                           | Add => Intg (the_Intg v1 + the_Intg v2)) |] ==>
         G\<turnstile>Norm s -BinOp bop e1 e2\<succ>v-> s2"

  -- "cf. 15.13.1, 15.2"
| LAcc: "G\<turnstile>Norm s -LAcc v\<succ>the (locals s v)-> Norm s"

  -- "cf. 15.25.1"
| LAss: "[| G\<turnstile>Norm s -e\<succ>v-> (x,(h,l));
            l' = (if x = None then l(va\<mapsto>v) else l) |] ==>
         G\<turnstile>Norm s -va::=e\<succ>v-> (x,(h,l'))"

  -- "cf. 15.10.1, 15.2"
| FAcc: "[| G\<turnstile>Norm s0 -e\<succ>a'-> (x1,s1); 
            v = the (snd (the (heap s1 (the_Addr a'))) (fn,T)) |] ==>
         G\<turnstile>Norm s0 -{T}e..fn\<succ>v-> (np a' x1,s1)"

  -- "cf. 15.25.1"
| FAss: "[| G\<turnstile>     Norm s0  -e1\<succ>a'-> (x1,s1); a = the_Addr a';
            G\<turnstile>(np a' x1,s1) -e2\<succ>v -> (x2,s2);
            h  = heap s2; (c,fs) = the (h a);
            h' = h(a\<mapsto>(c,(fs((fn,T)\<mapsto>v)))) |] ==>
         G\<turnstile>Norm s0 -{T}e1..fn:=e2\<succ>v-> c_hupd h' (x2,s2)"

  -- "cf. 15.11.4.1, 15.11.4.2, 15.11.4.4, 15.11.4.5, 14.15"
| Call: "[| G\<turnstile>Norm s0 -e\<succ>a'-> s1; a = the_Addr a';
            G\<turnstile>s1 -ps[\<succ>]pvs-> (x,(h,l)); dynT = fst (the (h a));
            (md,rT,pns,lvars,blk,res) = the (method (G,dynT) (mn,pTs));
            G\<turnstile>(np a' x,(h,(init_vars lvars)(pns[\<mapsto>]pvs)(This\<mapsto>a'))) -blk-> s3;
            G\<turnstile> s3 -res\<succ>v -> (x4,s4) |] ==>
         G\<turnstile>Norm s0 -{C}e..mn({pTs}ps)\<succ>v-> (x4,(heap s4,l))"


  -- "evaluation of expression lists"

  -- "cf. 15.5"
| XcptEs:"G\<turnstile>(Some xc,s) -e[\<succ>]undefined-> (Some xc,s)"

  -- "cf. 15.11.???"
| Nil:  "G\<turnstile>Norm s0 -[][\<succ>][]-> Norm s0"

  -- "cf. 15.6.4"
| Cons: "[| G\<turnstile>Norm s0 -e  \<succ> v -> s1;
            G\<turnstile>     s1 -es[\<succ>]vs-> s2 |] ==>
         G\<turnstile>Norm s0 -e#es[\<succ>]v#vs-> s2"


  -- "execution of statements"

  -- "cf. 14.1"
| XcptS:"G\<turnstile>(Some xc,s) -c-> (Some xc,s)"

  -- "cf. 14.5"
| Skip: "G\<turnstile>Norm s -Skip-> Norm s"

  -- "cf. 14.7"
| Expr: "[| G\<turnstile>Norm s0 -e\<succ>v-> s1 |] ==>
         G\<turnstile>Norm s0 -Expr e-> s1"

  -- "cf. 14.2"
| Comp: "[| G\<turnstile>Norm s0 -c1-> s1;
            G\<turnstile>     s1 -c2-> s2|] ==>
         G\<turnstile>Norm s0 -c1;; c2-> s2"

  -- "cf. 14.8.2"
| Cond: "[| G\<turnstile>Norm s0  -e\<succ>v-> s1;
            G\<turnstile> s1 -(if the_Bool v then c1 else c2)-> s2|] ==>
         G\<turnstile>Norm s0 -If(e) c1 Else c2-> s2"

  -- "cf. 14.10, 14.10.1"
| LoopF:"[| G\<turnstile>Norm s0 -e\<succ>v-> s1; \<not>the_Bool v |] ==>
         G\<turnstile>Norm s0 -While(e) c-> s1"
| LoopT:"[| G\<turnstile>Norm s0 -e\<succ>v-> s1;  the_Bool v;
      G\<turnstile>s1 -c-> s2; G\<turnstile>s2 -While(e) c-> s3 |] ==>
         G\<turnstile>Norm s0 -While(e) c-> s3"


lemmas eval_evals_exec_induct = eval_evals_exec.induct [split_format (complete)]

lemma NewCI: "[|new_Addr (heap s) = (a,x);  
       s' = c_hupd (heap s(a\<mapsto>(C,init_vars (fields (G,C))))) (x,s)|] ==>  
       G\<turnstile>Norm s -NewC C\<succ>Addr a-> s'"
apply simp
apply (rule eval_evals_exec.NewC)
apply auto
done

lemma eval_evals_exec_no_xcpt: 
 "!!s s'. (G\<turnstile>(x,s) -e \<succ>  v -> (x',s') --> x'=None --> x=None) \<and>  
          (G\<turnstile>(x,s) -es[\<succ>]vs-> (x',s') --> x'=None --> x=None) \<and>  
          (G\<turnstile>(x,s) -c       -> (x',s') --> x'=None --> x=None)"
apply(simp only: split_tupled_all)
apply(rule eval_evals_exec_induct)
apply(unfold c_hupd_def)
apply(simp_all)
done

lemma eval_no_xcpt: "G\<turnstile>(x,s) -e\<succ>v-> (None,s') ==> x=None"
apply (drule eval_evals_exec_no_xcpt [THEN conjunct1, THEN mp])
apply (fast)
done

lemma evals_no_xcpt: "G\<turnstile>(x,s) -e[\<succ>]v-> (None,s') ==> x=None"
apply (drule eval_evals_exec_no_xcpt [THEN conjunct2, THEN conjunct1, THEN mp])
apply (fast)
done

lemma exec_no_xcpt: "G \<turnstile> (x, s) -c-> (None, s')
\<Longrightarrow> x = None"
apply (drule eval_evals_exec_no_xcpt [THEN conjunct2 [THEN conjunct2], rule_format])
apply simp+
done


lemma eval_evals_exec_xcpt: 
"!!s s'. (G\<turnstile>(x,s) -e \<succ>  v -> (x',s') --> x=Some xc --> x'=Some xc \<and> s'=s) \<and>  
         (G\<turnstile>(x,s) -es[\<succ>]vs-> (x',s') --> x=Some xc --> x'=Some xc \<and> s'=s) \<and>  
         (G\<turnstile>(x,s) -c       -> (x',s') --> x=Some xc --> x'=Some xc \<and> s'=s)"
apply (simp only: split_tupled_all)
apply (rule eval_evals_exec_induct)
apply (unfold c_hupd_def)
apply (simp_all)
done

lemma eval_xcpt: "G\<turnstile>(Some xc,s) -e\<succ>v-> (x',s') ==> x'=Some xc \<and>  s'=s"
apply (drule eval_evals_exec_xcpt [THEN conjunct1, THEN mp])
apply (fast)
done

lemma exec_xcpt: "G\<turnstile>(Some xc,s) -s0-> (x',s') ==> x'=Some xc \<and>  s'=s"
apply (drule eval_evals_exec_xcpt [THEN conjunct2, THEN conjunct2, THEN mp])
apply (fast)
done


lemma eval_LAcc_code: "G\<turnstile>Norm (h, l) -LAcc v\<succ>the (l v)-> Norm (h, l)"
using LAcc[of G "(h, l)" v] by simp

lemma eval_Call_code:
  "[| G\<turnstile>Norm s0 -e\<succ>a'-> s1; a = the_Addr a';
      G\<turnstile>s1 -ps[\<succ>]pvs-> (x,(h,l)); dynT = fst (the (h a));
      (md,rT,pns,lvars,blk,res) = the (method (G,dynT) (mn,pTs));
      G\<turnstile>(np a' x,(h,(init_vars lvars)(pns[\<mapsto>]pvs)(This\<mapsto>a'))) -blk-> s3;
      G\<turnstile> s3 -res\<succ>v -> (x4,(h4, l4)) |] ==>
   G\<turnstile>Norm s0 -{C}e..mn({pTs}ps)\<succ>v-> (x4,(h4,l))"
using Call[of G s0 e a' s1 a ps pvs x h l dynT md rT pns lvars blk res mn pTs s3 v x4 "(h4, l4)" C]
by simp

lemmas [code_pred_intro] = XcptE NewC Cast Lit BinOp
lemmas [code_pred_intro LAcc_code] = eval_LAcc_code
lemmas [code_pred_intro] = LAss FAcc FAss
lemmas [code_pred_intro Call_code] = eval_Call_code
lemmas [code_pred_intro] = XcptEs Nil Cons XcptS Skip Expr Comp Cond LoopF 
lemmas [code_pred_intro LoopT_code] = LoopT

code_pred
  (modes: 
    eval: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool
  and
    evals: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool
  and
    exec: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool)
  eval
proof -
  case eval
  from eval.prems show thesis
  proof(cases (no_simp))
    case LAcc with LAcc_code show ?thesis by auto
  next
    case (Call a b c d e f g h i j k l m n o p q r s t u v s4)
    with Call_code show ?thesis
      by(cases "s4")(simp, (erule meta_allE meta_impE|rule conjI refl| assumption)+)
  qed(erule (3) that[OF refl]|assumption)+
next
  case evals
  from evals.prems show thesis
    by(cases (no_simp))(erule (3) that[OF refl]|assumption)+
next
  case exec
  from exec.prems show thesis
  proof(cases (no_simp))
    case LoopT thus ?thesis by(rule LoopT_code[OF refl])
  qed(erule (2) that[OF refl]|assumption)+
qed

end
