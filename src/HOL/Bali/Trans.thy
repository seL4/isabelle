(*  Title:      HOL/Bali/Trans.thy
    Author:     David von Oheimb and Norbert Schirmer

Operational transition (small-step) semantics of the 
execution of Java expressions and statements

PRELIMINARY!!!!!!!!
*)

theory Trans imports Evaln begin

definition
  groundVar :: "var \<Rightarrow> bool" where
  "groundVar v \<longleftrightarrow> (case v of
                     LVar ln \<Rightarrow> True
                   | {accC,statDeclC,stat}e..fn \<Rightarrow> \<exists> a. e=Lit a
                   | e1.[e2] \<Rightarrow> \<exists> a i. e1= Lit a \<and> e2 = Lit i
                   | InsInitV c v \<Rightarrow> False)"

lemma groundVar_cases:
  assumes ground: "groundVar v"
  obtains (LVar) ln where "v=LVar ln"
    | (FVar) accC statDeclC stat a fn where "v={accC,statDeclC,stat}(Lit a)..fn"
    | (AVar) a i where "v=(Lit a).[Lit i]"
  using ground LVar FVar AVar
  apply (cases v)
  apply (simp add: groundVar_def)
  apply (simp add: groundVar_def,blast)
  apply (simp add: groundVar_def,blast)
  apply (simp add: groundVar_def)
  done

definition
  groundExprs :: "expr list \<Rightarrow> bool"
  where "groundExprs es \<longleftrightarrow> (\<forall>e \<in> set es. \<exists>v. e = Lit v)"
  
primrec the_val:: "expr \<Rightarrow> val"
  where "the_val (Lit v) = v"

primrec the_var:: "prog \<Rightarrow> state \<Rightarrow> var \<Rightarrow> (vvar \<times> state)" where
  "the_var G s (LVar ln) = (lvar ln (store s),s)"
| the_var_FVar_def: "the_var G s ({accC,statDeclC,stat}a..fn) =fvar statDeclC stat fn (the_val a) s"
| the_var_AVar_def: "the_var G s(a.[i])                       =avar G (the_val i) (the_val a) s"

lemma the_var_FVar_simp[simp]:
"the_var G s ({accC,statDeclC,stat}(Lit a)..fn) = fvar statDeclC stat fn a s"
by (simp)
declare the_var_FVar_def [simp del]

lemma the_var_AVar_simp:
"the_var G s ((Lit a).[Lit i]) = avar G i a s"
by (simp)
declare the_var_AVar_def [simp del]

abbreviation
  Ref :: "loc \<Rightarrow> expr"
  where "Ref a == Lit (Addr a)"

abbreviation
  SKIP :: "expr"
  where "SKIP == Lit Unit"

inductive
  step :: "[prog,term \<times> state,term \<times> state] \<Rightarrow> bool" ("_\<turnstile>_ \<mapsto>1 _"[61,82,82] 81)
  for G :: prog
where

(* evaluation of expression *)
  (* cf. 15.5 *)
  Abrupt:       "\<lbrakk>\<forall>v. t \<noteq> \<langle>Lit v\<rangle>;
                  \<forall> t. t \<noteq> \<langle>l\<bullet> Skip\<rangle>;
                  \<forall> C vn c.  t \<noteq> \<langle>Try Skip Catch(C vn) c\<rangle>;
                  \<forall> x c. t \<noteq> \<langle>Skip Finally c\<rangle> \<and> xc \<noteq> Xcpt x;
                  \<forall> a c. t \<noteq> \<langle>FinA a c\<rangle>\<rbrakk> 
                \<Longrightarrow> 
                  G\<turnstile>(t,Some xc,s) \<mapsto>1 (\<langle>Lit undefined\<rangle>,Some xc,s)"

| InsInitE: "\<lbrakk>G\<turnstile>(\<langle>c\<rangle>,Norm s) \<mapsto>1 (\<langle>c'\<rangle>, s')\<rbrakk>
             \<Longrightarrow> 
             G\<turnstile>(\<langle>InsInitE c e\<rangle>,Norm s) \<mapsto>1 (\<langle>InsInitE c' e\<rangle>, s')"

(* SeqE: "G\<turnstile>(\<langle>Seq Skip e\<rangle>,Norm s) \<mapsto>1 (\<langle>e\<rangle>, Norm s)" *)
(* Specialised rules to evaluate: 
   InsInitE Skip (NewC C), InisInitE Skip (NewA T[e]) *)
 
  (* cf. 15.8.1 *)
| NewC: "G\<turnstile>(\<langle>NewC C\<rangle>,Norm s) \<mapsto>1 (\<langle>InsInitE (Init C) (NewC C)\<rangle>, Norm s)"
| NewCInited: "\<lbrakk>G\<turnstile> Norm s \<midarrow>halloc (CInst C)\<succ>a\<rightarrow> s'\<rbrakk> 
               \<Longrightarrow> 
               G\<turnstile>(\<langle>InsInitE Skip (NewC C)\<rangle>,Norm s) \<mapsto>1 (\<langle>Ref a\<rangle>, s')"



(* Alternative when rule SeqE is present 
NewCInited: "\<lbrakk>inited C (globs s); 
              G\<turnstile> Norm s \<midarrow>halloc (CInst C)\<succ>a\<rightarrow> s'\<rbrakk> 
             \<Longrightarrow> 
              G\<turnstile>(\<langle>NewC C\<rangle>,Norm s) \<mapsto>1 (\<langle>Ref a\<rangle>, s')"

NewC:
     "\<lbrakk>\<not> inited C (globs s)\<rbrakk> 
     \<Longrightarrow> 
      G\<turnstile>(\<langle>NewC C\<rangle>,Norm s) \<mapsto>1 (\<langle>Seq (Init C) (NewC C)\<rangle>, Norm s)"

*)
  (* cf. 15.9.1 *)
| NewA: 
   "G\<turnstile>(\<langle>New T[e]\<rangle>,Norm s) \<mapsto>1 (\<langle>InsInitE (init_comp_ty T) (New T[e])\<rangle>,Norm s)"
| InsInitNewAIdx: 
   "\<lbrakk>G\<turnstile>(\<langle>e\<rangle>,Norm s) \<mapsto>1 (\<langle>e'\<rangle>, s')\<rbrakk>
    \<Longrightarrow>  
    G\<turnstile>(\<langle>InsInitE Skip (New T[e])\<rangle>,Norm s) \<mapsto>1 (\<langle>InsInitE Skip (New T[e'])\<rangle>,s')"
| InsInitNewA: 
   "\<lbrakk>G\<turnstile>abupd (check_neg i) (Norm s) \<midarrow>halloc (Arr T (the_Intg i))\<succ>a\<rightarrow> s' \<rbrakk>
    \<Longrightarrow>
    G\<turnstile>(\<langle>InsInitE Skip (New T[Lit i])\<rangle>,Norm s) \<mapsto>1 (\<langle>Ref a\<rangle>,s')"
 
  (* cf. 15.15 *)
| CastE:
   "\<lbrakk>G\<turnstile>(\<langle>e\<rangle>,Norm s) \<mapsto>1 (\<langle>e'\<rangle>,s')\<rbrakk> 
    \<Longrightarrow>
    G\<turnstile>(\<langle>Cast T e\<rangle>,None,s) \<mapsto>1 (\<langle>Cast T e'\<rangle>,s')" 
| Cast:
   "\<lbrakk>s' = abupd (raise_if (\<not>G,s\<turnstile>v fits T)  ClassCast) (Norm s)\<rbrakk> 
    \<Longrightarrow> 
    G\<turnstile>(\<langle>Cast T (Lit v)\<rangle>,Norm s) \<mapsto>1 (\<langle>Lit v\<rangle>,s')"
  (* can be written without abupd, since we know Norm s *)


| InstE: "\<lbrakk>G\<turnstile>(\<langle>e\<rangle>,Norm s) \<mapsto>1 (\<langle>e'::expr\<rangle>,s')\<rbrakk> 
        \<Longrightarrow> 
        G\<turnstile>(\<langle>e InstOf T\<rangle>,Norm s) \<mapsto>1 (\<langle>e'\<rangle>,s')" 
| Inst:  "\<lbrakk>b = (v\<noteq>Null \<and> G,s\<turnstile>v fits RefT T)\<rbrakk> 
          \<Longrightarrow> 
          G\<turnstile>(\<langle>(Lit v) InstOf T\<rangle>,Norm s) \<mapsto>1 (\<langle>Lit (Bool b)\<rangle>,s')"

  (* cf. 15.7.1 *)
(*Lit                           "G\<turnstile>(Lit v,None,s) \<mapsto>1 (Lit v,None,s)"*)

| UnOpE:  "\<lbrakk>G\<turnstile>(\<langle>e\<rangle>,Norm s) \<mapsto>1 (\<langle>e'\<rangle>,s') \<rbrakk>
           \<Longrightarrow> 
           G\<turnstile>(\<langle>UnOp unop e\<rangle>,Norm s) \<mapsto>1 (\<langle>UnOp unop e'\<rangle>,s')"
| UnOp:   "G\<turnstile>(\<langle>UnOp unop (Lit v)\<rangle>,Norm s) \<mapsto>1 (\<langle>Lit (eval_unop unop v)\<rangle>,Norm s)"

| BinOpE1:  "\<lbrakk>G\<turnstile>(\<langle>e1\<rangle>,Norm s) \<mapsto>1 (\<langle>e1'\<rangle>,s') \<rbrakk>
             \<Longrightarrow> 
             G\<turnstile>(\<langle>BinOp binop e1 e2\<rangle>,Norm s) \<mapsto>1 (\<langle>BinOp binop e1' e2\<rangle>,s')"
| BinOpE2:  "\<lbrakk>need_second_arg binop v1; G\<turnstile>(\<langle>e2\<rangle>,Norm s) \<mapsto>1 (\<langle>e2'\<rangle>,s') \<rbrakk>
             \<Longrightarrow> 
             G\<turnstile>(\<langle>BinOp binop (Lit v1) e2\<rangle>,Norm s) 
              \<mapsto>1 (\<langle>BinOp binop (Lit v1) e2'\<rangle>,s')"
| BinOpTerm:  "\<lbrakk>\<not> need_second_arg binop v1\<rbrakk>
               \<Longrightarrow> 
               G\<turnstile>(\<langle>BinOp binop (Lit v1) e2\<rangle>,Norm s) 
                \<mapsto>1 (\<langle>Lit v1\<rangle>,Norm s)"
| BinOp:    "G\<turnstile>(\<langle>BinOp binop (Lit v1) (Lit v2)\<rangle>,Norm s) 
              \<mapsto>1 (\<langle>Lit (eval_binop binop v1 v2)\<rangle>,Norm s)"
(* Maybe its more convenient to add: need_second_arg as precondition to BinOp 
   to make the choice between BinOpTerm and BinOp deterministic *)
   
| Super: "G\<turnstile>(\<langle>Super\<rangle>,Norm s) \<mapsto>1 (\<langle>Lit (val_this s)\<rangle>,Norm s)"

| AccVA: "\<lbrakk>G\<turnstile>(\<langle>va\<rangle>,Norm s) \<mapsto>1 (\<langle>va'\<rangle>,s') \<rbrakk>
          \<Longrightarrow> 
          G\<turnstile>(\<langle>Acc va\<rangle>,Norm s) \<mapsto>1 (\<langle>Acc va'\<rangle>,s')"
| Acc:  "\<lbrakk>groundVar va; ((v,vf),s') = the_var G (Norm s) va\<rbrakk>
         \<Longrightarrow>  
         G\<turnstile>(\<langle>Acc va\<rangle>,Norm s) \<mapsto>1 (\<langle>Lit v\<rangle>,s')"

(*
AccLVar: "G\<turnstile>(\<langle>Acc (LVar vn)\<rangle>,Norm s) \<mapsto>1 (\<langle>Lit (fst (lvar vn s))\<rangle>,Norm s)"
AccFVar: "\<lbrakk>((v,vf),s') = fvar statDeclC stat fn a (Norm s)\<rbrakk>
          \<Longrightarrow>  
          G\<turnstile>(\<langle>Acc ({accC,statDeclC,stat}(Lit a)..fn)\<rangle>,Norm s) 
           \<mapsto>1 (\<langle>Lit v\<rangle>,s')"
AccAVar: "\<lbrakk>((v,vf),s') = avar G i a (Norm s)\<rbrakk>
          \<Longrightarrow>  
          G\<turnstile>(\<langle>Acc ((Lit a).[Lit i])\<rangle>,Norm s) \<mapsto>1 (\<langle>Lit v\<rangle>,s')"
*) 
| AssVA:  "\<lbrakk>G\<turnstile>(\<langle>va\<rangle>,Norm s) \<mapsto>1 (\<langle>va'\<rangle>,s')\<rbrakk> 
           \<Longrightarrow> 
           G\<turnstile>(\<langle>va:=e\<rangle>,Norm s) \<mapsto>1 (\<langle>va':=e\<rangle>,s')"
| AssE:   "\<lbrakk>groundVar va; G\<turnstile>(\<langle>e\<rangle>,Norm s) \<mapsto>1 (\<langle>e'\<rangle>,s')\<rbrakk> 
           \<Longrightarrow> 
           G\<turnstile>(\<langle>va:=e\<rangle>,Norm s) \<mapsto>1 (\<langle>va:=e'\<rangle>,s')"
| Ass:    "\<lbrakk>groundVar va; ((w,f),s') = the_var G (Norm s) va\<rbrakk> 
           \<Longrightarrow> 
           G\<turnstile>(\<langle>va:=(Lit v)\<rangle>,Norm s) \<mapsto>1 (\<langle>Lit v\<rangle>,assign f v s')"

| CondC: "\<lbrakk>G\<turnstile>(\<langle>e0\<rangle>,Norm s) \<mapsto>1 (\<langle>e0'\<rangle>,s')\<rbrakk> 
          \<Longrightarrow> 
          G\<turnstile>(\<langle>e0? e1:e2\<rangle>,Norm s) \<mapsto>1 (\<langle>e0'? e1:e2\<rangle>,s')"
| Cond:  "G\<turnstile>(\<langle>Lit b? e1:e2\<rangle>,Norm s) \<mapsto>1 (\<langle>if the_Bool b then e1 else e2\<rangle>,Norm s)"


| CallTarget: "\<lbrakk>G\<turnstile>(\<langle>e\<rangle>,Norm s) \<mapsto>1 (\<langle>e'\<rangle>,s')\<rbrakk> 
               \<Longrightarrow>
               G\<turnstile>(\<langle>{accC,statT,mode}e\<cdot>mn({pTs}args)\<rangle>,Norm s) 
                \<mapsto>1 (\<langle>{accC,statT,mode}e'\<cdot>mn({pTs}args)\<rangle>,s')"
| CallArgs:   "\<lbrakk>G\<turnstile>(\<langle>args\<rangle>,Norm s) \<mapsto>1 (\<langle>args'\<rangle>,s')\<rbrakk> 
               \<Longrightarrow>
               G\<turnstile>(\<langle>{accC,statT,mode}Lit a\<cdot>mn({pTs}args)\<rangle>,Norm s) 
                \<mapsto>1 (\<langle>{accC,statT,mode}Lit a\<cdot>mn({pTs}args')\<rangle>,s')"
| Call:       "\<lbrakk>groundExprs args; vs = map the_val args;
                D = invocation_declclass G mode s a statT \<lparr>name=mn,parTs=pTs\<rparr>;
                s'=init_lvars G D \<lparr>name=mn,parTs=pTs\<rparr> mode a' vs (Norm s)\<rbrakk> 
               \<Longrightarrow> 
               G\<turnstile>(\<langle>{accC,statT,mode}Lit a\<cdot>mn({pTs}args)\<rangle>,Norm s) 
                \<mapsto>1 (\<langle>Callee (locals s) (Methd D \<lparr>name=mn,parTs=pTs\<rparr>)\<rangle>,s')"
           
| Callee:     "\<lbrakk>G\<turnstile>(\<langle>e\<rangle>,Norm s) \<mapsto>1 (\<langle>e'::expr\<rangle>,s')\<rbrakk>
               \<Longrightarrow> 
               G\<turnstile>(\<langle>Callee lcls_caller e\<rangle>,Norm s) \<mapsto>1 (\<langle>e'\<rangle>,s')"

| CalleeRet:   "G\<turnstile>(\<langle>Callee lcls_caller (Lit v)\<rangle>,Norm s) 
                 \<mapsto>1 (\<langle>Lit v\<rangle>,(set_lvars lcls_caller (Norm s)))"

| Methd: "G\<turnstile>(\<langle>Methd D sig\<rangle>,Norm s) \<mapsto>1 (\<langle>body G D sig\<rangle>,Norm s)"

| Body: "G\<turnstile>(\<langle>Body D c\<rangle>,Norm s) \<mapsto>1 (\<langle>InsInitE (Init D) (Body D c)\<rangle>,Norm s)"

| InsInitBody: 
    "\<lbrakk>G\<turnstile>(\<langle>c\<rangle>,Norm s) \<mapsto>1 (\<langle>c'\<rangle>,s')\<rbrakk>
     \<Longrightarrow> 
     G\<turnstile>(\<langle>InsInitE Skip (Body D c)\<rangle>,Norm s) \<mapsto>1(\<langle>InsInitE Skip (Body D c')\<rangle>,s')"
| InsInitBodyRet: 
     "G\<turnstile>(\<langle>InsInitE Skip (Body D Skip)\<rangle>,Norm s)
       \<mapsto>1 (\<langle>Lit (the ((locals s) Result))\<rangle>,abupd (absorb Ret) (Norm s))"

(*   LVar: "G\<turnstile>(LVar vn,Norm s)" is already evaluated *)
  
| FVar: "\<lbrakk>\<not> inited statDeclC (globs s)\<rbrakk>
         \<Longrightarrow> 
         G\<turnstile>(\<langle>{accC,statDeclC,stat}e..fn\<rangle>,Norm s) 
          \<mapsto>1 (\<langle>InsInitV (Init statDeclC) ({accC,statDeclC,stat}e..fn)\<rangle>,Norm s)"
| InsInitFVarE:
      "\<lbrakk>G\<turnstile>(\<langle>e\<rangle>,Norm s) \<mapsto>1 (\<langle>e'\<rangle>,s')\<rbrakk>
       \<Longrightarrow>
       G\<turnstile>(\<langle>InsInitV Skip ({accC,statDeclC,stat}e..fn)\<rangle>,Norm s) 
        \<mapsto>1 (\<langle>InsInitV Skip ({accC,statDeclC,stat}e'..fn)\<rangle>,s')"
| InsInitFVar:
      "G\<turnstile>(\<langle>InsInitV Skip ({accC,statDeclC,stat}Lit a..fn)\<rangle>,Norm s) 
        \<mapsto>1 (\<langle>{accC,statDeclC,stat}Lit a..fn\<rangle>,Norm s)"
--  {* Notice, that we do not have literal values for @{text vars}. 
The rules for accessing variables (@{text Acc}) and assigning to variables 
(@{text Ass}), test this with the predicate @{text groundVar}.  After 
initialisation is done and the @{text FVar} is evaluated, we can't just 
throw away the @{text InsInitFVar} term and return a literal value, as in the 
cases of @{text New}  or @{text NewC}. Instead we just return the evaluated 
@{text FVar} and test for initialisation in the rule @{text FVar}. 
*}


| AVarE1: "\<lbrakk>G\<turnstile>(\<langle>e1\<rangle>,Norm s) \<mapsto>1 (\<langle>e1'\<rangle>,s')\<rbrakk> 
           \<Longrightarrow> 
           G\<turnstile>(\<langle>e1.[e2]\<rangle>,Norm s) \<mapsto>1 (\<langle>e1'.[e2]\<rangle>,s')"

| AVarE2: "G\<turnstile>(\<langle>e2\<rangle>,Norm s) \<mapsto>1 (\<langle>e2'\<rangle>,s') 
           \<Longrightarrow> 
           G\<turnstile>(\<langle>Lit a.[e2]\<rangle>,Norm s) \<mapsto>1 (\<langle>Lit a.[e2']\<rangle>,s')"

(* AVar: \<langle>(Lit a).[Lit i]\<rangle> is fully evaluated *)

(* evaluation of expression lists *)

  -- {* @{text Nil}  is fully evaluated *}

| ConsHd: "\<lbrakk>G\<turnstile>(\<langle>e::expr\<rangle>,Norm s) \<mapsto>1 (\<langle>e'::expr\<rangle>,s')\<rbrakk> 
           \<Longrightarrow>
           G\<turnstile>(\<langle>e#es\<rangle>,Norm s) \<mapsto>1 (\<langle>e'#es\<rangle>,s')"
  
| ConsTl: "\<lbrakk>G\<turnstile>(\<langle>es\<rangle>,Norm s) \<mapsto>1 (\<langle>es'\<rangle>,s')\<rbrakk> 
           \<Longrightarrow>
           G\<turnstile>(\<langle>(Lit v)#es\<rangle>,Norm s) \<mapsto>1 (\<langle>(Lit v)#es'\<rangle>,s')"

(* execution of statements *)

  (* cf. 14.5 *)
| Skip: "G\<turnstile>(\<langle>Skip\<rangle>,Norm s) \<mapsto>1 (\<langle>SKIP\<rangle>,Norm s)"

| ExprE: "\<lbrakk>G\<turnstile>(\<langle>e\<rangle>,Norm s) \<mapsto>1 (\<langle>e'\<rangle>,s')\<rbrakk> 
          \<Longrightarrow> 
          G\<turnstile>(\<langle>Expr e\<rangle>,Norm s) \<mapsto>1 (\<langle>Expr e'\<rangle>,s')"
| Expr:  "G\<turnstile>(\<langle>Expr (Lit v)\<rangle>,Norm s) \<mapsto>1 (\<langle>Skip\<rangle>,Norm s)"


| LabC: "\<lbrakk>G\<turnstile>(\<langle>c\<rangle>,Norm s) \<mapsto>1 (\<langle>c'\<rangle>,s')\<rbrakk> 
         \<Longrightarrow>  
         G\<turnstile>(\<langle>l\<bullet> c\<rangle>,Norm s) \<mapsto>1 (\<langle>l\<bullet> c'\<rangle>,s')"
| Lab:  "G\<turnstile>(\<langle>l\<bullet> Skip\<rangle>,s) \<mapsto>1 (\<langle>Skip\<rangle>, abupd (absorb l) s)"

  (* cf. 14.2 *)
| CompC1: "\<lbrakk>G\<turnstile>(\<langle>c1\<rangle>,Norm s) \<mapsto>1 (\<langle>c1'\<rangle>,s')\<rbrakk> 
           \<Longrightarrow> 
           G\<turnstile>(\<langle>c1;; c2\<rangle>,Norm s) \<mapsto>1 (\<langle>c1';; c2\<rangle>,s')"

| Comp:   "G\<turnstile>(\<langle>Skip;; c2\<rangle>,Norm s) \<mapsto>1 (\<langle>c2\<rangle>,Norm s)"

  (* cf. 14.8.2 *)
| IfE: "\<lbrakk>G\<turnstile>(\<langle>e\<rangle> ,Norm s) \<mapsto>1 (\<langle>e'\<rangle>,s')\<rbrakk> 
        \<Longrightarrow>
        G\<turnstile>(\<langle>If(e) s1 Else s2\<rangle>,Norm s) \<mapsto>1 (\<langle>If(e') s1 Else s2\<rangle>,s')"
| If:  "G\<turnstile>(\<langle>If(Lit v) s1 Else s2\<rangle>,Norm s) 
         \<mapsto>1 (\<langle>if the_Bool v then s1 else s2\<rangle>,Norm s)"

  (* cf. 14.10, 14.10.1 *)
| Loop: "G\<turnstile>(\<langle>l\<bullet> While(e) c\<rangle>,Norm s) 
          \<mapsto>1 (\<langle>If(e) (Cont l\<bullet>c;; l\<bullet> While(e) c) Else Skip\<rangle>,Norm s)"

| Jmp: "G\<turnstile>(\<langle>Jmp j\<rangle>,Norm s) \<mapsto>1 (\<langle>Skip\<rangle>,(Some (Jump j), s))"

| ThrowE: "\<lbrakk>G\<turnstile>(\<langle>e\<rangle>,Norm s) \<mapsto>1 (\<langle>e'\<rangle>,s')\<rbrakk> 
           \<Longrightarrow>
           G\<turnstile>(\<langle>Throw e\<rangle>,Norm s) \<mapsto>1 (\<langle>Throw e'\<rangle>,s')"
| Throw:  "G\<turnstile>(\<langle>Throw (Lit a)\<rangle>,Norm s) \<mapsto>1 (\<langle>Skip\<rangle>,abupd (throw a) (Norm s))"

| TryC1: "\<lbrakk>G\<turnstile>(\<langle>c1\<rangle>,Norm s) \<mapsto>1 (\<langle>c1'\<rangle>,s')\<rbrakk> 
          \<Longrightarrow>
          G\<turnstile>(\<langle>Try c1 Catch(C vn) c2\<rangle>, Norm s) \<mapsto>1 (\<langle>Try c1' Catch(C vn) c2\<rangle>,s')"
| Try:   "\<lbrakk>G\<turnstile>s \<midarrow>sxalloc\<rightarrow> s'\<rbrakk>
          \<Longrightarrow>
          G\<turnstile>(\<langle>Try Skip Catch(C vn) c2\<rangle>, s) 
           \<mapsto>1 (if G,s'\<turnstile>catch C then (\<langle>c2\<rangle>,new_xcpt_var vn s')
                                else (\<langle>Skip\<rangle>,s'))"

| FinC1: "\<lbrakk>G\<turnstile>(\<langle>c1\<rangle>,Norm s) \<mapsto>1 (\<langle>c1'\<rangle>,s')\<rbrakk> 
          \<Longrightarrow>
          G\<turnstile>(\<langle>c1 Finally c2\<rangle>,Norm s) \<mapsto>1 (\<langle>c1' Finally c2\<rangle>,s')"

| Fin:    "G\<turnstile>(\<langle>Skip Finally c2\<rangle>,(a,s)) \<mapsto>1 (\<langle>FinA a c2\<rangle>,Norm s)"

| FinAC: "\<lbrakk>G\<turnstile>(\<langle>c\<rangle>,s) \<mapsto>1 (\<langle>c'\<rangle>,s')\<rbrakk>
          \<Longrightarrow>
          G\<turnstile>(\<langle>FinA a c\<rangle>,s) \<mapsto>1 (\<langle>FinA a c'\<rangle>,s')"
| FinA: "G\<turnstile>(\<langle>FinA a Skip\<rangle>,s) \<mapsto>1 (\<langle>Skip\<rangle>,abupd (abrupt_if (a\<noteq>None) a) s)"


| Init1: "\<lbrakk>inited C (globs s)\<rbrakk> 
          \<Longrightarrow> 
          G\<turnstile>(\<langle>Init C\<rangle>,Norm s) \<mapsto>1 (\<langle>Skip\<rangle>,Norm s)"
| Init: "\<lbrakk>the (class G C)=c; \<not> inited C (globs s)\<rbrakk>  
         \<Longrightarrow> 
         G\<turnstile>(\<langle>Init C\<rangle>,Norm s) 
          \<mapsto>1 (\<langle>(if C = Object then Skip else (Init (super c)));;
                Expr (Callee (locals s) (InsInitE (init c) SKIP))\<rangle>
               ,Norm (init_class_obj G C s))"
-- {* @{text InsInitE} is just used as trick to embed the statement 
@{text "init c"} into an expression*} 
| InsInitESKIP:
    "G\<turnstile>(\<langle>InsInitE Skip SKIP\<rangle>,Norm s) \<mapsto>1 (\<langle>SKIP\<rangle>,Norm s)"

abbreviation
  stepn:: "[prog, term \<times> state,nat,term \<times> state] \<Rightarrow> bool" ("_\<turnstile>_ \<mapsto>_ _"[61,82,82] 81)
  where "G\<turnstile>p \<mapsto>n p' \<equiv> (p,p') \<in> {(x, y). step G x y}^^n"

abbreviation
  steptr:: "[prog,term \<times> state,term \<times> state] \<Rightarrow> bool" ("_\<turnstile>_ \<mapsto>* _"[61,82,82] 81)
  where "G\<turnstile>p \<mapsto>* p' \<equiv> (p,p') \<in> {(x, y). step G x y}\<^sup>*"
         
(* Equivalenzen:
  Bigstep zu Smallstep komplett.
  Smallstep zu Bigstep, nur wenn nicht die Ausdrücke Callee, FinA ,\<dots>
*)

(*
lemma imp_eval_trans:
  assumes eval: "G\<turnstile>s0 \<midarrow>t\<succ>\<rightarrow> (v,s1)" 
    shows trans: "G\<turnstile>(t,s0) \<mapsto>* (\<langle>Lit v\<rangle>,s1)"
*)
(* Jetzt muss man bei trans natürlich wieder unterscheiden: Stmt, Expr, Var!
   Sowas blödes:
   Am besten den Terminus ground auf Var,Stmt,Expr hochziehen und dann
   the_vals definieren\<dots>
  G\<turnstile>(t,s0) \<mapsto>* (t',s1) \<and> the_vals t' = v
*)


end