(*  Title:      HOL/MicroJava/Comp/TranslCompTp.thy
    Author:     Martin Strecker
*)

theory TranslCompTp
imports Index "../BV/JVMType"
begin

(**********************************************************************)

definition comb :: "['a \<Rightarrow> 'b list \<times> 'c, 'c \<Rightarrow> 'b list \<times> 'd, 'a] \<Rightarrow> 'b list \<times> 'd"
  (infixr \<open>\<box>\<close> 55)
where 
  "comb == (\<lambda> f1 f2 x0. let (xs1, x1) = f1 x0; 
                            (xs2, x2) = f2 x1 
                        in  (xs1 @ xs2, x2))"

definition comb_nil :: "'a \<Rightarrow> 'b list \<times> 'a" where
  "comb_nil a == ([], a)"

lemma comb_nil_left [simp]: "comb_nil \<box> f = f"
  by (simp add: comb_def comb_nil_def split_beta)

lemma comb_nil_right [simp]: "f \<box> comb_nil = f"
  by (simp add: comb_def comb_nil_def split_beta)

lemma comb_assoc [simp]: "(fa \<box> fb) \<box> fc = fa \<box> (fb \<box> fc)"
  by (simp add: comb_def split_beta)

lemma comb_inv:
  "(xs', x') = (f1 \<box> f2) x0 \<Longrightarrow>
  \<exists>xs1 x1 xs2 x2. (xs1, x1) = (f1 x0) \<and> (xs2, x2) = f2 x1 \<and> xs'= xs1 @ xs2 \<and> x'=x2"
  by (case_tac "f1 x0") (simp add: comb_def split_beta)

(**********************************************************************)

abbreviation (input)
  mt_of :: "method_type \<times> state_type \<Rightarrow> method_type"
  where "mt_of == fst"

abbreviation (input)
  sttp_of :: "method_type \<times> state_type \<Rightarrow> state_type"
  where "sttp_of == snd"

definition nochangeST :: "state_type \<Rightarrow> method_type \<times> state_type" where
  "nochangeST sttp == ([Some sttp], sttp)"

definition pushST :: "[ty list, state_type] \<Rightarrow> method_type \<times> state_type" where
  "pushST tps == (\<lambda> (ST, LT). ([Some (ST, LT)], (tps @ ST, LT)))"

definition dupST :: "state_type \<Rightarrow> method_type \<times> state_type" where
  "dupST == (\<lambda> (ST, LT). ([Some (ST, LT)], (hd ST # ST, LT)))"

definition dup_x1ST :: "state_type \<Rightarrow> method_type \<times> state_type" where
  "dup_x1ST == (\<lambda> (ST, LT). ([Some (ST, LT)], 
                             (hd ST # hd (tl ST) # hd ST # (tl (tl ST)), LT)))"

definition popST :: "[nat, state_type] \<Rightarrow> method_type \<times> state_type" where
  "popST n == (\<lambda> (ST, LT). ([Some (ST, LT)], (drop n ST, LT)))"

definition replST :: "[nat, ty, state_type] \<Rightarrow> method_type \<times> state_type" where
  "replST n tp == (\<lambda> (ST, LT). ([Some (ST, LT)], (tp # (drop n ST), LT)))"

definition storeST :: "[nat, ty, state_type] \<Rightarrow> method_type \<times> state_type" where
  "storeST i tp == (\<lambda> (ST, LT). ([Some (ST, LT)], (tl ST, LT [i:= OK tp])))"


(* Expressions *)

primrec compTpExpr :: "java_mb \<Rightarrow> java_mb prog \<Rightarrow> expr \<Rightarrow>
    state_type \<Rightarrow> method_type \<times> state_type"
  and compTpExprs :: "java_mb \<Rightarrow> java_mb prog \<Rightarrow> expr list \<Rightarrow>
    state_type \<Rightarrow> method_type \<times> state_type"
where
  "compTpExpr jmb G (NewC c) = pushST [Class c]"
| "compTpExpr jmb G (Cast c e) = (compTpExpr jmb G e) \<box> (replST 1 (Class c))"
| "compTpExpr jmb G (Lit val) = pushST [the (typeof (\<lambda>v. None) val)]"
| "compTpExpr jmb G (BinOp bo e1 e2) =
     (compTpExpr jmb G e1) \<box> (compTpExpr jmb G e2) \<box> 
     (case bo of 
       Eq => popST 2 \<box> pushST [PrimT Boolean] \<box> popST 1 \<box> pushST [PrimT Boolean]
     | Add => replST 2 (PrimT Integer))"
| "compTpExpr jmb G (LAcc vn) = (\<lambda> (ST, LT). 
      pushST [ok_val (LT ! (index jmb vn))] (ST, LT))"
| "compTpExpr jmb G (vn::=e) = 
      (compTpExpr jmb G e) \<box> dupST \<box> (popST 1)"
| "compTpExpr jmb G ( {cn}e..fn ) = 
      (compTpExpr jmb G e) \<box> replST 1 (snd (the (field (G,cn) fn)))"
| "compTpExpr jmb G (FAss cn e1 fn e2 ) = 
      (compTpExpr jmb G e1) \<box> (compTpExpr jmb G e2) \<box> dup_x1ST \<box> (popST 2)"
| "compTpExpr jmb G ({C}a..mn({fpTs}ps)) =
       (compTpExpr jmb G a) \<box> (compTpExprs jmb G ps) \<box> 
       (replST ((length ps) + 1) (method_rT (the (method (G,C) (mn,fpTs)))))"
| "compTpExprs jmb G [] = comb_nil"
| "compTpExprs jmb G (e#es) = (compTpExpr jmb G e) \<box> (compTpExprs jmb G es)"


(* Statements *)
primrec compTpStmt :: "java_mb \<Rightarrow> java_mb prog \<Rightarrow> stmt \<Rightarrow> 
    state_type \<Rightarrow> method_type \<times> state_type"
where
  "compTpStmt jmb G Skip = comb_nil"
| "compTpStmt jmb G (Expr e) =  (compTpExpr jmb G e) \<box> popST 1"
| "compTpStmt jmb G (c1;; c2) = (compTpStmt jmb G c1) \<box> (compTpStmt jmb G c2)"
| "compTpStmt jmb G (If(e) c1 Else c2) = 
      (pushST [PrimT Boolean]) \<box> (compTpExpr jmb G e) \<box> popST 2 \<box>
      (compTpStmt jmb G c1) \<box> nochangeST \<box> (compTpStmt jmb G c2)"
| "compTpStmt jmb G (While(e) c) = 
      (pushST [PrimT Boolean]) \<box> (compTpExpr jmb G e) \<box> popST 2 \<box>
      (compTpStmt jmb G c) \<box> nochangeST"

definition compTpInit :: "java_mb \<Rightarrow> (vname * ty)
                   \<Rightarrow> state_type \<Rightarrow> method_type \<times> state_type" where
  "compTpInit jmb == (\<lambda> (vn,ty). (pushST [ty]) \<box>  (storeST (index jmb vn) ty))"

primrec compTpInitLvars :: "[java_mb, (vname \<times> ty) list] \<Rightarrow>
    state_type \<Rightarrow> method_type \<times> state_type"
where
  "compTpInitLvars jmb [] = comb_nil"
| "compTpInitLvars jmb (lv#lvars) = (compTpInit jmb lv) \<box> (compTpInitLvars jmb lvars)"

definition start_ST :: "opstack_type" where
  "start_ST == []"

definition start_LT :: "cname \<Rightarrow> ty list \<Rightarrow> nat \<Rightarrow> locvars_type" where
  "start_LT C pTs n ==  (OK (Class C))#((map OK pTs))@(replicate n Err)"

definition compTpMethod  :: "[java_mb prog, cname, java_mb mdecl] \<Rightarrow> method_type" where
  "compTpMethod G C == \<lambda> ((mn,pTs),rT, jmb). 
                         let (pns,lvars,blk,res) = jmb
                         in (mt_of
                            ((compTpInitLvars jmb lvars \<box> 
                              compTpStmt jmb G blk \<box> 
                              compTpExpr jmb G res \<box>
                              nochangeST)
                                (start_ST, start_LT C pTs (length lvars))))"

definition compTp :: "java_mb prog => prog_type" where
  "compTp G C sig == let (D, rT, jmb) = (the (method (G, C) sig))
                      in compTpMethod G C (sig, rT, jmb)"



(**********************************************************************)
  (* Computing the maximum stack size from the method_type *)

definition ssize_sto :: "(state_type option) \<Rightarrow> nat" where
  "ssize_sto sto ==  case sto of None \<Rightarrow> 0 | (Some (ST, LT)) \<Rightarrow> length ST"

definition max_of_list :: "nat list \<Rightarrow> nat" where
  "max_of_list xs == foldr max xs 0"

definition max_ssize :: "method_type \<Rightarrow> nat" where
  "max_ssize mt == max_of_list (map ssize_sto mt)"

end
