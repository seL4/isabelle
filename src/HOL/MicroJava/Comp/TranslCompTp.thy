(*  Title:      HOL/MicroJava/Comp/TranslCompTp.thy
    ID:         $Id$
    Author:     Martin Strecker
*)

theory TranslCompTp =  JVMType + Index:


(**********************************************************************)


constdefs
  comb :: "['a \<Rightarrow> 'b list \<times> 'c, 'c \<Rightarrow> 'b list \<times> 'd, 'a] \<Rightarrow> 'b list \<times> 'd" 
  "comb == (\<lambda> f1 f2 x0. let (xs1, x1) = f1 x0; 
                            (xs2, x2) = f2 x1 
                        in  (xs1 @ xs2, x2))"
  comb_nil :: "'a \<Rightarrow> 'b list \<times> 'a"
  "comb_nil a == ([], a)"

syntax (xsymbols)
  "comb" :: "['a \<Rightarrow> 'b list \<times> 'c, 'c \<Rightarrow> 'b list \<times> 'd, 'a] \<Rightarrow> 'b list \<times> 'd"    
            (infixr "\<box>" 55)

lemma comb_nil_left [simp]: "comb_nil \<box> f = f"
by (simp add: comb_def comb_nil_def split_beta)

lemma comb_nil_right [simp]: "f \<box> comb_nil = f"
by (simp add: comb_def comb_nil_def split_beta)

lemma comb_assoc [simp]: "(fa \<box> fb) \<box> fc = fa \<box> (fb \<box> fc)"
by (simp add: comb_def split_beta)

lemma comb_inv: "(xs', x') = (f1 \<box> f2) x0 \<Longrightarrow>
  \<exists> xs1 x1 xs2 x2. (xs1, x1) = (f1 x0) \<and> (xs2, x2) = f2 x1 \<and> xs'= xs1 @ xs2 \<and> x'=x2"
apply (case_tac "f1 x0")
apply (case_tac "f2 x1")
apply (simp add: comb_def split_beta)
done

(**********************************************************************)

syntax
  mt_of		:: "method_type \<times> state_type \<Rightarrow> method_type"
  sttp_of	:: "method_type \<times> state_type \<Rightarrow> state_type"

translations
  "mt_of"     => "fst"
  "sttp_of"   => "snd"

consts
  compTpExpr  :: "java_mb \<Rightarrow> java_mb prog \<Rightarrow> expr
                   \<Rightarrow> state_type \<Rightarrow> method_type \<times> state_type"

  compTpExprs :: "java_mb \<Rightarrow> java_mb prog \<Rightarrow> expr list
                   \<Rightarrow> state_type \<Rightarrow> method_type \<times> state_type"

  compTpStmt  :: "java_mb \<Rightarrow> java_mb prog \<Rightarrow> stmt
                   \<Rightarrow> state_type \<Rightarrow> method_type \<times> state_type"


constdefs
  nochangeST :: "state_type \<Rightarrow> method_type \<times> state_type"
  "nochangeST sttp == ([Some sttp], sttp)"
  pushST :: "[ty list, state_type] \<Rightarrow> method_type \<times> state_type"
  "pushST tps == (\<lambda> (ST, LT). ([Some (ST, LT)], (tps @ ST, LT)))"
  dupST :: "state_type \<Rightarrow> method_type \<times> state_type"
  "dupST == (\<lambda> (ST, LT). ([Some (ST, LT)], (hd ST # ST, LT)))"
  dup_x1ST :: "state_type \<Rightarrow> method_type \<times> state_type"
  "dup_x1ST == (\<lambda> (ST, LT). ([Some (ST, LT)], 
                             (hd ST # hd (tl ST) # hd ST # (tl (tl ST)), LT)))"
  popST :: "[nat, state_type] \<Rightarrow> method_type \<times> state_type"
  "popST n == (\<lambda> (ST, LT). ([Some (ST, LT)], (drop n ST, LT)))"
  replST :: "[nat, ty, state_type] \<Rightarrow> method_type \<times> state_type"
  "replST n tp == (\<lambda> (ST, LT). ([Some (ST, LT)], (tp # (drop n ST), LT)))"

  storeST :: "[nat, ty, state_type] \<Rightarrow> method_type \<times> state_type"
  "storeST i tp == (\<lambda> (ST, LT). ([Some (ST, LT)], (tl ST, LT [i:= OK tp])))"


(* Expressions *)

primrec

  "compTpExpr jmb G (NewC c) = pushST [Class c]"

  "compTpExpr jmb G (Cast c e) = 
  (compTpExpr jmb G e) \<box> (replST 1 (Class c))"

  "compTpExpr jmb G (Lit val) = pushST [the (typeof (\<lambda>v. None) val)]"

  "compTpExpr jmb G (BinOp bo e1 e2) = 
     (compTpExpr jmb G e1) \<box> (compTpExpr jmb G e2) \<box> 
     (case bo of 
       Eq => popST 2 \<box> pushST [PrimT Boolean] \<box> popST 1 \<box> pushST [PrimT Boolean]
     | Add => replST 2 (PrimT Integer))"

  "compTpExpr jmb G (LAcc vn) = (\<lambda> (ST, LT). 
      pushST [ok_val (LT ! (index jmb vn))] (ST, LT))"

  "compTpExpr jmb G (vn::=e) = 
      (compTpExpr jmb G e) \<box> dupST \<box> (popST 1)"


  "compTpExpr jmb G ( {cn}e..fn ) = 
      (compTpExpr jmb G e) \<box> replST 1 (snd (the (field (G,cn) fn)))"

  "compTpExpr jmb G (FAss cn e1 fn e2 ) = 
      (compTpExpr jmb G e1) \<box> (compTpExpr jmb G e2) \<box> dup_x1ST \<box> (popST 2)"


  "compTpExpr jmb G ({C}a..mn({fpTs}ps)) =
       (compTpExpr jmb G a) \<box> (compTpExprs jmb G ps) \<box> 
       (replST ((length ps) + 1) (method_rT (the (method (G,C) (mn,fpTs)))))"


(* Expression lists *)

  "compTpExprs jmb G [] = comb_nil"

  "compTpExprs jmb G (e#es) = (compTpExpr jmb G e) \<box> (compTpExprs jmb G es)"


(* Statements *)
primrec
   "compTpStmt jmb G Skip = comb_nil"

   "compTpStmt jmb G (Expr e) =  (compTpExpr jmb G e) \<box> popST 1"

   "compTpStmt jmb G (c1;; c2) = (compTpStmt jmb G c1) \<box> (compTpStmt jmb G c2)"

   "compTpStmt jmb G (If(e) c1 Else c2) = 
      (pushST [PrimT Boolean]) \<box> (compTpExpr jmb G e) \<box> popST 2 \<box>
      (compTpStmt jmb G c1) \<box> nochangeST \<box> (compTpStmt jmb G c2)"

   "compTpStmt jmb G (While(e) c) = 
      (pushST [PrimT Boolean]) \<box> (compTpExpr jmb G e) \<box> popST 2 \<box>
      (compTpStmt jmb G c) \<box> nochangeST"

constdefs
  compTpInit  :: "java_mb \<Rightarrow> (vname * ty)
                   \<Rightarrow> state_type \<Rightarrow> method_type \<times> state_type"
  "compTpInit jmb == (\<lambda> (vn,ty). (pushST [ty]) \<box>  (storeST (index jmb vn) ty))"

consts
  compTpInitLvars :: "[java_mb, (vname \<times> ty) list] 
                   \<Rightarrow> state_type \<Rightarrow> method_type \<times> state_type"

primrec 
  "compTpInitLvars jmb [] = comb_nil"
  "compTpInitLvars jmb (lv#lvars) = (compTpInit jmb lv) \<box> (compTpInitLvars jmb lvars)"

constdefs
   start_ST :: "opstack_type"
  "start_ST == []"

   start_LT :: "cname \<Rightarrow> ty list \<Rightarrow> nat \<Rightarrow> locvars_type"
  "start_LT C pTs n ==  (OK (Class C))#((map OK pTs))@(replicate n Err)"

  compTpMethod  :: "[java_mb prog, cname, java_mb mdecl] \<Rightarrow> method_type"
  "compTpMethod G C == \<lambda> ((mn,pTs),rT, jmb). 
                         let (pns,lvars,blk,res) = jmb
                         in (mt_of
                            ((compTpInitLvars jmb lvars \<box> 
                              compTpStmt jmb G blk \<box> 
                              compTpExpr jmb G res \<box>
                              nochangeST)
                                (start_ST, start_LT C pTs (length lvars))))"

  compTp :: "java_mb prog => prog_type"
  "compTp G C sig == let (D, rT, jmb) = (the (method (G, C) sig))
                      in compTpMethod G C (sig, rT, jmb)"



(**********************************************************************)
  (* Computing the maximum stack size from the method_type *)

constdefs
  ssize_sto :: "(state_type option) \<Rightarrow> nat"
  "ssize_sto sto ==  case sto of None \<Rightarrow> 0 | (Some (ST, LT)) \<Rightarrow> length ST"

  max_of_list :: "nat list \<Rightarrow> nat"
  "max_of_list xs == foldr max xs 0"

  max_ssize :: "method_type \<Rightarrow> nat"
  "max_ssize mt == max_of_list (map ssize_sto mt)"


end

