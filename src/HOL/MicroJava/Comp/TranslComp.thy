(*  Title:      HOL/MicroJava/Comp/TranslComp.thy
    ID:         $Id$
    Author:     Martin Strecker
*)

(* Compiling MicroJava into MicroJVM -- Translation functions *)

theory TranslComp =  TranslCompTp:


(* parameter java_mb only serves to define function index later *)
consts
 compExpr  :: "java_mb => expr      => instr list"
 compExprs :: "java_mb => expr list => instr list"
 compStmt  :: "java_mb => stmt      => instr list"



(**********************************************************************)
(** code generation for expressions **)

primrec
(*class instance creation*)
"compExpr jmb (NewC c) = [New c]"

(*type cast*)
"compExpr jmb (Cast c e) = compExpr jmb e @ [Checkcast c]" 


(*literals*)
"compExpr jmb (Lit val) = [LitPush val]" 

      
(* binary operation *)                         
"compExpr jmb (BinOp bo e1 e2) = compExpr jmb e1 @ compExpr jmb e2 @ 
  (case bo of Eq => [Ifcmpeq 3,LitPush(Bool False),Goto 2,LitPush(Bool True)]
            | Add => [IAdd])" 

(*local variable*)
"compExpr jmb (LAcc vn) = [Load (index jmb vn)]" 


(*assignement*)
"compExpr jmb (vn::=e) = compExpr jmb e @ [Dup , Store (index jmb vn)]" 


(*field access*)
"compExpr jmb ( {cn}e..fn ) = compExpr jmb e @ [Getfield fn cn]"


(*field assignement - expected syntax:  {_}_.._:=_ *)
"compExpr jmb (FAss cn e1 fn e2 ) = 
       compExpr jmb e1 @ compExpr jmb e2 @ [Dup_x1 , Putfield fn cn]"


(*method call*)
"compExpr jmb (Call cn e1 mn X ps) = 
        compExpr jmb e1 @ compExprs jmb ps @ [Invoke cn mn X]"


(** code generation expression lists **)

"compExprs jmb []     = []"

"compExprs jmb (e#es) = compExpr jmb e @ compExprs jmb es"

  

primrec
(** code generation for statements **)

"compStmt jmb Skip = []"			

"compStmt jmb (Expr e) = ((compExpr jmb e) @ [Pop])"

"compStmt jmb (c1;; c2) = ((compStmt jmb c1) @ (compStmt jmb c2))"

"compStmt jmb (If(e) c1 Else c2) =
	(let cnstf = LitPush (Bool False);
             cnd   = compExpr jmb e;
	     thn   = compStmt jmb c1;
	     els   = compStmt jmb c2;
	     test  = Ifcmpeq (int(length thn +2)); 
	     thnex = Goto (int(length els +1))
	 in
	 [cnstf] @ cnd @ [test] @ thn @ [thnex] @ els)"

"compStmt jmb (While(e) c) =
	(let cnstf = LitPush (Bool False);
             cnd   = compExpr jmb e;
	     bdy   = compStmt jmb c;
	     test  = Ifcmpeq (int(length bdy +2)); 
	     loop  = Goto (-(int((length bdy) + (length cnd) +2)))
	 in
	 [cnstf] @ cnd @ [test] @ bdy @ [loop])"

(**********************************************************************)

(*compiling methods, classes and programs*) 

(*initialising a single variable*)
constdefs
 load_default_val :: "ty => instr"
"load_default_val ty == LitPush (default_val ty)"

 compInit :: "java_mb => (vname * ty) => instr list"
"compInit jmb == \<lambda> (vn,ty). [load_default_val ty, Store (index jmb vn)]"

 compInitLvars :: "[java_mb, (vname \<times> ty) list] \<Rightarrow> bytecode"
 "compInitLvars jmb lvars == concat (map (compInit jmb) lvars)"

  compMethod :: "java_mb prog \<Rightarrow> cname \<Rightarrow> java_mb mdecl \<Rightarrow> jvm_method mdecl"
  "compMethod G C jmdl == let (sig, rT, jmb) = jmdl;
                        (pns,lvars,blk,res) = jmb;
                        mt = (compTpMethod G C jmdl);
                        bc = compInitLvars jmb lvars @ 
                             compStmt jmb blk @ compExpr jmb res @
                             [Return]
                  in (sig, rT, max_ssize mt, length lvars, bc, [])"

  compClass :: "java_mb prog => java_mb cdecl=> jvm_method cdecl"
  "compClass G == \<lambda> (C,cno,fdls,jmdls). (C,cno,fdls, map (compMethod G C) jmdls)"

  comp :: "java_mb prog => jvm_prog"
  "comp G == map (compClass G) G"

end


