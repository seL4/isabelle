(*  Title:      HOL/Bali/Term.thy
    ID:         $Id$
    Author:     David von Oheimb
    License:    GPL (GNU GENERAL PUBLIC LICENSE)
*)

header {* Java expressions and statements *}

theory Term = Value:

text {*
design issues:
\begin{itemize}
\item invocation frames for local variables could be reduced to special static
  objects (one per method). This would reduce redundancy, but yield a rather
  non-standard execution model more difficult to understand.
\item method bodies separated from calls to handle assumptions in axiomat. 
  semantics
  NB: Body is intended to be in the environment of the called method.
\item class initialization is regarded as (auxiliary) statement 
      (required for AxSem)
\item result expression of method return is handled by a special result variable
  result variable is treated uniformly with local variables
  \begin{itemize}
  \item[+] welltypedness and existence of the result/return expression is 
           ensured without extra efford
  \end{itemize}
\end{itemize}

simplifications:
\begin{itemize}
\item expression statement allowed for any expression
\item no unary, binary, etc, operators
\item This  is modeled as a special non-assignable local variable
\item Super is modeled as a general expression with the same value as This
\item access to field x in current class via This.x
\item NewA creates only one-dimensional arrays;
  initialization of further subarrays may be simulated with nested NewAs
\item The 'Lit' constructor is allowed to contain a reference value.
  But this is assumed to be prohibited in the input language, which is enforced
  by the type-checking rules.
\item a call of a static method via a type name may be simulated by a dummy 
      variable
\item no nested blocks with inner local variables
\item no synchronized statements
\item no secondary forms of if, while (e.g. no for) (may be easily simulated)
\item no switch (may be simulated with if)
\item the @{text try_catch_finally} statement is divided into the 
      @{text try_catch} statement 
      and a finally statement, which may be considered as try..finally with 
      empty catch
\item the @{text try_catch} statement has exactly one catch clause; 
      multiple ones can be
  simulated with instanceof
\item the compiler is supposed to add the annotations {@{text _}} during 
      type-checking. This
  transformation is left out as its result is checked by the type rules anyway
\end{itemize}
*}

datatype inv_mode                  (* invocation mode for method calls *)
	= Static                   (* static *)
	| SuperM                   (* super  *)
	| IntVir                   (* interface or virtual *)

record  sig =            (* signature of a method, cf. 8.4.2  *)
	  name ::"mname"      (* acutally belongs to Decl.thy *)
          parTs::"ty list"        

translations
  "sig" <= (type) "\<lparr>name::mname,parTs::ty list\<rparr>"
  "sig" <= (type) "\<lparr>name::mname,parTs::ty list,\<dots>::'a\<rparr>"

datatype jump
        = Break label (* break *)
        | Cont label  (* continue *)
        | Ret         (* return from method *)

datatype var
	= LVar                  lname(* local variable (incl. parameters) *)
        | FVar qtname qtname bool expr vname
                                (*class field*)("{_,_,_}_.._"[10,10,10,85,99]90)
	| AVar        expr expr      (* array component *) ("_.[_]"[90,10   ]90)

and expr
	= NewC qtname              (* class instance creation *)
	| NewA ty expr             (* array creation *) ("New _[_]"[99,10   ]85)
	| Cast ty expr             (* type cast  *)
	| Inst expr ref_ty         (* instanceof *)     ("_ InstOf _"[85,99] 85)
	| Lit  val                 (* literal value, references not allowed *)
	| Super                    (* special Super keyword *)
	| Acc  var                 (* variable access *)
	| Ass  var expr            (* variable assign *) ("_:=_"   [90,85   ]85)
	| Cond expr expr expr      (* conditional *)  ("_ ? _ : _" [85,85,80]80)
        | Call qtname ref_ty inv_mode expr mname "(ty list)" (* method call *)
                  "(expr list)" ("{_,_,_}_\<cdot>_'( {_}_')"[10,10,10,85,99,10,10]85)
        | Methd qtname sig          (*   (folded) method (see below) *)
        | Body qtname stmt          (* (unfolded) method body *)
and  stmt
	= Skip                     (* empty      statement *)
	| Expr  expr               (* expression statement *)
        | Lab   label stmt         ("_\<bullet> _"(* labeled statement*)[      99,66]66)
                                   (* handles break *)
	| Comp  stmt stmt          ("_;; _"                     [      66,65]65)
	| If_   expr stmt stmt     ("If'(_') _ Else _"          [   80,79,79]70)
	| Loop  label expr stmt    ("_\<bullet> While'(_') _"           [   99,80,79]70)
        | Do jump                  (* break, continue, return *)
	| Throw expr
        | TryC  stmt
	        qtname vname stmt   ("Try _ Catch'(_ _') _"     [79,99,80,79]70)
	| Fin   stmt stmt          ("_ Finally _"               [      79,79]70)
	| Init  qtname              (* class initialization *)


text {*
The expressions Methd and Body are artificial program constructs, in the
sense that they are not used to define a concrete Bali program. In the 
evaluation semantic definition they are "generated on the fly" to decompose 
the task to define the behaviour of the Call expression. They are crucial 
for the axiomatic semantics to give a syntactic hook to insert 
some assertions (cf. AxSem.thy, Eval.thy).
Also the Init statement (to initialize a class on its first use) is inserted 
in various places by the evaluation semantics.   
*}
 
types "term" = "(expr+stmt, var, expr list) sum3"
translations
  "sig"   <= (type) "mname \<times> ty list"
  "var"   <= (type) "Term.var"
  "expr"  <= (type) "Term.expr"
  "stmt"  <= (type) "Term.stmt"
  "term"  <= (type) "(expr+stmt, var, expr list) sum3"

syntax
  
  this    :: expr
  LAcc    :: "vname \<Rightarrow>         expr" ("!!")
  LAss    :: "vname \<Rightarrow> expr \<Rightarrow> stmt" ("_:==_" [90,85] 85)
  Return  :: "expr \<Rightarrow> stmt"
  StatRef :: "ref_ty \<Rightarrow> expr"

translations
  
 "this"       == "Acc (LVar This)"
 "!!v"        == "Acc (LVar (EName (VNam v)))"
 "v:==e"      == "Expr (Ass (LVar (EName (VNam  v))) e)"
 "Return e"   == "Expr (Ass (LVar (EName Res)) e);; Do Ret" 
                                                   (* Res := e;; Do Ret *)
 "StatRef rt" == "Cast (RefT rt) (Lit Null)"
  
constdefs

  is_stmt :: "term \<Rightarrow> bool"
 "is_stmt t \<equiv> \<exists>c. t=In1r c"

ML {*
bind_thms ("is_stmt_rews", sum3_instantiate (thm "is_stmt_def"));
*}

declare is_stmt_rews [simp]
end