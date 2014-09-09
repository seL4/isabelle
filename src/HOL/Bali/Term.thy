(*  Title:      HOL/Bali/Term.thy
    Author:     David von Oheimb
*)

header {* Java expressions and statements *}

theory Term imports Value Table begin

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



type_synonym locals = "(lname, val) table"  --{* local variables *}


datatype_new jump
        = Break label --{* break *}
        | Cont label  --{* continue *}
        | Ret         --{* return from method *}

datatype_new xcpt        --{* exception *}
        = Loc loc    --{* location of allocated execption object *}
        | Std xname  --{* intermediate standard exception, see Eval.thy *}

datatype_new error
       =  AccessViolation  --{* Access to a member that isn't permitted *}
        | CrossMethodJump  --{* Method exits with a break or continue *}

datatype_new abrupt       --{* abrupt completion *} 
        = Xcpt xcpt   --{* exception *}
        | Jump jump   --{* break, continue, return *}
        | Error error -- {* runtime errors, we wan't to detect and proof absent
                            in welltyped programms *}
type_synonym
  abopt  = "abrupt option"

text {* Local variable store and exception. 
Anticipation of State.thy used by smallstep semantics. For a method call, 
we save the local variables of the caller in the term Callee to restore them 
after method return. Also an exception must be restored after the finally
statement *}

translations
 (type) "locals" <= (type) "(lname, val) table"

datatype_new inv_mode                  --{* invocation mode for method calls *}
        = Static                   --{* static *}
        | SuperM                   --{* super  *}
        | IntVir                   --{* interface or virtual *}

record  sig =              --{* signature of a method, cf. 8.4.2  *}
          name ::"mname"   --{* acutally belongs to Decl.thy *}
          parTs::"ty list"        

translations
  (type) "sig" <= (type) "\<lparr>name::mname,parTs::ty list\<rparr>"
  (type) "sig" <= (type) "\<lparr>name::mname,parTs::ty list,\<dots>::'a\<rparr>"

--{* function codes for unary operations *}
datatype_new unop =  UPlus    -- {*{\tt +} unary plus*} 
               | UMinus   -- {*{\tt -} unary minus*}
               | UBitNot  -- {*{\tt ~} bitwise NOT*}
               | UNot     -- {*{\tt !} logical complement*}

--{* function codes for binary operations *}
datatype_new binop = Mul     -- {*{\tt * }   multiplication*}
               | Div     -- {*{\tt /}   division*}
               | Mod     -- {*{\tt \%}   remainder*}
               | Plus    -- {*{\tt +}   addition*}
               | Minus   -- {*{\tt -}   subtraction*}
               | LShift  -- {*{\tt <<}  left shift*}
               | RShift  -- {*{\tt >>}  signed right shift*}
               | RShiftU -- {*{\tt >>>} unsigned right shift*}
               | Less    -- {*{\tt <}   less than*}
               | Le      -- {*{\tt <=}  less than or equal*}
               | Greater -- {*{\tt >}   greater than*}
               | Ge      -- {*{\tt >=}  greater than or equal*}
               | Eq      -- {*{\tt ==}  equal*}
               | Neq     -- {*{\tt !=}  not equal*}
               | BitAnd  -- {*{\tt \&}   bitwise AND*}
               | And     -- {*{\tt \&}   boolean AND*}
               | BitXor  -- {*{\texttt \^}   bitwise Xor*}
               | Xor     -- {*{\texttt \^}   boolean Xor*}
               | BitOr   -- {*{\tt |}   bitwise Or*}
               | Or      -- {*{\tt |}   boolean Or*}
               | CondAnd -- {*{\tt \&\&}  conditional And*}
               | CondOr  -- {*{\tt ||}  conditional Or *}
text{* The boolean operators {\tt \&} and {\tt |} strictly evaluate both
of their arguments. The conditional operators {\tt \&\&} and {\tt ||} only 
evaluate the second argument if the value of the whole expression isn't 
allready determined by the first argument.
e.g.: {\tt false \&\& e} e is not evaluated;  
      {\tt true || e} e is not evaluated; 
*}

datatype_new var
        = LVar lname --{* local variable (incl. parameters) *}
        | FVar qtname qtname bool expr vname ("{_,_,_}_.._"[10,10,10,85,99]90)
                     --{* class field *}
                     --{* @{term "{accC,statDeclC,stat}e..fn"}   *}
                     --{* @{text accC}: accessing class (static class were *}
                     --{* the code is declared. Annotation only needed for *}
                     --{* evaluation to check accessibility) *}
                     --{* @{text statDeclC}: static declaration class of field*}
                     --{* @{text stat}: static or instance field?*}
                     --{* @{text e}: reference to object*}
                     --{* @{text fn}: field name*}
        | AVar expr expr ("_.[_]"[90,10   ]90)
                     --{* array component *}
                     --{* @{term "e1.[e2]"}: e1 array reference; e2 index *}
        | InsInitV stmt var 
                     --{* insertion of initialization before evaluation   *}
                     --{* of var (technical term for smallstep semantics.)*}

and expr
        = NewC qtname         --{* class instance creation *}
        | NewA ty expr ("New _[_]"[99,10   ]85) 
                              --{* array creation *} 
        | Cast ty expr        --{* type cast  *}
        | Inst expr ref_ty ("_ InstOf _"[85,99] 85)   
                              --{* instanceof *}     
        | Lit  val              --{* literal value, references not allowed *}
        | UnOp unop expr        --{* unary operation *}
        | BinOp binop expr expr --{* binary operation *}
        
        | Super               --{* special Super keyword *}
        | Acc  var            --{* variable access *}
        | Ass  var expr       ("_:=_"   [90,85   ]85)
                              --{* variable assign *} 
        | Cond expr expr expr ("_ ? _ : _" [85,85,80]80) --{* conditional *}  
        | Call qtname ref_ty inv_mode expr mname "(ty list)" "(expr list)"  
            ("{_,_,_}_\<cdot>_'( {_}_')"[10,10,10,85,99,10,10]85) 
                    --{* method call *} 
                    --{* @{term "{accC,statT,mode}e\<cdot>mn({pTs}args)"} " *}
                    --{* @{text accC}: accessing class (static class were *}
                    --{* the call code is declared. Annotation only needed for*}
                    --{* evaluation to check accessibility) *}
                    --{* @{text statT}: static declaration class/interface of *}
                    --{* method *}
                    --{* @{text mode}: invocation mode *}
                    --{* @{text e}: reference to object*}
                    --{* @{text mn}: field name*}   
                    --{* @{text pTs}: types of parameters *}
                    --{* @{text args}: the actual parameters/arguments *} 
        | Methd qtname sig    --{*   (folded) method (see below) *}
        | Body qtname stmt    --{* (unfolded) method body *}
        | InsInitE stmt expr  
                 --{* insertion of initialization before *}
                 --{* evaluation of expr (technical term for smallstep sem.) *}
        | Callee locals expr  --{* save callers locals in callee-Frame *}
                              --{* (technical term for smallstep semantics) *}
and  stmt
        = Skip                  --{* empty      statement *}
        | Expr  expr            --{* expression statement *}
        | Lab   jump stmt       ("_\<bullet> _" [      99,66]66)
                                --{* labeled statement; handles break *}
        | Comp  stmt stmt       ("_;; _"                  [      66,65]65)
        | If'   expr stmt stmt  ("If'(_') _ Else _"       [   80,79,79]70)
        | Loop  label expr stmt ("_\<bullet> While'(_') _"        [   99,80,79]70)
        | Jmp jump              --{* break, continue, return *}
        | Throw expr
        | TryC  stmt qtname vname stmt ("Try _ Catch'(_ _') _"  [79,99,80,79]70)
             --{* @{term "Try c1 Catch(C vn) c2"} *} 
             --{* @{text c1}: block were exception may be thrown *}
             --{* @{text C}:  execption class to catch *}
             --{* @{text vn}: local name for exception used in @{text c2}*}
             --{* @{text c2}: block to execute when exception is cateched*}
        | Fin  stmt  stmt        ("_ Finally _"               [      79,79]70)
        | FinA abopt stmt       --{* Save abruption of first statement *} 
                                --{* technical term  for smallstep sem.) *}
        | Init  qtname          --{* class initialization *}


text {*
The expressions Methd and Body are artificial program constructs, in the
sense that they are not used to define a concrete Bali program. In the 
operational semantic's they are "generated on the fly" 
to decompose the task to define the behaviour of the Call expression. 
They are crucial for the axiomatic semantics to give a syntactic hook to insert 
some assertions (cf. AxSem.thy, Eval.thy). 
The Init statement (to initialize a class on its first use) is 
inserted in various places by the semantics. 
Callee, InsInitV, InsInitE,FinA are only needed as intermediate steps in the
smallstep (transition) semantics (cf. Trans.thy). Callee is used to save the 
local variables of the caller for method return. So ve avoid modelling a 
frame stack.
The InsInitV/E terms are only used by the smallstep semantics to model the
intermediate steps of class-initialisation.
*}
 
type_synonym "term" = "(expr+stmt,var,expr list) sum3"
translations
  (type) "sig"   <= (type) "mname \<times> ty list"
  (type) "term"  <= (type) "(expr+stmt,var,expr list) sum3"

abbreviation this :: expr
  where "this == Acc (LVar This)"

abbreviation LAcc :: "vname \<Rightarrow> expr" ("!!")
  where "!!v == Acc (LVar (EName (VNam v)))"

abbreviation
  LAss :: "vname \<Rightarrow> expr \<Rightarrow>stmt" ("_:==_" [90,85] 85)
  where "v:==e == Expr (Ass (LVar (EName (VNam  v))) e)"

abbreviation
  Return :: "expr \<Rightarrow> stmt"
  where "Return e == Expr (Ass (LVar (EName Res)) e);; Jmp Ret" --{* \tt Res := e;; Jmp Ret *}

abbreviation
  StatRef :: "ref_ty \<Rightarrow> expr"
  where "StatRef rt == Cast (RefT rt) (Lit Null)"
  
definition
  is_stmt :: "term \<Rightarrow> bool"
  where "is_stmt t = (\<exists>c. t=In1r c)"

ML {* ML_Thms.bind_thms ("is_stmt_rews", sum3_instantiate @{context} @{thm is_stmt_def}) *}

declare is_stmt_rews [simp]

text {*
  Here is some syntactic stuff to handle the injections of statements,
  expressions, variables and expression lists into general terms.
*}

abbreviation (input)
  expr_inj_term :: "expr \<Rightarrow> term" ("\<langle>_\<rangle>\<^sub>e" 1000)
  where "\<langle>e\<rangle>\<^sub>e == In1l e"

abbreviation (input)
  stmt_inj_term :: "stmt \<Rightarrow> term" ("\<langle>_\<rangle>\<^sub>s" 1000)
  where "\<langle>c\<rangle>\<^sub>s == In1r c"

abbreviation (input)
  var_inj_term :: "var \<Rightarrow> term"  ("\<langle>_\<rangle>\<^sub>v" 1000)
  where "\<langle>v\<rangle>\<^sub>v == In2 v"

abbreviation (input)
  lst_inj_term :: "expr list \<Rightarrow> term" ("\<langle>_\<rangle>\<^sub>l" 1000)
  where "\<langle>es\<rangle>\<^sub>l == In3 es"

text {* It seems to be more elegant to have an overloaded injection like the
following.
*}

class inj_term =
  fixes inj_term:: "'a \<Rightarrow> term" ("\<langle>_\<rangle>" 1000)

text {* How this overloaded injections work can be seen in the theory 
@{text DefiniteAssignment}. Other big inductive relations on
terms defined in theories @{text WellType}, @{text Eval}, @{text Evaln} and
@{text AxSem} don't follow this convention right now, but introduce subtle 
syntactic sugar in the relations themselves to make a distinction on 
expressions, statements and so on. So unfortunately you will encounter a 
mixture of dealing with these injections. The abbreviations above are used
as bridge between the different conventions.  
*}

instantiation stmt :: inj_term
begin

definition
  stmt_inj_term_def: "\<langle>c::stmt\<rangle> = In1r c"

instance ..

end

lemma stmt_inj_term_simp: "\<langle>c::stmt\<rangle> = In1r c"
by (simp add: stmt_inj_term_def)

lemma  stmt_inj_term [iff]: "\<langle>x::stmt\<rangle> = \<langle>y\<rangle> \<equiv> x = y"
  by (simp add: stmt_inj_term_simp)

instantiation expr :: inj_term
begin

definition
  expr_inj_term_def: "\<langle>e::expr\<rangle> = In1l e"

instance ..

end

lemma expr_inj_term_simp: "\<langle>e::expr\<rangle> = In1l e"
by (simp add: expr_inj_term_def)

lemma expr_inj_term [iff]: "\<langle>x::expr\<rangle> = \<langle>y\<rangle> \<equiv> x = y"
  by (simp add: expr_inj_term_simp)

instantiation var :: inj_term
begin

definition
  var_inj_term_def: "\<langle>v::var\<rangle> = In2 v"

instance ..

end

lemma var_inj_term_simp: "\<langle>v::var\<rangle> = In2 v"
by (simp add: var_inj_term_def)

lemma var_inj_term [iff]: "\<langle>x::var\<rangle> = \<langle>y\<rangle> \<equiv> x = y"
  by (simp add: var_inj_term_simp)

class expr_of =
  fixes expr_of :: "'a \<Rightarrow> expr"

instantiation expr :: expr_of
begin

definition
  "expr_of = (\<lambda>(e::expr). e)"

instance ..

end 

instantiation list :: (expr_of) inj_term
begin

definition
  "\<langle>es::'a list\<rangle> = In3 (map expr_of es)"

instance ..

end

lemma expr_list_inj_term_def:
  "\<langle>es::expr list\<rangle> \<equiv> In3 es"
  by (simp add: inj_term_list_def expr_of_expr_def)

lemma expr_list_inj_term_simp: "\<langle>es::expr list\<rangle> = In3 es"
by (simp add: expr_list_inj_term_def)

lemma expr_list_inj_term [iff]: "\<langle>x::expr list\<rangle> = \<langle>y\<rangle> \<equiv> x = y"
  by (simp add: expr_list_inj_term_simp)

lemmas inj_term_simps = stmt_inj_term_simp expr_inj_term_simp var_inj_term_simp
                        expr_list_inj_term_simp
lemmas inj_term_sym_simps = stmt_inj_term_simp [THEN sym] 
                            expr_inj_term_simp [THEN sym]
                            var_inj_term_simp [THEN sym]
                            expr_list_inj_term_simp [THEN sym]

lemma stmt_expr_inj_term [iff]: "\<langle>t::stmt\<rangle> \<noteq> \<langle>w::expr\<rangle>"
  by (simp add: inj_term_simps)
lemma expr_stmt_inj_term [iff]: "\<langle>t::expr\<rangle> \<noteq> \<langle>w::stmt\<rangle>"
  by (simp add: inj_term_simps)
lemma stmt_var_inj_term [iff]: "\<langle>t::stmt\<rangle> \<noteq> \<langle>w::var\<rangle>"
  by (simp add: inj_term_simps)
lemma var_stmt_inj_term [iff]: "\<langle>t::var\<rangle> \<noteq> \<langle>w::stmt\<rangle>"
  by (simp add: inj_term_simps)
lemma stmt_elist_inj_term [iff]: "\<langle>t::stmt\<rangle> \<noteq> \<langle>w::expr list\<rangle>"
  by (simp add: inj_term_simps)
lemma elist_stmt_inj_term [iff]: "\<langle>t::expr list\<rangle> \<noteq> \<langle>w::stmt\<rangle>"
  by (simp add: inj_term_simps)
lemma expr_var_inj_term [iff]: "\<langle>t::expr\<rangle> \<noteq> \<langle>w::var\<rangle>"
  by (simp add: inj_term_simps)
lemma var_expr_inj_term [iff]: "\<langle>t::var\<rangle> \<noteq> \<langle>w::expr\<rangle>"
  by (simp add: inj_term_simps)
lemma expr_elist_inj_term [iff]: "\<langle>t::expr\<rangle> \<noteq> \<langle>w::expr list\<rangle>"
  by (simp add: inj_term_simps)
lemma elist_expr_inj_term [iff]: "\<langle>t::expr list\<rangle> \<noteq> \<langle>w::expr\<rangle>"
  by (simp add: inj_term_simps)
lemma var_elist_inj_term [iff]: "\<langle>t::var\<rangle> \<noteq> \<langle>w::expr list\<rangle>"
  by (simp add: inj_term_simps)
lemma elist_var_inj_term [iff]: "\<langle>t::expr list\<rangle> \<noteq> \<langle>w::var\<rangle>"
  by (simp add: inj_term_simps)

lemma term_cases: "
  \<lbrakk>\<And> v. P \<langle>v\<rangle>\<^sub>v; \<And> e. P \<langle>e\<rangle>\<^sub>e;\<And> c. P \<langle>c\<rangle>\<^sub>s;\<And> l. P \<langle>l\<rangle>\<^sub>l\<rbrakk>
  \<Longrightarrow> P t"
  apply (cases t)
  apply (case_tac a)
  apply auto
  done

section {* Evaluation of unary operations *}
primrec eval_unop :: "unop \<Rightarrow> val \<Rightarrow> val"
where
  "eval_unop UPlus v = Intg (the_Intg v)"
| "eval_unop UMinus v = Intg (- (the_Intg v))"
| "eval_unop UBitNot v = Intg 42"                -- "FIXME: Not yet implemented"
| "eval_unop UNot v = Bool (\<not> the_Bool v)"

section {* Evaluation of binary operations *}
primrec eval_binop :: "binop \<Rightarrow> val \<Rightarrow> val \<Rightarrow> val"
where
  "eval_binop Mul     v1 v2 = Intg ((the_Intg v1) * (the_Intg v2))" 
| "eval_binop Div     v1 v2 = Intg ((the_Intg v1) div (the_Intg v2))"
| "eval_binop Mod     v1 v2 = Intg ((the_Intg v1) mod (the_Intg v2))"
| "eval_binop Plus    v1 v2 = Intg ((the_Intg v1) + (the_Intg v2))"
| "eval_binop Minus   v1 v2 = Intg ((the_Intg v1) - (the_Intg v2))"

-- "Be aware of the explicit coercion of the shift distance to nat"
| "eval_binop LShift  v1 v2 = Intg ((the_Intg v1) *   (2^(nat (the_Intg v2))))"
| "eval_binop RShift  v1 v2 = Intg ((the_Intg v1) div (2^(nat (the_Intg v2))))"
| "eval_binop RShiftU v1 v2 = Intg 42" --"FIXME: Not yet implemented"

| "eval_binop Less    v1 v2 = Bool ((the_Intg v1) < (the_Intg v2))" 
| "eval_binop Le      v1 v2 = Bool ((the_Intg v1) \<le> (the_Intg v2))"
| "eval_binop Greater v1 v2 = Bool ((the_Intg v2) < (the_Intg v1))"
| "eval_binop Ge      v1 v2 = Bool ((the_Intg v2) \<le> (the_Intg v1))"

| "eval_binop Eq      v1 v2 = Bool (v1=v2)"
| "eval_binop Neq     v1 v2 = Bool (v1\<noteq>v2)"
| "eval_binop BitAnd  v1 v2 = Intg 42" -- "FIXME: Not yet implemented"
| "eval_binop And     v1 v2 = Bool ((the_Bool v1) \<and> (the_Bool v2))"
| "eval_binop BitXor  v1 v2 = Intg 42" -- "FIXME: Not yet implemented"
| "eval_binop Xor     v1 v2 = Bool ((the_Bool v1) \<noteq> (the_Bool v2))"
| "eval_binop BitOr   v1 v2 = Intg 42" -- "FIXME: Not yet implemented"
| "eval_binop Or      v1 v2 = Bool ((the_Bool v1) \<or> (the_Bool v2))"
| "eval_binop CondAnd v1 v2 = Bool ((the_Bool v1) \<and> (the_Bool v2))"
| "eval_binop CondOr  v1 v2 = Bool ((the_Bool v1) \<or> (the_Bool v2))"

definition
  need_second_arg :: "binop \<Rightarrow> val \<Rightarrow> bool" where
  "need_second_arg binop v1 = (\<not> ((binop=CondAnd \<and>  \<not> the_Bool v1) \<or>
                                 (binop=CondOr  \<and> the_Bool v1)))"
text {* @{term CondAnd} and @{term CondOr} only evalulate the second argument
 if the value isn't already determined by the first argument*}

lemma need_second_arg_CondAnd [simp]: "need_second_arg CondAnd (Bool b) = b" 
by (simp add: need_second_arg_def)

lemma need_second_arg_CondOr [simp]: "need_second_arg CondOr (Bool b) = (\<not> b)" 
by (simp add: need_second_arg_def)

lemma need_second_arg_strict[simp]: 
 "\<lbrakk>binop\<noteq>CondAnd; binop\<noteq>CondOr\<rbrakk> \<Longrightarrow> need_second_arg binop b"
by (cases binop) 
   (simp_all add: need_second_arg_def)
end