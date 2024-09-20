(*  Title:      HOL/Bali/Term.thy
    Author:     David von Oheimb
*)

subsection \<open>Java expressions and statements\<close>

theory Term imports Value Table begin

text \<open>
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
\item the \<open>try_catch_finally\<close> statement is divided into the 
      \<open>try_catch\<close> statement 
      and a finally statement, which may be considered as try..finally with 
      empty catch
\item the \<open>try_catch\<close> statement has exactly one catch clause; 
      multiple ones can be
  simulated with instanceof
\item the compiler is supposed to add the annotations {\<open>_\<close>} during 
      type-checking. This
  transformation is left out as its result is checked by the type rules anyway
\end{itemize}
\<close>



type_synonym locals = "(lname, val) table"  \<comment> \<open>local variables\<close>


datatype jump
        = Break label \<comment> \<open>break\<close>
        | Cont label  \<comment> \<open>continue\<close>
        | Ret         \<comment> \<open>return from method\<close>

datatype xcpt        \<comment> \<open>exception\<close>
        = Loc loc    \<comment> \<open>location of allocated execption object\<close>
        | Std xname  \<comment> \<open>intermediate standard exception, see Eval.thy\<close>

datatype error
       =  AccessViolation  \<comment> \<open>Access to a member that isn't permitted\<close>
        | CrossMethodJump  \<comment> \<open>Method exits with a break or continue\<close>

datatype abrupt       \<comment> \<open>abrupt completion\<close> 
        = Xcpt xcpt   \<comment> \<open>exception\<close>
        | Jump jump   \<comment> \<open>break, continue, return\<close>
        | Error error \<comment> \<open>runtime errors, we wan't to detect and proof absent
                            in welltyped programms\<close>
type_synonym
  abopt  = "abrupt option"

text \<open>Local variable store and exception. 
Anticipation of State.thy used by smallstep semantics. For a method call, 
we save the local variables of the caller in the term Callee to restore them 
after method return. Also an exception must be restored after the finally
statement\<close>

translations
 (type) "locals" <= (type) "(lname, val) table"

datatype inv_mode                  \<comment> \<open>invocation mode for method calls\<close>
        = Static                   \<comment> \<open>static\<close>
        | SuperM                   \<comment> \<open>super\<close>
        | IntVir                   \<comment> \<open>interface or virtual\<close>

record  sig =              \<comment> \<open>signature of a method, cf. 8.4.2\<close>
          name ::"mname"   \<comment> \<open>acutally belongs to Decl.thy\<close>
          parTs::"ty list"        

translations
  (type) "sig" <= (type) "\<lparr>name::mname,parTs::ty list\<rparr>"
  (type) "sig" <= (type) "\<lparr>name::mname,parTs::ty list,\<dots>::'a\<rparr>"

\<comment> \<open>function codes for unary operations\<close>
datatype unop =  UPlus    \<comment> \<open>{\tt +} unary plus\<close> 
               | UMinus   \<comment> \<open>{\tt -} unary minus\<close>
               | UBitNot  \<comment> \<open>{\tt ~} bitwise NOT\<close>
               | UNot     \<comment> \<open>{\tt !} logical complement\<close>

\<comment> \<open>function codes for binary operations\<close>
datatype binop = Mul     \<comment> \<open>{\tt *}   multiplication\<close>
               | Div     \<comment> \<open>{\tt /}   division\<close>
               | Mod     \<comment> \<open>{\tt \%}   remainder\<close>
               | Plus    \<comment> \<open>{\tt +}   addition\<close>
               | Minus   \<comment> \<open>{\tt -}   subtraction\<close>
               | LShift  \<comment> \<open>{\tt <<}  left shift\<close>
               | RShift  \<comment> \<open>{\tt >>}  signed right shift\<close>
               | RShiftU \<comment> \<open>{\tt >>>} unsigned right shift\<close>
               | Less    \<comment> \<open>{\tt <}   less than\<close>
               | Le      \<comment> \<open>{\tt <=}  less than or equal\<close>
               | Greater \<comment> \<open>{\tt >}   greater than\<close>
               | Ge      \<comment> \<open>{\tt >=}  greater than or equal\<close>
               | Eq      \<comment> \<open>{\tt ==}  equal\<close>
               | Neq     \<comment> \<open>{\tt !=}  not equal\<close>
               | BitAnd  \<comment> \<open>{\tt \&}   bitwise AND\<close>
               | And     \<comment> \<open>{\tt \&}   boolean AND\<close>
               | BitXor  \<comment> \<open>{\texttt \^}   bitwise Xor\<close>
               | Xor     \<comment> \<open>{\texttt \^}   boolean Xor\<close>
               | BitOr   \<comment> \<open>{\tt |}   bitwise Or\<close>
               | Or      \<comment> \<open>{\tt |}   boolean Or\<close>
               | CondAnd \<comment> \<open>{\tt \&\&}  conditional And\<close>
               | CondOr  \<comment> \<open>{\tt ||}  conditional Or\<close>
text\<open>The boolean operators {\tt \&} and {\tt |} strictly evaluate both
of their arguments. The conditional operators {\tt \&\&} and {\tt ||} only 
evaluate the second argument if the value of the whole expression isn't 
allready determined by the first argument.
e.g.: {\tt false \&\& e} e is not evaluated;  
      {\tt true || e} e is not evaluated; 
\<close>

datatype var
        = LVar lname \<comment> \<open>local variable (incl. parameters)\<close>
        | FVar qtname qtname bool expr vname (\<open>{_,_,_}_.._\<close>[10,10,10,85,99]90)
                     \<comment> \<open>class field\<close>
                     \<comment> \<open>\<^term>\<open>{accC,statDeclC,stat}e..fn\<close>\<close>
                     \<comment> \<open>\<open>accC\<close>: accessing class (static class were\<close>
                     \<comment> \<open>the code is declared. Annotation only needed for\<close>
                     \<comment> \<open>evaluation to check accessibility)\<close>
                     \<comment> \<open>\<open>statDeclC\<close>: static declaration class of field\<close>
                     \<comment> \<open>\<open>stat\<close>: static or instance field?\<close>
                     \<comment> \<open>\<open>e\<close>: reference to object\<close>
                     \<comment> \<open>\<open>fn\<close>: field name\<close>
        | AVar expr expr (\<open>_.[_]\<close>[90,10   ]90)
                     \<comment> \<open>array component\<close>
                     \<comment> \<open>\<^term>\<open>e1.[e2]\<close>: e1 array reference; e2 index\<close>
        | InsInitV stmt var 
                     \<comment> \<open>insertion of initialization before evaluation\<close>
                     \<comment> \<open>of var (technical term for smallstep semantics.)\<close>

and expr
        = NewC qtname         \<comment> \<open>class instance creation\<close>
        | NewA ty expr (\<open>New _[_]\<close>[99,10   ]85) 
                              \<comment> \<open>array creation\<close> 
        | Cast ty expr        \<comment> \<open>type cast\<close>
        | Inst expr ref_ty (\<open>_ InstOf _\<close>[85,99] 85)   
                              \<comment> \<open>instanceof\<close>     
        | Lit  val              \<comment> \<open>literal value, references not allowed\<close>
        | UnOp unop expr        \<comment> \<open>unary operation\<close>
        | BinOp binop expr expr \<comment> \<open>binary operation\<close>
        
        | Super               \<comment> \<open>special Super keyword\<close>
        | Acc  var            \<comment> \<open>variable access\<close>
        | Ass  var expr       (\<open>_:=_\<close>   [90,85   ]85)
                              \<comment> \<open>variable assign\<close> 
        | Cond expr expr expr (\<open>_ ? _ : _\<close> [85,85,80]80) \<comment> \<open>conditional\<close>  
        | Call qtname ref_ty inv_mode expr mname "(ty list)" "(expr list)"  
            (\<open>{_,_,_}_\<cdot>_'( {_}_')\<close>[10,10,10,85,99,10,10]85) 
                    \<comment> \<open>method call\<close> 
                    \<comment> \<open>\<^term>\<open>{accC,statT,mode}e\<cdot>mn({pTs}args)\<close> "\<close>
                    \<comment> \<open>\<open>accC\<close>: accessing class (static class were\<close>
                    \<comment> \<open>the call code is declared. Annotation only needed for\<close>
                    \<comment> \<open>evaluation to check accessibility)\<close>
                    \<comment> \<open>\<open>statT\<close>: static declaration class/interface of\<close>
                    \<comment> \<open>method\<close>
                    \<comment> \<open>\<open>mode\<close>: invocation mode\<close>
                    \<comment> \<open>\<open>e\<close>: reference to object\<close>
                    \<comment> \<open>\<open>mn\<close>: field name\<close>   
                    \<comment> \<open>\<open>pTs\<close>: types of parameters\<close>
                    \<comment> \<open>\<open>args\<close>: the actual parameters/arguments\<close> 
        | Methd qtname sig    \<comment> \<open>(folded) method (see below)\<close>
        | Body qtname stmt    \<comment> \<open>(unfolded) method body\<close>
        | InsInitE stmt expr  
                 \<comment> \<open>insertion of initialization before\<close>
                 \<comment> \<open>evaluation of expr (technical term for smallstep sem.)\<close>
        | Callee locals expr  \<comment> \<open>save callers locals in callee-Frame\<close>
                              \<comment> \<open>(technical term for smallstep semantics)\<close>
and  stmt
        = Skip                  \<comment> \<open>empty      statement\<close>
        | Expr  expr            \<comment> \<open>expression statement\<close>
        | Lab   jump stmt       (\<open>_\<bullet> _\<close> [      99,66]66)
                                \<comment> \<open>labeled statement; handles break\<close>
        | Comp  stmt stmt       (\<open>_;; _\<close>                  [      66,65]65)
        | If'   expr stmt stmt  (\<open>If'(_') _ Else _\<close>       [   80,79,79]70)
        | Loop  label expr stmt (\<open>_\<bullet> While'(_') _\<close>        [   99,80,79]70)
        | Jmp jump              \<comment> \<open>break, continue, return\<close>
        | Throw expr
        | TryC  stmt qtname vname stmt (\<open>Try _ Catch'(_ _') _\<close>  [79,99,80,79]70)
             \<comment> \<open>\<^term>\<open>Try c1 Catch(C vn) c2\<close>\<close> 
             \<comment> \<open>\<open>c1\<close>: block were exception may be thrown\<close>
             \<comment> \<open>\<open>C\<close>:  execption class to catch\<close>
             \<comment> \<open>\<open>vn\<close>: local name for exception used in \<open>c2\<close>\<close>
             \<comment> \<open>\<open>c2\<close>: block to execute when exception is cateched\<close>
        | Fin  stmt  stmt        (\<open>_ Finally _\<close>               [      79,79]70)
        | FinA abopt stmt       \<comment> \<open>Save abruption of first statement\<close> 
                                \<comment> \<open>technical term  for smallstep sem.)\<close>
        | Init  qtname          \<comment> \<open>class initialization\<close>

datatype_compat var expr stmt


text \<open>
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
\<close>
 
type_synonym "term" = "(expr+stmt,var,expr list) sum3"
translations
  (type) "sig"   <= (type) "mname \<times> ty list"
  (type) "term"  <= (type) "(expr+stmt,var,expr list) sum3"

abbreviation this :: expr
  where "this == Acc (LVar This)"

abbreviation LAcc :: "vname \<Rightarrow> expr" (\<open>!!\<close>)
  where "!!v == Acc (LVar (EName (VNam v)))"

abbreviation
  LAss :: "vname \<Rightarrow> expr \<Rightarrow>stmt" (\<open>_:==_\<close> [90,85] 85)
  where "v:==e == Expr (Ass (LVar (EName (VNam  v))) e)"

abbreviation
  Return :: "expr \<Rightarrow> stmt"
  where "Return e == Expr (Ass (LVar (EName Res)) e);; Jmp Ret" \<comment> \<open>\tt Res := e;; Jmp Ret\<close>

abbreviation
  StatRef :: "ref_ty \<Rightarrow> expr"
  where "StatRef rt == Cast (RefT rt) (Lit Null)"
  
definition
  is_stmt :: "term \<Rightarrow> bool"
  where "is_stmt t = (\<exists>c. t=In1r c)"

ML \<open>ML_Thms.bind_thms ("is_stmt_rews", sum3_instantiate \<^context> @{thm is_stmt_def})\<close>

declare is_stmt_rews [simp]

text \<open>
  Here is some syntactic stuff to handle the injections of statements,
  expressions, variables and expression lists into general terms.
\<close>

abbreviation (input)
  expr_inj_term :: "expr \<Rightarrow> term" (\<open>\<langle>_\<rangle>\<^sub>e\<close> 1000)
  where "\<langle>e\<rangle>\<^sub>e == In1l e"

abbreviation (input)
  stmt_inj_term :: "stmt \<Rightarrow> term" (\<open>\<langle>_\<rangle>\<^sub>s\<close> 1000)
  where "\<langle>c\<rangle>\<^sub>s == In1r c"

abbreviation (input)
  var_inj_term :: "var \<Rightarrow> term"  (\<open>\<langle>_\<rangle>\<^sub>v\<close> 1000)
  where "\<langle>v\<rangle>\<^sub>v == In2 v"

abbreviation (input)
  lst_inj_term :: "expr list \<Rightarrow> term" (\<open>\<langle>_\<rangle>\<^sub>l\<close> 1000)
  where "\<langle>es\<rangle>\<^sub>l == In3 es"

text \<open>It seems to be more elegant to have an overloaded injection like the
following.
\<close>

class inj_term =
  fixes inj_term:: "'a \<Rightarrow> term" (\<open>\<langle>_\<rangle>\<close> 1000)

text \<open>How this overloaded injections work can be seen in the theory 
\<open>DefiniteAssignment\<close>. Other big inductive relations on
terms defined in theories \<open>WellType\<close>, \<open>Eval\<close>, \<open>Evaln\<close> and
\<open>AxSem\<close> don't follow this convention right now, but introduce subtle 
syntactic sugar in the relations themselves to make a distinction on 
expressions, statements and so on. So unfortunately you will encounter a 
mixture of dealing with these injections. The abbreviations above are used
as bridge between the different conventions.  
\<close>

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
  apply (rename_tac a, case_tac a)
  apply auto
  done

subsubsection \<open>Evaluation of unary operations\<close>
primrec eval_unop :: "unop \<Rightarrow> val \<Rightarrow> val"
where
  "eval_unop UPlus v = Intg (the_Intg v)"
| "eval_unop UMinus v = Intg (- (the_Intg v))"
| "eval_unop UBitNot v = Intg 42"                \<comment> \<open>FIXME: Not yet implemented\<close>
| "eval_unop UNot v = Bool (\<not> the_Bool v)"

subsubsection \<open>Evaluation of binary operations\<close>
primrec eval_binop :: "binop \<Rightarrow> val \<Rightarrow> val \<Rightarrow> val"
where
  "eval_binop Mul     v1 v2 = Intg ((the_Intg v1) * (the_Intg v2))" 
| "eval_binop Div     v1 v2 = Intg ((the_Intg v1) div (the_Intg v2))"
| "eval_binop Mod     v1 v2 = Intg ((the_Intg v1) mod (the_Intg v2))"
| "eval_binop Plus    v1 v2 = Intg ((the_Intg v1) + (the_Intg v2))"
| "eval_binop Minus   v1 v2 = Intg ((the_Intg v1) - (the_Intg v2))"

\<comment> \<open>Be aware of the explicit coercion of the shift distance to nat\<close>
| "eval_binop LShift  v1 v2 = Intg ((the_Intg v1) *   (2^(nat (the_Intg v2))))"
| "eval_binop RShift  v1 v2 = Intg ((the_Intg v1) div (2^(nat (the_Intg v2))))"
| "eval_binop RShiftU v1 v2 = Intg 42" \<comment> \<open>FIXME: Not yet implemented\<close>

| "eval_binop Less    v1 v2 = Bool ((the_Intg v1) < (the_Intg v2))" 
| "eval_binop Le      v1 v2 = Bool ((the_Intg v1) \<le> (the_Intg v2))"
| "eval_binop Greater v1 v2 = Bool ((the_Intg v2) < (the_Intg v1))"
| "eval_binop Ge      v1 v2 = Bool ((the_Intg v2) \<le> (the_Intg v1))"

| "eval_binop Eq      v1 v2 = Bool (v1=v2)"
| "eval_binop Neq     v1 v2 = Bool (v1\<noteq>v2)"
| "eval_binop BitAnd  v1 v2 = Intg 42" \<comment> \<open>FIXME: Not yet implemented\<close>
| "eval_binop And     v1 v2 = Bool ((the_Bool v1) \<and> (the_Bool v2))"
| "eval_binop BitXor  v1 v2 = Intg 42" \<comment> \<open>FIXME: Not yet implemented\<close>
| "eval_binop Xor     v1 v2 = Bool ((the_Bool v1) \<noteq> (the_Bool v2))"
| "eval_binop BitOr   v1 v2 = Intg 42" \<comment> \<open>FIXME: Not yet implemented\<close>
| "eval_binop Or      v1 v2 = Bool ((the_Bool v1) \<or> (the_Bool v2))"
| "eval_binop CondAnd v1 v2 = Bool ((the_Bool v1) \<and> (the_Bool v2))"
| "eval_binop CondOr  v1 v2 = Bool ((the_Bool v1) \<or> (the_Bool v2))"

definition
  need_second_arg :: "binop \<Rightarrow> val \<Rightarrow> bool" where
  "need_second_arg binop v1 = (\<not> ((binop=CondAnd \<and>  \<not> the_Bool v1) \<or>
                                 (binop=CondOr  \<and> the_Bool v1)))"
text \<open>\<^term>\<open>CondAnd\<close> and \<^term>\<open>CondOr\<close> only evalulate the second argument
 if the value isn't already determined by the first argument\<close>

lemma need_second_arg_CondAnd [simp]: "need_second_arg CondAnd (Bool b) = b" 
by (simp add: need_second_arg_def)

lemma need_second_arg_CondOr [simp]: "need_second_arg CondOr (Bool b) = (\<not> b)" 
by (simp add: need_second_arg_def)

lemma need_second_arg_strict[simp]: 
 "\<lbrakk>binop\<noteq>CondAnd; binop\<noteq>CondOr\<rbrakk> \<Longrightarrow> need_second_arg binop b"
by (cases binop) 
   (simp_all add: need_second_arg_def)
end
