(*<*)
theory CodeGen imports Main begin
(*>*)

section{*Case Study: Compiling Expressions*}

text{*\label{sec:ExprCompiler}
\index{compiling expressions example|(}%
The task is to develop a compiler from a generic type of expressions (built
from variables, constants and binary operations) to a stack machine.  This
generic type of expressions is a generalization of the boolean expressions in
\S\ref{sec:boolex}.  This time we do not commit ourselves to a particular
type of variables or values but make them type parameters.  Neither is there
a fixed set of binary operations: instead the expression contains the
appropriate function itself.
*}

type_synonym 'v binop = "'v \<Rightarrow> 'v \<Rightarrow> 'v";
datatype ('a,'v)expr = Cex 'v
                     | Vex 'a
                     | Bex "'v binop"  "('a,'v)expr"  "('a,'v)expr";

text{*\noindent
The three constructors represent constants, variables and the application of
a binary operation to two subexpressions.

The value of an expression with respect to an environment that maps variables to
values is easily defined:
*}

primrec "value" :: "('a,'v)expr \<Rightarrow> ('a \<Rightarrow> 'v) \<Rightarrow> 'v" where
"value (Cex v) env = v" |
"value (Vex a) env = env a" |
"value (Bex f e1 e2) env = f (value e1 env) (value e2 env)"

text{*
The stack machine has three instructions: load a constant value onto the
stack, load the contents of an address onto the stack, and apply a
binary operation to the two topmost elements of the stack, replacing them by
the result. As for @{text"expr"}, addresses and values are type parameters:
*}

datatype ('a,'v) instr = Const 'v
                       | Load 'a
                       | Apply "'v binop";

text{*
The execution of the stack machine is modelled by a function
@{text"exec"} that takes a list of instructions, a store (modelled as a
function from addresses to values, just like the environment for
evaluating expressions), and a stack (modelled as a list) of values,
and returns the stack at the end of the execution --- the store remains
unchanged:
*}

primrec exec :: "('a,'v)instr list \<Rightarrow> ('a\<Rightarrow>'v) \<Rightarrow> 'v list \<Rightarrow> 'v list"
where
"exec [] s vs = vs" |
"exec (i#is) s vs = (case i of
    Const v  \<Rightarrow> exec is s (v#vs)
  | Load a   \<Rightarrow> exec is s ((s a)#vs)
  | Apply f  \<Rightarrow> exec is s ((f (hd vs) (hd(tl vs)))#(tl(tl vs))))"

text{*\noindent
Recall that @{term"hd"} and @{term"tl"}
return the first element and the remainder of a list.
Because all functions are total, \cdx{hd} is defined even for the empty
list, although we do not know what the result is. Thus our model of the
machine always terminates properly, although the definition above does not
tell us much about the result in situations where @{term"Apply"} was executed
with fewer than two elements on the stack.

The compiler is a function from expressions to a list of instructions. Its
definition is obvious:
*}

primrec compile :: "('a,'v)expr \<Rightarrow> ('a,'v)instr list" where
"compile (Cex v)       = [Const v]" |
"compile (Vex a)       = [Load a]" |
"compile (Bex f e1 e2) = (compile e2) @ (compile e1) @ [Apply f]"

text{*
Now we have to prove the correctness of the compiler, i.e.\ that the
execution of a compiled expression results in the value of the expression:
*}
theorem "exec (compile e) s [] = [value e s]";
(*<*)oops;(*>*)
text{*\noindent
This theorem needs to be generalized:
*}

theorem "\<forall>vs. exec (compile e) s vs = (value e s) # vs";

txt{*\noindent
It will be proved by induction on @{term"e"} followed by simplification.  
First, we must prove a lemma about executing the concatenation of two
instruction sequences:
*}
(*<*)oops;(*>*)
lemma exec_app[simp]:
  "\<forall>vs. exec (xs@ys) s vs = exec ys s (exec xs s vs)"; 

txt{*\noindent
This requires induction on @{term"xs"} and ordinary simplification for the
base cases. In the induction step, simplification leaves us with a formula
that contains two @{text"case"}-expressions over instructions. Thus we add
automatic case splitting, which finishes the proof:
*}
apply(induct_tac xs, simp, simp split: instr.split);
(*<*)done(*>*)
text{*\noindent
Note that because both \methdx{simp_all} and \methdx{auto} perform simplification, they can
be modified in the same way as @{text simp}.  Thus the proof can be
rewritten as
*}
(*<*)
declare exec_app[simp del];
lemma [simp]: "\<forall>vs. exec (xs@ys) s vs = exec ys s (exec xs s vs)"; 
(*>*)
apply(induct_tac xs, simp_all split: instr.split);
(*<*)done(*>*)
text{*\noindent
Although this is more compact, it is less clear for the reader of the proof.

We could now go back and prove @{prop"exec (compile e) s [] = [value e s]"}
merely by simplification with the generalized version we just proved.
However, this is unnecessary because the generalized version fully subsumes
its instance.%
\index{compiling expressions example|)}
*}
(*<*)
theorem "\<forall>vs. exec (compile e) s vs = (value e s) # vs";
by(induct_tac e, auto);
end
(*>*)
