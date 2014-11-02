(*  Title:      HOL/Isar_Examples/Expr_Compiler.thy
    Author:     Markus Wenzel, TU Muenchen

Correctness of a simple expression/stack-machine compiler.
*)

section \<open>Correctness of a simple expression compiler\<close>

theory Expr_Compiler
imports Main
begin

text \<open>This is a (rather trivial) example of program verification.
  We model a compiler for translating expressions to stack machine
  instructions, and prove its correctness wrt.\ some evaluation
  semantics.\<close>


subsection \<open>Binary operations\<close>

text \<open>Binary operations are just functions over some type of values.
  This is both for abstract syntax and semantics, i.e.\ we use a
  ``shallow embedding'' here.\<close>

type_synonym 'val binop = "'val \<Rightarrow> 'val \<Rightarrow> 'val"


subsection \<open>Expressions\<close>

text \<open>The language of expressions is defined as an inductive type,
  consisting of variables, constants, and binary operations on
  expressions.\<close>

datatype (dead 'adr, dead 'val) expr =
    Variable 'adr
  | Constant 'val
  | Binop "'val binop" "('adr, 'val) expr" "('adr, 'val) expr"

text \<open>Evaluation (wrt.\ some environment of variable assignments) is
  defined by primitive recursion over the structure of expressions.\<close>

primrec eval :: "('adr, 'val) expr \<Rightarrow> ('adr \<Rightarrow> 'val) \<Rightarrow> 'val"
where
  "eval (Variable x) env = env x"
| "eval (Constant c) env = c"
| "eval (Binop f e1 e2) env = f (eval e1 env) (eval e2 env)"


subsection \<open>Machine\<close>

text \<open>Next we model a simple stack machine, with three
  instructions.\<close>

datatype (dead 'adr, dead 'val) instr =
    Const 'val
  | Load 'adr
  | Apply "'val binop"

text \<open>Execution of a list of stack machine instructions is easily
  defined as follows.\<close>

primrec exec :: "(('adr, 'val) instr) list \<Rightarrow> 'val list \<Rightarrow> ('adr \<Rightarrow> 'val) \<Rightarrow> 'val list"
where
  "exec [] stack env = stack"
| "exec (instr # instrs) stack env =
    (case instr of
      Const c \<Rightarrow> exec instrs (c # stack) env
    | Load x \<Rightarrow> exec instrs (env x # stack) env
    | Apply f \<Rightarrow> exec instrs (f (hd stack) (hd (tl stack))
                   # (tl (tl stack))) env)"

definition execute :: "(('adr, 'val) instr) list \<Rightarrow> ('adr \<Rightarrow> 'val) \<Rightarrow> 'val"
  where "execute instrs env = hd (exec instrs [] env)"


subsection \<open>Compiler\<close>

text \<open>We are ready to define the compilation function of expressions
  to lists of stack machine instructions.\<close>

primrec compile :: "('adr, 'val) expr \<Rightarrow> (('adr, 'val) instr) list"
where
  "compile (Variable x) = [Load x]"
| "compile (Constant c) = [Const c]"
| "compile (Binop f e1 e2) = compile e2 @ compile e1 @ [Apply f]"


text \<open>The main result of this development is the correctness theorem
  for @{text compile}.  We first establish a lemma about @{text exec}
  and list append.\<close>

lemma exec_append:
  "exec (xs @ ys) stack env =
    exec ys (exec xs stack env) env"
proof (induct xs arbitrary: stack)
  case Nil
  show ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (induct x)
    case Const
    from Cons show ?case by simp
  next
    case Load
    from Cons show ?case by simp
  next
    case Apply
    from Cons show ?case by simp
  qed
qed

theorem correctness: "execute (compile e) env = eval e env"
proof -
  have "\<And>stack. exec (compile e) stack env = eval e env # stack"
  proof (induct e)
    case Variable
    show ?case by simp
  next
    case Constant
    show ?case by simp
  next
    case Binop
    then show ?case by (simp add: exec_append)
  qed
  then show ?thesis by (simp add: execute_def)
qed


text \<open>\bigskip In the proofs above, the @{text simp} method does
  quite a lot of work behind the scenes (mostly ``functional program
  execution'').  Subsequently, the same reasoning is elaborated in
  detail --- at most one recursive function definition is used at a
  time.  Thus we get a better idea of what is actually going on.\<close>

lemma exec_append':
  "exec (xs @ ys) stack env = exec ys (exec xs stack env) env"
proof (induct xs arbitrary: stack)
  case (Nil s)
  have "exec ([] @ ys) s env = exec ys s env"
    by simp
  also have "\<dots> = exec ys (exec [] s env) env"
    by simp
  finally show ?case .
next
  case (Cons x xs s)
  show ?case
  proof (induct x)
    case (Const val)
    have "exec ((Const val # xs) @ ys) s env = exec (Const val # xs @ ys) s env"
      by simp
    also have "\<dots> = exec (xs @ ys) (val # s) env"
      by simp
    also from Cons have "\<dots> = exec ys (exec xs (val # s) env) env" .
    also have "\<dots> = exec ys (exec (Const val # xs) s env) env"
      by simp
    finally show ?case .
  next
    case (Load adr)
    from Cons show ?case
      by simp -- \<open>same as above\<close>
  next
    case (Apply fn)
    have "exec ((Apply fn # xs) @ ys) s env =
        exec (Apply fn # xs @ ys) s env" by simp
    also have "\<dots> =
        exec (xs @ ys) (fn (hd s) (hd (tl s)) # (tl (tl s))) env"
      by simp
    also from Cons have "\<dots> =
        exec ys (exec xs (fn (hd s) (hd (tl s)) # tl (tl s)) env) env" .
    also have "\<dots> = exec ys (exec (Apply fn # xs) s env) env"
      by simp
    finally show ?case .
  qed
qed

theorem correctness': "execute (compile e) env = eval e env"
proof -
  have exec_compile: "\<And>stack. exec (compile e) stack env = eval e env # stack"
  proof (induct e)
    case (Variable adr s)
    have "exec (compile (Variable adr)) s env = exec [Load adr] s env"
      by simp
    also have "\<dots> = env adr # s"
      by simp
    also have "env adr = eval (Variable adr) env"
      by simp
    finally show ?case .
  next
    case (Constant val s)
    show ?case by simp -- \<open>same as above\<close>
  next
    case (Binop fn e1 e2 s)
    have "exec (compile (Binop fn e1 e2)) s env =
        exec (compile e2 @ compile e1 @ [Apply fn]) s env"
      by simp
    also have "\<dots> = exec [Apply fn]
        (exec (compile e1) (exec (compile e2) s env) env) env"
      by (simp only: exec_append)
    also have "exec (compile e2) s env = eval e2 env # s"
      by fact
    also have "exec (compile e1) \<dots> env = eval e1 env # \<dots>"
      by fact
    also have "exec [Apply fn] \<dots> env =
        fn (hd \<dots>) (hd (tl \<dots>)) # (tl (tl \<dots>))"
      by simp
    also have "\<dots> = fn (eval e1 env) (eval e2 env) # s"
      by simp
    also have "fn (eval e1 env) (eval e2 env) =
        eval (Binop fn e1 e2) env"
      by simp
    finally show ?case .
  qed

  have "execute (compile e) env = hd (exec (compile e) [] env)"
    by (simp add: execute_def)
  also from exec_compile have "exec (compile e) [] env = [eval e env]" .
  also have "hd \<dots> = eval e env"
    by simp
  finally show ?thesis .
qed

end
