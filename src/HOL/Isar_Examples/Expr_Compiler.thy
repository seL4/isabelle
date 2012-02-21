(*  Title:      HOL/Isar_Examples/Expr_Compiler.thy
    Author:     Markus Wenzel, TU Muenchen

Correctness of a simple expression/stack-machine compiler.
*)

header {* Correctness of a simple expression compiler *}

theory Expr_Compiler
imports Main
begin

text {* This is a (rather trivial) example of program verification.
  We model a compiler for translating expressions to stack machine
  instructions, and prove its correctness wrt.\ some evaluation
  semantics. *}


subsection {* Binary operations *}

text {* Binary operations are just functions over some type of values.
  This is both for abstract syntax and semantics, i.e.\ we use a
  ``shallow embedding'' here. *}

type_synonym 'val binop = "'val => 'val => 'val"


subsection {* Expressions *}

text {* The language of expressions is defined as an inductive type,
  consisting of variables, constants, and binary operations on
  expressions. *}

datatype ('adr, 'val) expr =
    Variable 'adr
  | Constant 'val
  | Binop "'val binop" "('adr, 'val) expr" "('adr, 'val) expr"

text {* Evaluation (wrt.\ some environment of variable assignments) is
  defined by primitive recursion over the structure of expressions. *}

primrec eval :: "('adr, 'val) expr => ('adr => 'val) => 'val"
where
  "eval (Variable x) env = env x"
| "eval (Constant c) env = c"
| "eval (Binop f e1 e2) env = f (eval e1 env) (eval e2 env)"


subsection {* Machine *}

text {* Next we model a simple stack machine, with three
  instructions. *}

datatype ('adr, 'val) instr =
    Const 'val
  | Load 'adr
  | Apply "'val binop"

text {* Execution of a list of stack machine instructions is easily
  defined as follows. *}

primrec exec :: "(('adr, 'val) instr) list => 'val list => ('adr => 'val) => 'val list"
where
  "exec [] stack env = stack"
| "exec (instr # instrs) stack env =
    (case instr of
      Const c => exec instrs (c # stack) env
    | Load x => exec instrs (env x # stack) env
    | Apply f => exec instrs (f (hd stack) (hd (tl stack))
                   # (tl (tl stack))) env)"

definition execute :: "(('adr, 'val) instr) list => ('adr => 'val) => 'val"
  where "execute instrs env = hd (exec instrs [] env)"


subsection {* Compiler *}

text {* We are ready to define the compilation function of expressions
  to lists of stack machine instructions. *}

primrec compile :: "('adr, 'val) expr => (('adr, 'val) instr) list"
where
  "compile (Variable x) = [Load x]"
| "compile (Constant c) = [Const c]"
| "compile (Binop f e1 e2) = compile e2 @ compile e1 @ [Apply f]"


text {* The main result of this development is the correctness theorem
  for @{text compile}.  We first establish a lemma about @{text exec}
  and list append. *}

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
    case Variable show ?case by simp
  next
    case Constant show ?case by simp
  next
    case Binop then show ?case by (simp add: exec_append)
  qed
  then show ?thesis by (simp add: execute_def)
qed


text {* \bigskip In the proofs above, the @{text simp} method does
  quite a lot of work behind the scenes (mostly ``functional program
  execution'').  Subsequently, the same reasoning is elaborated in
  detail --- at most one recursive function definition is used at a
  time.  Thus we get a better idea of what is actually going on. *}

lemma exec_append':
  "exec (xs @ ys) stack env = exec ys (exec xs stack env) env"
proof (induct xs arbitrary: stack)
  case (Nil s)
  have "exec ([] @ ys) s env = exec ys s env" by simp
  also have "... = exec ys (exec [] s env) env" by simp
  finally show ?case .
next
  case (Cons x xs s)
  show ?case
  proof (induct x)
    case (Const val)
    have "exec ((Const val # xs) @ ys) s env = exec (Const val # xs @ ys) s env"
      by simp
    also have "... = exec (xs @ ys) (val # s) env" by simp
    also from Cons have "... = exec ys (exec xs (val # s) env) env" .
    also have "... = exec ys (exec (Const val # xs) s env) env" by simp
    finally show ?case .
  next
    case (Load adr)
    from Cons show ?case by simp -- {* same as above *}
  next
    case (Apply fn)
    have "exec ((Apply fn # xs) @ ys) s env =
        exec (Apply fn # xs @ ys) s env" by simp
    also have "... =
        exec (xs @ ys) (fn (hd s) (hd (tl s)) # (tl (tl s))) env" by simp
    also from Cons have "... =
        exec ys (exec xs (fn (hd s) (hd (tl s)) # tl (tl s)) env) env" .
    also have "... = exec ys (exec (Apply fn # xs) s env) env" by simp
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
    also have "... = env adr # s" by simp
    also have "env adr = eval (Variable adr) env" by simp
    finally show ?case .
  next
    case (Constant val s)
    show ?case by simp -- {* same as above *}
  next
    case (Binop fn e1 e2 s)
    have "exec (compile (Binop fn e1 e2)) s env =
        exec (compile e2 @ compile e1 @ [Apply fn]) s env" by simp
    also have "... = exec [Apply fn]
        (exec (compile e1) (exec (compile e2) s env) env) env"
      by (simp only: exec_append)
    also have "exec (compile e2) s env = eval e2 env # s" by fact
    also have "exec (compile e1) ... env = eval e1 env # ..." by fact
    also have "exec [Apply fn] ... env =
        fn (hd ...) (hd (tl ...)) # (tl (tl ...))" by simp
    also have "... = fn (eval e1 env) (eval e2 env) # s" by simp
    also have "fn (eval e1 env) (eval e2 env) =
        eval (Binop fn e1 e2) env"
      by simp
    finally show ?case .
  qed

  have "execute (compile e) env = hd (exec (compile e) [] env)"
    by (simp add: execute_def)
  also from exec_compile have "exec (compile e) [] env = [eval e env]" .
  also have "hd ... = eval e env" by simp
  finally show ?thesis .
qed

end
