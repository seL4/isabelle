(*  Title:      HOL/Isar_examples/ExprCompiler.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Correctness of a simple expression/stack-machine compiler.
*)

header {* Correctness of a simple expression compiler *};

theory ExprCompiler = Main:;

text {*
 This is a (rather trivial) example of program verification.  We model
 a compiler for translating expressions to stack machine instructions,
 and prove its correctness wrt.\ some evaluation semantics.
*};


subsection {* Binary operations *};

text {*
 Binary operations are just functions over some type of values.  This
 is both for abstract syntax and semantics, i.e.\ we use a ``shallow
 embedding'' here.
*};

types
  'val binop = "'val => 'val => 'val";


subsection {* Expressions *};

text {*
 The language of expressions is defined as an inductive type,
 consisting of variables, constants, and binary operations on
 expressions.
*};

datatype ('adr, 'val) expr =
  Variable 'adr |
  Constant 'val |
  Binop "'val binop" "('adr, 'val) expr" "('adr, 'val) expr";

text {*
 Evaluation (wrt.\ some environment of variable assignments) is
 defined by primitive recursion over the structure of expressions.
*};

consts
  eval :: "('adr, 'val) expr => ('adr => 'val) => 'val";

primrec
  "eval (Variable x) env = env x"
  "eval (Constant c) env = c"
  "eval (Binop f e1 e2) env = f (eval e1 env) (eval e2 env)";


subsection {* Machine *};

text {*
 Next we model a simple stack machine, with three instructions.
*};

datatype ('adr, 'val) instr =
  Const 'val |
  Load 'adr |
  Apply "'val binop";

text {*
 Execution of a list of stack machine instructions is easily defined
 as follows.
*};

consts
  exec :: "(('adr, 'val) instr) list
    => 'val list => ('adr => 'val) => 'val list";

primrec
  "exec [] stack env = stack"
  "exec (instr # instrs) stack env =
    (case instr of
      Const c => exec instrs (c # stack) env
    | Load x => exec instrs (env x # stack) env
    | Apply f => exec instrs (f (hd stack) (hd (tl stack))
                   # (tl (tl stack))) env)";

constdefs
  execute :: "(('adr, 'val) instr) list => ('adr => 'val) => 'val"
  "execute instrs env == hd (exec instrs [] env)";


subsection {* Compiler *};

text {*
 We are ready to define the compilation function of expressions to
 lists of stack machine instructions.
*};

consts
  compile :: "('adr, 'val) expr => (('adr, 'val) instr) list";

primrec
  "compile (Variable x) = [Load x]"
  "compile (Constant c) = [Const c]"
  "compile (Binop f e1 e2) = compile e2 @ compile e1 @ [Apply f]";


text {*
 The main result of this development is the correctness theorem for
 $\idt{compile}$.  We first establish a lemma about $\idt{exec}$ and
 list append.
*};

lemma exec_append:
  "ALL stack. exec (xs @ ys) stack env =
    exec ys (exec xs stack env) env" (is "?P xs");
proof (induct ?P xs in type: list);
  show "?P []"; by simp;

  fix x xs; assume "?P xs";
  show "?P (x # xs)" (is "?Q x");
  proof (induct ?Q x in type: instr);
    show "!!val. ?Q (Const val)"; by (simp!);
    show "!!adr. ?Q (Load adr)"; by (simp!);
    show "!!fun. ?Q (Apply fun)"; by (simp!);
  qed;
qed;

theorem correctness: "execute (compile e) env = eval e env";
proof -;
  have "ALL stack. exec (compile e) stack env =
    eval e env # stack" (is "?P e");
  proof (induct ?P e in type: expr);
    show "!!adr. ?P (Variable adr)"; by simp;
    show "!!val. ?P (Constant val)"; by simp;
    show "!!fun e1 e2. (?P e1 ==> ?P e2 ==> ?P (Binop fun e1 e2))";
      by (simp add: exec_append);
  qed;
  thus ?thesis; by (simp add: execute_def);
qed;


text {*
 \bigskip In the proofs above, the \name{simp} method does quite a lot
 of work behind the scenes (mostly ``functional program execution'').
 Subsequently, the same reasoning is elaborated in detail --- at most
 one recursive function definition is used at a time.  Thus we get a
 better idea of what is actually going on.
*};

lemma exec_append:
  "ALL stack. exec (xs @ ys) stack env
    = exec ys (exec xs stack env) env" (is "?P xs");
proof (induct ?P xs);
  show "?P []" (is "ALL s. ?Q s");
  proof;
    fix s; have "exec ([] @ ys) s env = exec ys s env"; by simp;
    also; have "... = exec ys (exec [] s env) env"; by simp;
    finally; show "?Q s"; .;
  qed;
  fix x xs; assume hyp: "?P xs";
  show "?P (x # xs)";
  proof (induct x);
    fix val;
    show "?P (Const val # xs)" (is "ALL s. ?Q s");
    proof;
      fix s;
      have "exec ((Const val # xs) @ ys) s env =
          exec (Const val # xs @ ys) s env";
        by simp;
      also; have "... = exec (xs @ ys) (val # s) env"; by simp;
      also; from hyp; have "... = exec ys (exec xs (val # s) env) env"; ..;
      also; have "... = exec ys (exec (Const val # xs) s env) env";
        by simp;
      finally; show "?Q s"; .;
    qed;
  next;
    fix adr; from hyp; show "?P (Load adr # xs)"; by simp -- {* same as above *};
  next;
    fix fun;
    show "?P (Apply fun # xs)" (is "ALL s. ?Q s");
    proof;
      fix s;
      have "exec ((Apply fun # xs) @ ys) s env =
          exec (Apply fun # xs @ ys) s env";
        by simp;
      also; have "... =
          exec (xs @ ys) (fun (hd s) (hd (tl s)) # (tl (tl s))) env";
        by simp;
      also; from hyp; have "... =
        exec ys (exec xs (fun (hd s) (hd (tl s)) # tl (tl s)) env) env"; ..;
      also; have "... = exec ys (exec (Apply fun # xs) s env) env"; by simp;
      finally; show "?Q s"; .;
    qed;
  qed;
qed;

theorem correctness: "execute (compile e) env = eval e env";
proof -;
  have exec_compile:
  "ALL stack. exec (compile e) stack env = eval e env # stack" (is "?P e");
  proof (induct e);
    fix adr; show "?P (Variable adr)" (is "ALL s. ?Q s");
    proof;
      fix s;
      have "exec (compile (Variable adr)) s env = exec [Load adr] s env";
        by simp;
      also; have "... = env adr # s"; by simp;
      also; have "env adr = eval (Variable adr) env"; by simp;
      finally; show "?Q s"; .;
    qed;
  next;
    fix val; show "?P (Constant val)"; by simp -- {* same as above *};
  next;
    fix fun e1 e2; assume hyp1: "?P e1" and hyp2: "?P e2";
    show "?P (Binop fun e1 e2)" (is "ALL s. ?Q s");
    proof;
      fix s; have "exec (compile (Binop fun e1 e2)) s env
        = exec (compile e2 @ compile e1 @ [Apply fun]) s env"; by simp;
      also; have "... =
          exec [Apply fun] (exec (compile e1) (exec (compile e2) s env) env) env";
        by (simp only: exec_append);
      also; from hyp2; have "exec (compile e2) s env = eval e2 env # s"; ..;
      also; from hyp1; have "exec (compile e1) ... env = eval e1 env # ..."; ..;
      also; have "exec [Apply fun] ... env =
        fun (hd ...) (hd (tl ...)) # (tl (tl ...))"; by simp;
      also; have "... = fun (eval e1 env) (eval e2 env) # s"; by simp;
      also; have "fun (eval e1 env) (eval e2 env) = eval (Binop fun e1 e2) env";
        by simp;
      finally; show "?Q s"; .;
    qed;
  qed;

  have "execute (compile e) env = hd (exec (compile e) [] env)";
    by (simp add: execute_def);
  also; from exec_compile; have "exec (compile e) [] env = [eval e env]"; ..;
  also; have "hd ... = eval e env"; by simp;
  finally; show ?thesis; .;
qed;

end;
