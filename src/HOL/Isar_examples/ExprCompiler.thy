(*  Title:      HOL/Isar_examples/ExprCompiler.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Correctness of a simple expression/stack-machine compiler.
*)

header {* Correctness of a simple expression compiler *};

theory ExprCompiler = Main:;

text {*
 This is a (quite trivial) example of program verification.  We model
 a compiler translating expressions to stack machine instructions, and
 prove its correctness wrt.\ evaluation semantics.
*};


subsection {* Binary operations *};

text {*
 Binary operations are just functions over some type of values.  This
 is both for syntax and semantics, i.e.\ we use a ``shallow
 embedding''.
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
 Evaluation (wrt.\ an environment) is defined by primitive recursion
 over the structure of expressions.
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
  comp :: "('adr, 'val) expr => (('adr, 'val) instr) list";

primrec
  "comp (Variable x) = [Load x]"
  "comp (Constant c) = [Const c]"
  "comp (Binop f e1 e2) = comp e2 @ comp e1 @ [Apply f]";


text {*
  The main result of this development is the correctness theorem for
  $\idt{comp}$.  We first establish some lemmas about $\idt{exec}$.
*};

lemma exec_append:
  "ALL stack. exec (xs @ ys) stack env =
    exec ys (exec xs stack env) env" (is "?P xs");
proof (induct ?P xs type: list);
  show "?P []"; by simp;

  fix x xs;
  assume "?P xs";
  show "?P (x # xs)" (is "?Q x");
  proof (induct ?Q x type: instr);
    fix val; show "?Q (Const val)"; by (simp!);
  next;
    fix adr; show "?Q (Load adr)"; by (simp!);
  next;
    fix fun; show "?Q (Apply fun)"; by (simp!);
  qed;
qed;

lemma exec_comp:
  "ALL stack. exec (comp e) stack env =
    eval e env # stack" (is "?P e");
proof (induct ?P e type: expr);
  fix adr; show "?P (Variable adr)"; by (simp!);
next;
  fix val; show "?P (Constant val)"; by (simp!);
next;
  fix fun e1 e2; assume "?P e1" "?P e2"; show "?P (Binop fun e1 e2)";
    by (simp! add: exec_append);
qed;


text {* Main theorem ahead. *};

theorem correctness: "execute (comp e) env = eval e env";
  by (simp add: execute_def exec_comp);

end;
