(*  Title:      HOL/Isar_examples/ExprCompiler.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Correctness of a simple expression/stack-machine compiler.
*)

theory ExprCompiler = Main:;

title {* Correctness of a simple expression/stack-machine compiler *};


section {* Basics *};

text {*
 First we define a type abbreviation for binary operations over some
 type @{type "'val"} of values.
*};

types
  'val binop = "'val => 'val => 'val";


section {* Machine *};

text {*
 Next we model a simple stack machine, with three instructions.
*};

datatype ('adr, 'val) instr =
  Const 'val |
  Load 'adr |
  Apply "'val binop";

text {*
 Execution of a list of stack machine instructions is
 straight-forward.
*};

consts
  exec :: "(('adr, 'val) instr) list => 'val list => ('adr => 'val) => 'val list";

primrec
  "exec [] stack env = stack"
  "exec (instr # instrs) stack env =
    (case instr of
      Const c => exec instrs (c # stack) env
    | Load x => exec instrs (env x # stack) env
    | Apply f => exec instrs (f (hd stack) (hd (tl stack)) # (tl (tl stack))) env)";

constdefs
  execute :: "(('adr, 'val) instr) list => ('adr => 'val) => 'val"
  "execute instrs env == hd (exec instrs [] env)";


section {* Expressions *};

text {*
 We introduce a simple language of expressions: variables ---
 constants --- binary operations.
*};

datatype ('adr, 'val) expr =
  Variable 'adr |
  Constant 'val |
  Binop "'val binop" "('adr, 'val) expr" "('adr, 'val) expr";

text {*
 Evaluation of expressions does not do any unexpected things.
*};

consts
  eval :: "('adr, 'val) expr => ('adr => 'val) => 'val";

primrec
  "eval (Variable x) env = env x"
  "eval (Constant c) env = c"
  "eval (Binop f e1 e2) env = f (eval e1 env) (eval e2 env)";


section {* Compiler *};

text {*
 So we are ready to define the compilation function of expressions to
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
 @{term "comp"}.  We first establish some lemmas.
*};

lemma exec_append:
  "ALL stack. exec (xs @ ys) stack env = exec ys (exec xs stack env) env" (is "??P xs");
proof (induct ??P xs type: list);
  show "??P []"; by simp;

  fix x xs;
  assume "??P xs";
  show "??P (x # xs)" (is "??Q x");
  proof (induct ??Q x type: instr);
    fix val; show "??Q (Const val)"; by brute_force;
    next;
    fix adr; show "??Q (Load adr)"; by brute_force;
    next;
    fix fun; show "??Q (Apply fun)"; by brute_force;
  qed;
qed;

lemma exec_comp:
  "ALL stack. exec (comp e) stack env = eval e env # stack" (is "??P e");
proof (induct ??P e type: expr);

  fix adr; show "??P (Variable adr)"; by brute_force;
  next;
  fix val; show "??P (Constant val)"; by brute_force;
  next;
  fix fun e1 e2; assume "??P e1" "??P e2"; show "??P (Binop fun e1 e2)";
    by (brute_force simp add: exec_append);
qed;


text {* Main theorem ahead. *};

theorem correctness: "execute (comp e) env = eval e env";
  by (simp add: execute_def exec_comp);


end;
