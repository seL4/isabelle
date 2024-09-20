theory Examples
imports Main "HOL-Library.Predicate_Compile_Alternative_Defs"
begin

declare [[values_timeout = 480.0]]

section \<open>Formal Languages\<close>

subsection \<open>General Context Free Grammars\<close>

text \<open>a contribution by Aditi Barthwal\<close>

datatype ('nts,'ts) symbol = NTS 'nts
                            | TS 'ts

                            
datatype ('nts,'ts) rule = rule 'nts "('nts,'ts) symbol list"

type_synonym ('nts,'ts) grammar = "('nts,'ts) rule set * 'nts"

fun rules :: "('nts,'ts) grammar => ('nts,'ts) rule set"
where
  "rules (r, s) = r"

definition derives 
where
"derives g = { (lsl,rsl). \<exists>s1 s2 lhs rhs. 
                         (s1 @ [NTS lhs] @ s2 = lsl) \<and>
                         (s1 @ rhs @ s2) = rsl \<and>
                         (rule lhs rhs) \<in> fst g }"

definition derivesp ::
  "(('nts, 'ts) rule => bool) * 'nts => ('nts, 'ts) symbol list => ('nts, 'ts) symbol list => bool"
where
  "derivesp g = (\<lambda> lhs rhs. (lhs, rhs) \<in> derives (Collect (fst g), snd g))"
 
lemma [code_pred_def]:
  "derivesp g = (\<lambda> lsl rsl. \<exists>s1 s2 lhs rhs. 
                         (s1 @ [NTS lhs] @ s2 = lsl) \<and>
                         (s1 @ rhs @ s2) = rsl \<and>
                         (fst g) (rule lhs rhs))"
unfolding derivesp_def derives_def by auto

abbreviation "example_grammar == 
({ rule ''S'' [NTS ''A'', NTS ''B''],
   rule ''S'' [TS ''a''],
  rule ''A'' [TS ''b'']}, ''S'')"

definition "example_rules == 
(%x. x = rule ''S'' [NTS ''A'', NTS ''B''] \<or>
   x = rule ''S'' [TS ''a''] \<or>
  x = rule ''A'' [TS ''b''])"


code_pred [inductify, skip_proof] derivesp .

thm derivesp.equation

definition "testp = (% rhs. derivesp (example_rules, ''S'') [NTS ''S''] rhs)"

code_pred (modes: o \<Rightarrow> bool) [inductify] testp .
thm testp.equation

values "{rhs. testp rhs}"

declare rtranclp.intros(1)[code_pred_def] converse_rtranclp_into_rtranclp[code_pred_def]

code_pred [inductify] rtranclp .

definition "test2 = (\<lambda> rhs. rtranclp (derivesp (example_rules, ''S'')) [NTS ''S''] rhs)"

code_pred [inductify, skip_proof] test2 .

values "{rhs. test2 rhs}"

subsection \<open>Some concrete Context Free Grammars\<close>

datatype alphabet = a | b

inductive_set S\<^sub>1 and A\<^sub>1 and B\<^sub>1 where
  "[] \<in> S\<^sub>1"
| "w \<in> A\<^sub>1 \<Longrightarrow> b # w \<in> S\<^sub>1"
| "w \<in> B\<^sub>1 \<Longrightarrow> a # w \<in> S\<^sub>1"
| "w \<in> S\<^sub>1 \<Longrightarrow> a # w \<in> A\<^sub>1"
| "w \<in> S\<^sub>1 \<Longrightarrow> b # w \<in> S\<^sub>1"
| "\<lbrakk>v \<in> B\<^sub>1; v \<in> B\<^sub>1\<rbrakk> \<Longrightarrow> a # v @ w \<in> B\<^sub>1"

code_pred [inductify] S\<^sub>1p .
code_pred [random_dseq inductify] S\<^sub>1p .
thm S\<^sub>1p.equation
thm S\<^sub>1p.random_dseq_equation

values [random_dseq 5, 5, 5] 5 "{x. S\<^sub>1p x}"

inductive_set S\<^sub>2 and A\<^sub>2 and B\<^sub>2 where
  "[] \<in> S\<^sub>2"
| "w \<in> A\<^sub>2 \<Longrightarrow> b # w \<in> S\<^sub>2"
| "w \<in> B\<^sub>2 \<Longrightarrow> a # w \<in> S\<^sub>2"
| "w \<in> S\<^sub>2 \<Longrightarrow> a # w \<in> A\<^sub>2"
| "w \<in> S\<^sub>2 \<Longrightarrow> b # w \<in> B\<^sub>2"
| "\<lbrakk>v \<in> B\<^sub>2; v \<in> B\<^sub>2\<rbrakk> \<Longrightarrow> a # v @ w \<in> B\<^sub>2"

code_pred [random_dseq inductify] S\<^sub>2p .
thm S\<^sub>2p.random_dseq_equation
thm A\<^sub>2p.random_dseq_equation
thm B\<^sub>2p.random_dseq_equation

values [random_dseq 5, 5, 5] 10 "{x. S\<^sub>2p x}"

inductive_set S\<^sub>3 and A\<^sub>3 and B\<^sub>3 where
  "[] \<in> S\<^sub>3"
| "w \<in> A\<^sub>3 \<Longrightarrow> b # w \<in> S\<^sub>3"
| "w \<in> B\<^sub>3 \<Longrightarrow> a # w \<in> S\<^sub>3"
| "w \<in> S\<^sub>3 \<Longrightarrow> a # w \<in> A\<^sub>3"
| "w \<in> S\<^sub>3 \<Longrightarrow> b # w \<in> B\<^sub>3"
| "\<lbrakk>v \<in> B\<^sub>3; w \<in> B\<^sub>3\<rbrakk> \<Longrightarrow> a # v @ w \<in> B\<^sub>3"

code_pred [inductify, skip_proof] S\<^sub>3p .
thm S\<^sub>3p.equation

values 10 "{x. S\<^sub>3p x}"

inductive_set S\<^sub>4 and A\<^sub>4 and B\<^sub>4 where
  "[] \<in> S\<^sub>4"
| "w \<in> A\<^sub>4 \<Longrightarrow> b # w \<in> S\<^sub>4"
| "w \<in> B\<^sub>4 \<Longrightarrow> a # w \<in> S\<^sub>4"
| "w \<in> S\<^sub>4 \<Longrightarrow> a # w \<in> A\<^sub>4"
| "\<lbrakk>v \<in> A\<^sub>4; w \<in> A\<^sub>4\<rbrakk> \<Longrightarrow> b # v @ w \<in> A\<^sub>4"
| "w \<in> S\<^sub>4 \<Longrightarrow> b # w \<in> B\<^sub>4"
| "\<lbrakk>v \<in> B\<^sub>4; w \<in> B\<^sub>4\<rbrakk> \<Longrightarrow> a # v @ w \<in> B\<^sub>4"

code_pred (expected_modes: o => bool, i => bool) S\<^sub>4p .

hide_const a b

section \<open>Semantics of programming languages\<close>

subsection \<open>IMP\<close>

type_synonym var = nat
type_synonym state = "int list"

datatype com =
  Skip |
  Ass var "state => int" |
  Seq com com |
  IF "state => bool" com com |
  While "state => bool" com

inductive exec :: "com => state => state => bool" where
"exec Skip s s" |
"exec (Ass x e) s (s[x := e(s)])" |
"exec c1 s1 s2 ==> exec c2 s2 s3 ==> exec (Seq c1 c2) s1 s3" |
"b s ==> exec c1 s t ==> exec (IF b c1 c2) s t" |
"~b s ==> exec c2 s t ==> exec (IF b c1 c2) s t" |
"~b s ==> exec (While b c) s s" |
"b s1 ==> exec c s1 s2 ==> exec (While b c) s2 s3 ==> exec (While b c) s1 s3"

code_pred exec .

values "{t. exec
 (While (%s. s!0 > 0) (Seq (Ass 0 (%s. s!0 - 1)) (Ass 1 (%s. s!1 + 1))))
 [3,5] t}"

subsection \<open>Lambda\<close>

datatype type =
    Atom nat
  | Fun type type    (infixr \<open>\<Rightarrow>\<close> 200)

datatype dB =
    Var nat
  | App dB dB (infixl \<open>\<degree>\<close> 200)
  | Abs type dB

primrec
  nth_el :: "'a list \<Rightarrow> nat \<Rightarrow> 'a option" (\<open>_\<langle>_\<rangle>\<close> [90, 0] 91)
where
  "[]\<langle>i\<rangle> = None"
| "(x # xs)\<langle>i\<rangle> = (case i of 0 \<Rightarrow> Some x | Suc j \<Rightarrow> xs \<langle>j\<rangle>)"

inductive nth_el' :: "'a list \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> bool"
where
  "nth_el' (x # xs) 0 x"
| "nth_el' xs i y \<Longrightarrow> nth_el' (x # xs) (Suc i) y"

inductive typing :: "type list \<Rightarrow> dB \<Rightarrow> type \<Rightarrow> bool"  (\<open>_ \<turnstile> _ : _\<close> [50, 50, 50] 50)
  where
    Var [intro!]: "nth_el' env x T \<Longrightarrow> env \<turnstile> Var x : T"
  | Abs [intro!]: "T # env \<turnstile> t : U \<Longrightarrow> env \<turnstile> Abs T t : (T \<Rightarrow> U)"
  | App [intro!]: "env \<turnstile> s : T \<Rightarrow> U \<Longrightarrow> env \<turnstile> t : T \<Longrightarrow> env \<turnstile> (s \<degree> t) : U"

primrec
  lift :: "[dB, nat] => dB"
where
    "lift (Var i) k = (if i < k then Var i else Var (i + 1))"
  | "lift (s \<degree> t) k = lift s k \<degree> lift t k"
  | "lift (Abs T s) k = Abs T (lift s (k + 1))"

primrec
  subst :: "[dB, dB, nat] => dB"  (\<open>_[_'/_]\<close> [300, 0, 0] 300)
where
    subst_Var: "(Var i)[s/k] =
      (if k < i then Var (i - 1) else if i = k then s else Var i)"
  | subst_App: "(t \<degree> u)[s/k] = t[s/k] \<degree> u[s/k]"
  | subst_Abs: "(Abs T t)[s/k] = Abs T (t[lift s 0 / k+1])"

inductive beta :: "[dB, dB] => bool"  (infixl \<open>\<rightarrow>\<^sub>\<beta>\<close> 50)
  where
    beta [simp, intro!]: "Abs T s \<degree> t \<rightarrow>\<^sub>\<beta> s[t/0]"
  | appL [simp, intro!]: "s \<rightarrow>\<^sub>\<beta> t ==> s \<degree> u \<rightarrow>\<^sub>\<beta> t \<degree> u"
  | appR [simp, intro!]: "s \<rightarrow>\<^sub>\<beta> t ==> u \<degree> s \<rightarrow>\<^sub>\<beta> u \<degree> t"
  | abs [simp, intro!]: "s \<rightarrow>\<^sub>\<beta> t ==> Abs T s \<rightarrow>\<^sub>\<beta> Abs T t"

code_pred (expected_modes: i => i => o => bool, i => i => i => bool) typing .
thm typing.equation

code_pred (modes: i => i => bool,  i => o => bool as reduce') beta .
thm beta.equation

values "{x. App (Abs (Atom 0) (Var 0)) (Var 1) \<rightarrow>\<^sub>\<beta> x}"

definition "reduce t = Predicate.the (reduce' t)"

value "reduce (App (Abs (Atom 0) (Var 0)) (Var 1))"

code_pred [dseq] typing .
code_pred [random_dseq] typing .

values [random_dseq 1,1,5] 10 "{(\<Gamma>, t, T). \<Gamma> \<turnstile> t : T}"

subsection \<open>A minimal example of yet another semantics\<close>

text \<open>thanks to Elke Salecker\<close>

type_synonym vname = nat
type_synonym vvalue = int
type_synonym var_assign = "vname \<Rightarrow> vvalue"  \<comment> \<open>variable assignment\<close>

datatype ir_expr = 
  IrConst vvalue
| ObjAddr vname
| Add ir_expr ir_expr

datatype val =
  IntVal  vvalue

record  configuration =
  Env :: var_assign

inductive eval_var ::
  "ir_expr \<Rightarrow> configuration \<Rightarrow> val \<Rightarrow> bool"
where
  irconst: "eval_var (IrConst i) conf (IntVal i)"
| objaddr: "\<lbrakk> Env conf n = i \<rbrakk> \<Longrightarrow> eval_var (ObjAddr n) conf (IntVal i)"
| plus: "\<lbrakk> eval_var l conf (IntVal vl); eval_var r conf (IntVal vr) \<rbrakk> \<Longrightarrow>
    eval_var (Add l r) conf (IntVal (vl+vr))"


code_pred eval_var .
thm eval_var.equation

values "{val. eval_var (Add (IrConst 1) (IrConst 2)) (| Env = (\<lambda>x. 0)|) val}"

subsection \<open>Another semantics\<close>

type_synonym name = nat \<comment> \<open>For simplicity in examples\<close>
type_synonym state' = "name \<Rightarrow> nat"

datatype aexp = N nat | V name | Plus aexp aexp

fun aval :: "aexp \<Rightarrow> state' \<Rightarrow> nat" where
"aval (N n) _ = n" |
"aval (V x) st = st x" |
"aval (Plus e\<^sub>1 e\<^sub>2) st = aval e\<^sub>1 st + aval e\<^sub>2 st"

datatype bexp = B bool | Not bexp | And bexp bexp | Less aexp aexp

primrec bval :: "bexp \<Rightarrow> state' \<Rightarrow> bool" where
"bval (B b) _ = b" |
"bval (Not b) st = (\<not> bval b st)" |
"bval (And b1 b2) st = (bval b1 st \<and> bval b2 st)" |
"bval (Less a\<^sub>1 a\<^sub>2) st = (aval a\<^sub>1 st < aval a\<^sub>2 st)"

datatype
  com' = SKIP 
      | Assign name aexp         (\<open>_ ::= _\<close> [1000, 61] 61)
      | Semi   com'  com'          (\<open>_; _\<close>  [60, 61] 60)
      | If     bexp com' com'     (\<open>IF _ THEN _ ELSE _\<close>  [0, 0, 61] 61)
      | While  bexp com'         (\<open>WHILE _ DO _\<close>  [0, 61] 61)

inductive
  big_step :: "com' * state' \<Rightarrow> state' \<Rightarrow> bool" (infix \<open>\<Rightarrow>\<close> 55)
where
  Skip:    "(SKIP,s) \<Rightarrow> s"
| Assign:  "(x ::= a,s) \<Rightarrow> s(x := aval a s)"

| Semi:    "(c\<^sub>1,s\<^sub>1) \<Rightarrow> s\<^sub>2  \<Longrightarrow>  (c\<^sub>2,s\<^sub>2) \<Rightarrow> s\<^sub>3  \<Longrightarrow> (c\<^sub>1;c\<^sub>2, s\<^sub>1) \<Rightarrow> s\<^sub>3"

| IfTrue:  "bval b s  \<Longrightarrow>  (c\<^sub>1,s) \<Rightarrow> t  \<Longrightarrow>  (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<Rightarrow> t"
| IfFalse: "\<not>bval b s  \<Longrightarrow>  (c\<^sub>2,s) \<Rightarrow> t  \<Longrightarrow>  (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<Rightarrow> t"

| WhileFalse: "\<not>bval b s \<Longrightarrow> (WHILE b DO c,s) \<Rightarrow> s"
| WhileTrue:  "bval b s\<^sub>1  \<Longrightarrow>  (c,s\<^sub>1) \<Rightarrow> s\<^sub>2  \<Longrightarrow>  (WHILE b DO c, s\<^sub>2) \<Rightarrow> s\<^sub>3
               \<Longrightarrow> (WHILE b DO c, s\<^sub>1) \<Rightarrow> s\<^sub>3"

code_pred big_step .

thm big_step.equation

definition list :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a list" where
  "list s n = map s [0 ..< n]"

values [expected "{[42::nat, 43]}"] "{list s 2|s. (SKIP, nth [42, 43]) \<Rightarrow> s}"


subsection \<open>CCS\<close>

text\<open>This example formalizes finite CCS processes without communication or
recursion. For simplicity, labels are natural numbers.\<close>

datatype proc = nil | pre nat proc | or proc proc | par proc proc

inductive step :: "proc \<Rightarrow> nat \<Rightarrow> proc \<Rightarrow> bool" where
"step (pre n p) n p" |
"step p1 a q \<Longrightarrow> step (or p1 p2) a q" |
"step p2 a q \<Longrightarrow> step (or p1 p2) a q" |
"step p1 a q \<Longrightarrow> step (par p1 p2) a (par q p2)" |
"step p2 a q \<Longrightarrow> step (par p1 p2) a (par p1 q)"

code_pred step .

inductive steps where
"steps p [] p" |
"step p a q \<Longrightarrow> steps q as r \<Longrightarrow> steps p (a#as) r"

code_pred steps .

values 3 
 "{as . steps (par (or (pre 0 nil) (pre 1 nil)) (pre 2 nil)) as (par nil nil)}"

values 5
 "{as . steps (par (or (pre 0 nil) (pre 1 nil)) (pre 2 nil)) as (par nil nil)}"

values 3 "{(a,q). step (par nil nil) a q}"


end

