(*<*)theory FP1 = Main:(*>*)

subsection{*Quickcheck*}

lemma "rev(xs @ ys) = rev xs @ rev ys"
quickcheck
oops

subsection{*More Syntax*}

lemma "if xs = ys
       then rev xs = rev ys
       else rev xs \<noteq> rev ys"
by auto

lemma "case xs of
         []   \<Rightarrow> tl xs = xs
       | y#ys \<Rightarrow> tl xs \<noteq> xs"
apply(case_tac xs)
by auto


subsection{*More Types*}


subsubsection{*Natural Numbers*}

consts sum :: "nat \<Rightarrow> nat"
primrec "sum 0 = 0"
        "sum (Suc n) = Suc n + sum n"

lemma "sum n + sum n = n*(Suc n)"
apply(induct_tac n)
apply(auto)
done

text{*Some examples of linear arithmetic:*}

lemma "\<lbrakk> \<not> m < n; m < n+(1::int) \<rbrakk> \<Longrightarrow> m = n"
by(auto)

lemma "min i (max j k) = max (min k i) (min i (j::nat))"
by(arith)

text{*Full Presburger arithmetic:*}
lemma "8 \<le> (n::int) \<Longrightarrow> \<exists>i j. 0\<le>i \<and> 0\<le>j \<and> n = 3*i + 5*j"
by(arith)

text{*Not proved automatically because it involves multiplication:*}
lemma "n*n = n \<Longrightarrow> n=0 \<or> n=(1::int)"
(*<*)oops(*>*)


subsubsection{*Pairs*}

lemma "fst(x,y) = snd(z,x)"
by auto


subsection{*Definitions*}

consts xor :: "bool \<Rightarrow> bool \<Rightarrow> bool"
defs xor_def: "xor x y \<equiv> x \<and> \<not>y \<or> \<not>x \<and> y"

constdefs nand :: "bool \<Rightarrow> bool \<Rightarrow> bool"
         "nand x y \<equiv> \<not>(x \<and> y)"

lemma "\<not> xor x x"
apply(unfold xor_def)
by auto



subsection{*Simplification*}


subsubsection{*Simplification Rules*}

lemma fst_conv[simp]: "fst(x,y) = x"
by auto

text{*Setting and resetting the @{text simp} attribute:*}

declare fst_conv[simp]
declare fst_conv[simp del]


subsubsection{*The Simplification Method*}

lemma "x*(y+1) = y*(x+1::nat)"
apply simp
(*<*)oops(*>*)


subsubsection{*Adding and Deleting Simplification Rules*}

lemma "\<forall>x::nat. x*(y+z) = r"
apply (simp add: add_mult_distrib2)
(*<*)oops(*>*)text_raw{* \isanewline\isanewline *}

lemma "rev(rev(xs @ [])) = xs"
apply (simp del: rev_rev_ident)
(*<*)oops(*>*)


subsubsection{*Rewriting with Definitions*}

lemma "xor A (\<not>A)"
apply(simp only: xor_def)
apply simp
done


subsubsection{*Conditional Equations*}

(*<*)thm hd_Cons_tl(*>*)
text{*A pre-proved simplification rule: @{thm hd_Cons_tl[no_vars]}*}
lemma "hd(xs @ [x]) # tl(xs @ [x]) = xs @ [x]"
by simp


subsubsection{*Automatic Case Splits*}

lemma "\<forall>xs. if xs = [] then A else B"
apply simp
(*<*)oops(*>*)
text{*Case-expressions are only split on demand.*}


subsubsection{*Arithmetic*}

text{*Only simple arithmetic:*}
lemma "\<lbrakk> \<not> m < n; m < n+(1::nat) \<rbrakk> \<Longrightarrow> m = n"
by simp
text{*\noindent Complex goals need @{text arith}-method.*}

(*<*)
subsubsection{*Tracing*}

lemma "rev [a] = []"
apply(simp)
oops
(*>*)


subsection{*Case Study: Compiling Expressions*}


subsubsection{*Expressions*}

types 'v binop = "'v \<Rightarrow> 'v \<Rightarrow> 'v"

datatype ('a,'v)expr = Cex 'v
                     | Vex 'a
                     | Bex "'v binop"  "('a,'v)expr"  "('a,'v)expr"

consts value :: "('a,'v)expr \<Rightarrow> ('a \<Rightarrow> 'v) \<Rightarrow> 'v"
primrec
"value (Cex v) env = v"
"value (Vex a) env = env a"
"value (Bex f e1 e2) env = f (value e1 env) (value e2 env)"


subsubsection{*The Stack Machine*}

datatype ('a,'v) instr = Const 'v
                       | Load 'a
                       | Apply "'v binop"

consts exec :: "('a,'v)instr list \<Rightarrow> ('a\<Rightarrow>'v) \<Rightarrow> 'v list \<Rightarrow> 'v list"
primrec
"exec [] s vs = vs"
"exec (i#is) s vs = (case i of
    Const v  \<Rightarrow> exec is s (v#vs)
  | Load a   \<Rightarrow> exec is s ((s a)#vs)
  | Apply f  \<Rightarrow> exec is s ((f (hd vs) (hd(tl vs)))#(tl(tl vs))))"


subsubsection{*The Compiler*}

consts compile :: "('a,'v)expr \<Rightarrow> ('a,'v)instr list"
primrec
"compile (Cex v)       = [Const v]"
"compile (Vex a)       = [Load a]"
"compile (Bex f e1 e2) = (compile e2) @ (compile e1) @ [Apply f]"

theorem "exec (compile e) s [] = [value e s]"
(*<*)oops(*>*)



subsection{*Advanced Datatypes*}


subsubsection{*Mutual Recursion*}

datatype 'a aexp = IF   "'a bexp" "'a aexp" "'a aexp"
                 | Sum  "'a aexp" "'a aexp"
                 | Var 'a
                 | Num nat
and      'a bexp = Less "'a aexp" "'a aexp"
                 | And  "'a bexp" "'a bexp"
                 | Neg  "'a bexp"


consts  evala :: "'a aexp \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> nat"
        evalb :: "'a bexp \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> bool"

primrec
  "evala (IF b a1 a2) env =
     (if evalb b env then evala a1 env else evala a2 env)"
  "evala (Sum a1 a2) env = evala a1 env + evala a2 env"
  "evala (Var v) env = env v"
  "evala (Num n) env = n"

  "evalb (Less a1 a2) env = (evala a1 env < evala a2 env)"
  "evalb (And b1 b2) env = (evalb b1 env \<and> evalb b2 env)"
  "evalb (Neg b) env = (\<not> evalb b env)"

consts substa :: "('a \<Rightarrow> 'b aexp) \<Rightarrow> 'a aexp \<Rightarrow> 'b aexp"
       substb :: "('a \<Rightarrow> 'b aexp) \<Rightarrow> 'a bexp \<Rightarrow> 'b bexp"

primrec
  "substa s (IF b a1 a2) =
     IF (substb s b) (substa s a1) (substa s a2)"
  "substa s (Sum a1 a2) = Sum (substa s a1) (substa s a2)"
  "substa s (Var v) = s v"
  "substa s (Num n) = Num n"

  "substb s (Less a1 a2) = Less (substa s a1) (substa s a2)"
  "substb s (And b1 b2) = And (substb s b1) (substb s b2)"
  "substb s (Neg b) = Neg (substb s b)"

lemma substitution_lemma:
 "evala (substa s a) env = evala a (\<lambda>x. evala (s x) env) \<and>
  evalb (substb s b) env = evalb b (\<lambda>x. evala (s x) env)"
apply(induct_tac a and b)
by simp_all


subsubsection{*Nested Recursion*}

datatype tree = Tree "tree list"

text{*Some trees:*}
term "Tree []"
term "Tree [Tree [Tree []], Tree []]"

consts
mirror :: "tree \<Rightarrow> tree"
mirrors:: "tree list \<Rightarrow> tree list"

primrec
  "mirror(Tree ts) = Tree(mirrors ts)"

  "mirrors [] = []"
  "mirrors (t # ts) = mirrors ts @ [mirror t]"

lemma "mirror(mirror t) = t \<and> mirrors(mirrors ts) = ts"
apply(induct_tac t and ts)
apply simp_all
(*<*)oops(*>*)

text{*
\begin{exercise}
Complete the above proof.
\end{exercise}
*}

subsubsection{*Datatypes Involving Functions*}

datatype ('a,'i)bigtree = Tip | Br 'a "'i \<Rightarrow> ('a,'i)bigtree"

text{*A big tree:*}
term "Br 0 (\<lambda>i. Br i (\<lambda>n. Tip))"

consts map_bt :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a,'i)bigtree \<Rightarrow> ('b,'i)bigtree"
primrec
"map_bt f Tip      = Tip"
"map_bt f (Br a F) = Br (f a) (\<lambda>i. map_bt f (F i))"

lemma "map_bt (g o f) T = map_bt g (map_bt f T)"
apply(induct_tac T, rename_tac[2] F)
apply simp_all
done

text{*The ordinals:*}
datatype ord = Zero | Succ ord | Lim "nat \<Rightarrow> ord"

thm ord.induct[no_vars]

instance ord :: plus ..
instance ord :: times ..

primrec
"a + Zero   = a"
"a + Succ b = Succ(a+b)"
"a + Lim F  = Lim(\<lambda>n. a + F n)"

primrec
"a * Zero   = Zero"
"a * Succ b = a*b + a"
"a * Lim F  = Lim(\<lambda>n. a * F n)"

text{*An example provided by Stan Wainer:*}
consts H :: "ord \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat)"
primrec
"H Zero     f n = n"
"H (Succ b) f n = H b f (f n)"
"H (Lim F)  f n = H (F n) f n"

lemma [simp]: "H (a+b) f = H a f \<circ> H b f"
apply(induct b)
apply auto
done

lemma [simp]: "H (a*b) = H b \<circ> H a"
apply(induct b)
apply auto
done

text{* This is \emph{not} allowed:
\begin{verbatim}
datatype lambda = C "lambda => lambda"
\end{verbatim}

\begin{exercise}
Define the ordinal $\Gamma_0$.
\end{exercise}
*}
(*<*)end(*>*)
