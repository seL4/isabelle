theory Reg_Exp_Example
imports
  "~~/src/HOL/Library/Predicate_Compile_Quickcheck"
  "~~/src/HOL/Library/Code_Prolog"
begin

text {* An example from the experiments from SmallCheck (http://www.cs.york.ac.uk/fp/smallcheck/) *}
text {* The example (original in Haskell) was imported with Haskabelle and
  manually slightly adapted.
*}
 
datatype Nat = Zer
             | Suc Nat

fun sub :: "Nat \<Rightarrow> Nat \<Rightarrow> Nat"
where
  "sub x y = (case y of
                 Zer \<Rightarrow> x
               | Suc y' \<Rightarrow> case x of
                                         Zer \<Rightarrow> Zer
                                       | Suc x' \<Rightarrow> sub x' y')"

datatype Sym = N0
             | N1 Sym

datatype RE = Sym Sym
            | Or RE RE
            | Seq RE RE
            | And RE RE
            | Star RE
            | Empty

 
function accepts :: "RE \<Rightarrow> Sym list \<Rightarrow> bool" and 
    seqSplit :: "RE \<Rightarrow> RE \<Rightarrow> Sym list \<Rightarrow> Sym list \<Rightarrow> bool" and 
    seqSplit'' :: "RE \<Rightarrow> RE \<Rightarrow> Sym list \<Rightarrow> Sym list \<Rightarrow> bool" and 
    seqSplit' :: "RE \<Rightarrow> RE \<Rightarrow> Sym list \<Rightarrow> Sym list \<Rightarrow> bool"
where
  "accepts re ss = (case re of
                       Sym n \<Rightarrow> case ss of
                                              Nil \<Rightarrow> False
                                            | (n' # ss') \<Rightarrow> n = n' & List.null ss'
                     | Or re1 re2 \<Rightarrow> accepts re1 ss | accepts re2 ss
                     | Seq re1 re2 \<Rightarrow> seqSplit re1 re2 Nil ss
                     | And re1 re2 \<Rightarrow> accepts re1 ss & accepts re2 ss
                     | Star re' \<Rightarrow> case ss of
                                                 Nil \<Rightarrow> True
                                               | (s # ss') \<Rightarrow> seqSplit re' re [s] ss'
                     | Empty \<Rightarrow> List.null ss)"
| "seqSplit re1 re2 ss2 ss = (seqSplit'' re1 re2 ss2 ss | seqSplit' re1 re2 ss2 ss)"
| "seqSplit'' re1 re2 ss2 ss = (accepts re1 ss2 & accepts re2 ss)"
| "seqSplit' re1 re2 ss2 ss = (case ss of
                                  Nil \<Rightarrow> False
                                | (n # ss') \<Rightarrow> seqSplit re1 re2 (ss2 @ [n]) ss')"
by pat_completeness auto

termination
  sorry
 
fun rep :: "Nat \<Rightarrow> RE \<Rightarrow> RE"
where
  "rep n re = (case n of
                  Zer \<Rightarrow> Empty
                | Suc n' \<Rightarrow> Seq re (rep n' re))"

 
fun repMax :: "Nat \<Rightarrow> RE \<Rightarrow> RE"
where
  "repMax n re = (case n of
                     Zer \<Rightarrow> Empty
                   | Suc n' \<Rightarrow> Or (rep n re) (repMax n' re))"

 
fun repInt' :: "Nat \<Rightarrow> Nat \<Rightarrow> RE \<Rightarrow> RE"
where
  "repInt' n k re = (case k of
                        Zer \<Rightarrow> rep n re
                      | Suc k' \<Rightarrow> Or (rep n re) (repInt' (Suc n) k' re))"

 
fun repInt :: "Nat \<Rightarrow> Nat \<Rightarrow> RE \<Rightarrow> RE"
where
  "repInt n k re = repInt' n (sub k n) re"

 
fun prop_regex :: "Nat * Nat * RE * RE * Sym list \<Rightarrow> bool"
where
  "prop_regex (n, (k, (p, (q, s)))) = ((accepts (repInt n k (And p q)) s) = (accepts (And (repInt n k p) (repInt n k q)) s))"



lemma "accepts (repInt n k (And p q)) s --> accepts (And (repInt n k p) (repInt n k q)) s"
(*nitpick
quickcheck[tester = random, iterations = 10000]
quickcheck[tester = predicate_compile_wo_ff]
quickcheck[tester = predicate_compile_ff_fs]*)
oops


setup {* Context.theory_map (Quickcheck.add_tester ("prolog", (Code_Prolog.active, Code_Prolog.test_goals))) *}

setup {* Code_Prolog.map_code_options (K 
  {ensure_groundness = true,
   limit_globally = NONE,
   limited_types = [(@{typ Sym}, 0), (@{typ "Sym list"}, 2), (@{typ RE}, 6)],
   limited_predicates = [(["repIntPa"], 2), (["repP"], 2), (["subP"], 0),
    (["accepts", "acceptsaux", "seqSplit", "seqSplita", "seqSplitaux", "seqSplitb"], 25)],
   replacing =
     [(("repP", "limited_repP"), "lim_repIntPa"),
      (("subP", "limited_subP"), "repIntP"),
      (("repIntPa", "limited_repIntPa"), "repIntP"),
      (("accepts", "limited_accepts"), "quickcheck")],  
   manual_reorder = []}) *}

text {* Finding the counterexample still seems out of reach for the
 prolog-style generation. *}

lemma "accepts (And (repInt n k p) (repInt n k q)) s --> accepts (repInt n k (And p q)) s"
quickcheck[exhaustive]
quickcheck[tester = random, iterations = 1000]
(*quickcheck[tester = predicate_compile_wo_ff]*)
(*quickcheck[tester = predicate_compile_ff_fs, iterations = 1]*)
(*quickcheck[tester = prolog, iterations = 1, size = 1]*)
oops

section {* Given a partial solution *}

lemma
(*  assumes "n = Zer"
  assumes "k = Suc (Suc Zer)"*)
  assumes "p = Sym N0"
  assumes "q = Seq (Sym N0) (Sym N0)"
(*  assumes "s = [N0, N0]"*)
  shows "accepts (And (repInt n k p) (repInt n k q)) s --> accepts (repInt n k (And p q)) s"
(*quickcheck[tester = predicate_compile_wo_ff, iterations = 1]*)
quickcheck[tester = prolog, iterations = 1, size = 1]
oops

section {* Checking the counterexample *}

definition a_sol
where
  "a_sol = (Zer, (Suc (Suc Zer), (Sym N0, (Seq (Sym N0) (Sym N0), [N0, N0]))))"

lemma 
  assumes "n = Zer"
  assumes "k = Suc (Suc Zer)"
  assumes "p = Sym N0"
  assumes "q = Seq (Sym N0) (Sym N0)"
  assumes "s = [N0, N0]"
  shows "accepts (repInt n k (And p q)) s --> accepts (And (repInt n k p) (repInt n k q)) s"
(*quickcheck[tester = predicate_compile_wo_ff]*)
oops

lemma
  assumes "n = Zer"
  assumes "k = Suc (Suc Zer)"
  assumes "p = Sym N0"
  assumes "q = Seq (Sym N0) (Sym N0)"
  assumes "s = [N0, N0]"
  shows "accepts (And (repInt n k p) (repInt n k q)) s --> accepts (repInt n k (And p q)) s"
(*quickcheck[tester = predicate_compile_wo_ff, iterations = 1, expect = counterexample]*)
quickcheck[tester = prolog, iterations = 1, size = 1]
oops

lemma
  assumes "n = Zer"
  assumes "k = Suc (Suc Zer)"
  assumes "p = Sym N0"
  assumes "q = Seq (Sym N0) (Sym N0)"
  assumes "s = [N0, N0]"
shows "prop_regex (n, (k, (p, (q, s))))"
quickcheck[tester = smart_exhaustive, depth = 30]
quickcheck[tester = prolog]
oops

lemma "prop_regex a_sol"
quickcheck[tester = random]
quickcheck[tester = smart_exhaustive]
oops

value [code] "prop_regex a_sol"


end
