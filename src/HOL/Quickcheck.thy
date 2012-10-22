(* Author: Florian Haftmann & Lukas Bulwahn, TU Muenchen *)

header {* A simple counterexample generator performing random testing *}

theory Quickcheck
imports Random Code_Evaluation Enum
begin

notation fcomp (infixl "\<circ>>" 60)
notation scomp (infixl "\<circ>\<rightarrow>" 60)

setup {* Code_Target.extend_target ("Quickcheck", (Code_Runtime.target, K I)) *}

subsection {* Catching Match exceptions *}

axiomatization catch_match :: "'a => 'a => 'a"

code_const catch_match 
  (Quickcheck "((_) handle Match => _)")

subsection {* The @{text random} class *}

class random = typerep +
  fixes random :: "code_numeral \<Rightarrow> Random.seed \<Rightarrow> ('a \<times> (unit \<Rightarrow> term)) \<times> Random.seed"


subsection {* Fundamental and numeric types*}

instantiation bool :: random
begin

definition
  "random i = Random.range 2 \<circ>\<rightarrow>
    (\<lambda>k. Pair (if k = 0 then Code_Evaluation.valtermify False else Code_Evaluation.valtermify True))"

instance ..

end

instantiation itself :: (typerep) random
begin

definition
  random_itself :: "code_numeral \<Rightarrow> Random.seed \<Rightarrow> ('a itself \<times> (unit \<Rightarrow> term)) \<times> Random.seed"
where "random_itself _ = Pair (Code_Evaluation.valtermify TYPE('a))"

instance ..

end

instantiation char :: random
begin

definition
  "random _ = Random.select (Enum.enum :: char list) \<circ>\<rightarrow> (\<lambda>c. Pair (c, \<lambda>u. Code_Evaluation.term_of c))"

instance ..

end

instantiation String.literal :: random
begin

definition 
  "random _ = Pair (STR '''', \<lambda>u. Code_Evaluation.term_of (STR ''''))"

instance ..

end

instantiation nat :: random
begin

definition random_nat :: "code_numeral \<Rightarrow> Random.seed
  \<Rightarrow> (nat \<times> (unit \<Rightarrow> Code_Evaluation.term)) \<times> Random.seed"
where
  "random_nat i = Random.range (i + 1) \<circ>\<rightarrow> (\<lambda>k. Pair (
     let n = Code_Numeral.nat_of k
     in (n, \<lambda>_. Code_Evaluation.term_of n)))"

instance ..

end

instantiation int :: random
begin

definition
  "random i = Random.range (2 * i + 1) \<circ>\<rightarrow> (\<lambda>k. Pair (
     let j = (if k \<ge> i then Code_Numeral.int_of (k - i) else - Code_Numeral.int_of (i - k))
     in (j, \<lambda>_. Code_Evaluation.term_of j)))"

instance ..

end


subsection {* Complex generators *}

text {* Towards @{typ "'a \<Rightarrow> 'b"} *}

axiomatization random_fun_aux :: "typerep \<Rightarrow> typerep \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> term)
  \<Rightarrow> (Random.seed \<Rightarrow> ('b \<times> (unit \<Rightarrow> term)) \<times> Random.seed)
  \<Rightarrow> (Random.seed \<Rightarrow> Random.seed \<times> Random.seed)
  \<Rightarrow> Random.seed \<Rightarrow> (('a \<Rightarrow> 'b) \<times> (unit \<Rightarrow> term)) \<times> Random.seed"

definition random_fun_lift :: "(Random.seed \<Rightarrow> ('b \<times> (unit \<Rightarrow> term)) \<times> Random.seed)
  \<Rightarrow> Random.seed \<Rightarrow> (('a\<Colon>term_of \<Rightarrow> 'b\<Colon>typerep) \<times> (unit \<Rightarrow> term)) \<times> Random.seed"
where
  "random_fun_lift f =
    random_fun_aux TYPEREP('a) TYPEREP('b) (op =) Code_Evaluation.term_of f Random.split_seed"

instantiation "fun" :: ("{equal, term_of}", random) random
begin

definition
  random_fun :: "code_numeral \<Rightarrow> Random.seed \<Rightarrow> (('a \<Rightarrow> 'b) \<times> (unit \<Rightarrow> term)) \<times> Random.seed"
  where "random i = random_fun_lift (random i)"

instance ..

end

text {* Towards type copies and datatypes *}

definition collapse :: "('a \<Rightarrow> ('a \<Rightarrow> 'b \<times> 'a) \<times> 'a) \<Rightarrow> 'a \<Rightarrow> 'b \<times> 'a"
  where "collapse f = (f \<circ>\<rightarrow> id)"

definition beyond :: "code_numeral \<Rightarrow> code_numeral \<Rightarrow> code_numeral"
  where "beyond k l = (if l > k then l else 0)"

lemma beyond_zero: "beyond k 0 = 0"
  by (simp add: beyond_def)


definition (in term_syntax) [code_unfold]:
  "valterm_emptyset = Code_Evaluation.valtermify ({} :: ('a :: typerep) set)"

definition (in term_syntax) [code_unfold]:
  "valtermify_insert x s = Code_Evaluation.valtermify insert {\<cdot>} (x :: ('a :: typerep * _)) {\<cdot>} s"

instantiation set :: (random) random
begin

primrec random_aux_set
where
  "random_aux_set 0 j = collapse (Random.select_weight [(1, Pair valterm_emptyset)])"
| "random_aux_set (Code_Numeral.Suc i) j =
    collapse (Random.select_weight
      [(1, Pair valterm_emptyset),
       (Code_Numeral.Suc i,
        random j \<circ>\<rightarrow> (%x. random_aux_set i j \<circ>\<rightarrow> (%s. Pair (valtermify_insert x s))))])"

lemma [code]:
  "random_aux_set i j =
    collapse (Random.select_weight [(1, Pair valterm_emptyset),
      (i, random j \<circ>\<rightarrow> (%x. random_aux_set (i - 1) j \<circ>\<rightarrow> (%s. Pair (valtermify_insert x s))))])"
proof (induct i rule: code_numeral.induct)
  case zero
  show ?case by (subst select_weight_drop_zero[symmetric])
    (simp add: filter.simps random_aux_set.simps[simplified])
next
  case (Suc i)
  show ?case by (simp only: random_aux_set.simps(2)[of "i"] Suc_code_numeral_minus_one)
qed

definition "random_set i = random_aux_set i i"

instance ..

end

lemma random_aux_rec:
  fixes random_aux :: "code_numeral \<Rightarrow> 'a"
  assumes "random_aux 0 = rhs 0"
    and "\<And>k. random_aux (Code_Numeral.Suc k) = rhs (Code_Numeral.Suc k)"
  shows "random_aux k = rhs k"
  using assms by (rule code_numeral.induct)

subsection {* Deriving random generators for datatypes *}

ML_file "Tools/Quickcheck/quickcheck_common.ML" 
ML_file "Tools/Quickcheck/random_generators.ML"
setup Random_Generators.setup


subsection {* Code setup *}

code_const random_fun_aux (Quickcheck "Random'_Generators.random'_fun")
  -- {* With enough criminal energy this can be abused to derive @{prop False};
  for this reason we use a distinguished target @{text Quickcheck}
  not spoiling the regular trusted code generation *}

code_reserved Quickcheck Random_Generators

no_notation fcomp (infixl "\<circ>>" 60)
no_notation scomp (infixl "\<circ>\<rightarrow>" 60)

subsection {* The Random-Predicate Monad *} 

fun iter' ::
  "'a itself => code_numeral => code_numeral => code_numeral * code_numeral
    => ('a::random) Predicate.pred"
where
  "iter' T nrandom sz seed = (if nrandom = 0 then bot_class.bot else
     let ((x, _), seed') = random sz seed
   in Predicate.Seq (%u. Predicate.Insert x (iter' T (nrandom - 1) sz seed')))"

definition iter :: "code_numeral => code_numeral => code_numeral * code_numeral
  => ('a::random) Predicate.pred"
where
  "iter nrandom sz seed = iter' (TYPE('a)) nrandom sz seed"

lemma [code]:
  "iter nrandom sz seed = (if nrandom = 0 then bot_class.bot else
     let ((x, _), seed') = random sz seed
   in Predicate.Seq (%u. Predicate.Insert x (iter (nrandom - 1) sz seed')))"
unfolding iter_def iter'.simps[of _ nrandom] ..

type_synonym 'a randompred = "Random.seed \<Rightarrow> ('a Predicate.pred \<times> Random.seed)"

definition empty :: "'a randompred"
  where "empty = Pair (bot_class.bot)"

definition single :: "'a => 'a randompred"
  where "single x = Pair (Predicate.single x)"

definition bind :: "'a randompred \<Rightarrow> ('a \<Rightarrow> 'b randompred) \<Rightarrow> 'b randompred"
  where
    "bind R f = (\<lambda>s. let
       (P, s') = R s;
       (s1, s2) = Random.split_seed s'
     in (Predicate.bind P (%a. fst (f a s1)), s2))"

definition union :: "'a randompred \<Rightarrow> 'a randompred \<Rightarrow> 'a randompred"
where
  "union R1 R2 = (\<lambda>s. let
     (P1, s') = R1 s; (P2, s'') = R2 s'
   in (sup_class.sup P1 P2, s''))"

definition if_randompred :: "bool \<Rightarrow> unit randompred"
where
  "if_randompred b = (if b then single () else empty)"

definition iterate_upto :: "(code_numeral => 'a) => code_numeral => code_numeral => 'a randompred"
where
  "iterate_upto f n m = Pair (Predicate.iterate_upto f n m)"

definition not_randompred :: "unit randompred \<Rightarrow> unit randompred"
where
  "not_randompred P = (\<lambda>s. let
     (P', s') = P s
   in if Predicate.eval P' () then (Orderings.bot, s') else (Predicate.single (), s'))"

definition Random :: "(Random.seed \<Rightarrow> ('a \<times> (unit \<Rightarrow> term)) \<times> Random.seed) \<Rightarrow> 'a randompred"
  where "Random g = scomp g (Pair o (Predicate.single o fst))"

definition map :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a randompred \<Rightarrow> 'b randompred)"
  where "map f P = bind P (single o f)"

hide_fact
  random_bool_def
  random_itself_def
  random_char_def
  random_literal_def
  random_nat_def
  random_int_def
  random_fun_lift_def
  random_fun_def
  collapse_def
  beyond_def
  beyond_zero
  random_aux_rec

hide_const (open) catch_match random collapse beyond random_fun_aux random_fun_lift

hide_fact (open) iter'.simps iter_def empty_def single_def bind_def union_def
  if_randompred_def iterate_upto_def not_randompred_def Random_def map_def 
hide_type (open) randompred
hide_const (open) iter' iter empty single bind union if_randompred
  iterate_upto not_randompred Random map

end

