header {* A simple example demonstrating parallelism for code generated towards Isabelle/ML *}

theory Parallel_Example
imports Complex_Main "~~/src/HOL/Library/Parallel" "~~/src/HOL/Library/Debug"
begin

subsection {* Compute-intensive examples. *}

subsubsection {* Fragments of the harmonic series *}

definition harmonic :: "nat \<Rightarrow> rat" where
  "harmonic n = listsum (map (\<lambda>n. 1 / of_nat n) [1..<n])"


subsubsection {* The sieve of Erathostenes *}

text {*
  The attentive reader may relate this ad-hoc implementation to the
  arithmetic notion of prime numbers as a little exercise.
*}

primrec mark :: "nat \<Rightarrow> nat \<Rightarrow> bool list \<Rightarrow> bool list" where
  "mark _ _ [] = []"
| "mark m n (p # ps) = (case n of 0 \<Rightarrow> False # mark m m ps
    | Suc n \<Rightarrow> p # mark m n ps)"

lemma length_mark [simp]:
  "length (mark m n ps) = length ps"
  by (induct ps arbitrary: n) (simp_all split: nat.split)

function sieve :: "nat \<Rightarrow> bool list \<Rightarrow> bool list" where
  "sieve m ps = (case dropWhile Not ps
   of [] \<Rightarrow> ps
    | p#ps' \<Rightarrow> let n = m - length ps' in takeWhile Not ps @ p # sieve m (mark n n ps'))"
by pat_completeness auto

termination -- {* tuning of this proof is left as an exercise to the reader *}
  apply (relation "measure (length \<circ> snd)")
  apply rule
  apply (auto simp add: length_dropWhile_le)
proof -
  fix ps qs q
  assume "dropWhile Not ps = q # qs"
  then have "length (q # qs) = length (dropWhile Not ps)" by simp
  then have "length qs < length (dropWhile Not ps)" by simp
  moreover have "length (dropWhile Not ps) \<le> length ps"
    by (simp add: length_dropWhile_le)
  ultimately show "length qs < length ps" by auto
qed

primrec natify :: "nat \<Rightarrow> bool list \<Rightarrow> nat list" where
  "natify _ [] = []"
| "natify n (p#ps) = (if p then n # natify (Suc n) ps else natify (Suc n) ps)"

primrec list_primes where
  "list_primes (Suc n) = natify 1 (sieve n (False # replicate n True))"


subsubsection {* Naive factorisation *}

function factorise_from :: "nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "factorise_from k n = (if 1 < k \<and> k \<le> n
    then
      let (q, r) = divmod_nat n k 
      in if r = 0 then k # factorise_from k q
        else factorise_from (Suc k) n
    else [])" 
by pat_completeness auto

termination factorise_from -- {* tuning of this proof is left as an exercise to the reader *}
term measure
apply (relation "measure (\<lambda>(k, n). 2 * n - k)")
apply (auto simp add: prod_eq_iff)
apply (case_tac "k \<le> 2 * q")
apply (rule diff_less_mono)
apply auto
done

definition factorise :: "nat \<Rightarrow> nat list" where
  "factorise n = factorise_from 2 n"


subsection {* Concurrent computation via futures *}

definition computation_harmonic :: "unit \<Rightarrow> rat" where
  "computation_harmonic _ = Debug.timing (STR ''harmonic example'') harmonic 300"

definition computation_primes :: "unit \<Rightarrow> nat list" where
  "computation_primes _ = Debug.timing (STR ''primes example'') list_primes 4000"

definition computation_future :: "unit \<Rightarrow> nat list \<times> rat" where
  "computation_future = Debug.timing (STR ''overall computation'')
   (\<lambda>() \<Rightarrow> let c = Parallel.fork computation_harmonic
     in (computation_primes (), Parallel.join c))"

value [code] "computation_future ()"

definition computation_factorise :: "nat \<Rightarrow> nat list" where
  "computation_factorise = Debug.timing (STR ''factorise'') factorise"

definition computation_parallel :: "unit \<Rightarrow> nat list list" where
  "computation_parallel _ = Debug.timing (STR ''overall computation'')
     (Parallel.map computation_factorise) [20000..<20100]"

value [code] "computation_parallel ()"

end

