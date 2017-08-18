(*  Title:      HOL/Corec_Examples/Tests/Small_Concrete.thy
    Author:     Aymeric Bouzy, Ecole polytechnique
    Author:     Jasmin Blanchette, Inria, LORIA, MPII
    Copyright   2015, 2016

Small concrete examples.
*)

section \<open>Small Concrete Examples\<close>

theory Small_Concrete
imports "HOL-Library.BNF_Corec"
begin

subsection \<open>Streams of Natural Numbers\<close>

codatatype natstream = S (head: nat) (tail: natstream)

corec (friend) incr_all where
  "incr_all s = S (head s + 1) (incr_all (tail s))"

corec all_numbers where
  "all_numbers = S 0 (incr_all all_numbers)"

corec all_numbers_efficient where
  "all_numbers_efficient n = S n (all_numbers_efficient (n + 1))"

corec remove_multiples where
  "remove_multiples n s =
    (if (head s) mod n = 0 then
      S (head (tail s)) (remove_multiples n (tail (tail s)))
    else
      S (head s) (remove_multiples n (tail s)))"

corec prime_numbers where
  "prime_numbers known_primes =
    (let next_prime = head (fold (%n s. remove_multiples n s) known_primes (tail (tail all_numbers))) in
      S next_prime (prime_numbers (next_prime # known_primes)))"

term "prime_numbers []"

corec prime_numbers_more_efficient where
  "prime_numbers_more_efficient n remaining_numbers =
    (let remaining_numbers = remove_multiples n remaining_numbers in
      S (head remaining_numbers) (prime_numbers_more_efficient (head remaining_numbers) remaining_numbers))"

term "prime_numbers_more_efficient 0 (tail (tail all_numbers))"

corec (friend) alternate where
  "alternate s1 s2 = S (head s1) (S (head s2) (alternate (tail s1) (tail s2)))"

corec (friend) all_sums where
  "all_sums s1 s2 = S (head s1 + head s2) (alternate (all_sums s1 (tail s2)) (all_sums (tail s1) s2))"

corec app_list where
  "app_list s l = (case l of
    [] \<Rightarrow> s
  | a # r \<Rightarrow> S a (app_list s r))"

friend_of_corec app_list where
  "app_list s l = (case l of
    [] \<Rightarrow> (case s of S a b \<Rightarrow> S a b)
  | a # r \<Rightarrow> S a (app_list s r))"
  sorry

corec expand_with where
  "expand_with f s = (let l = f (head s) in S (hd l) (app_list (expand_with f (tail s)) (tl l)))"

friend_of_corec expand_with where
  "expand_with f s = (let l = f (head s) in S (hd l) (app_list (expand_with f (tail s)) (tl l)))"
  sorry

corec iterations where
  "iterations f a = S a (iterations f (f a))"

corec exponential_iterations where
  "exponential_iterations f a = S (f a) (exponential_iterations (f o f) a)"

corec (friend) alternate_list where
  "alternate_list l = (let heads = (map head l) in S (hd heads) (app_list (alternate_list (map tail l)) (tl heads)))"

corec switch_one_two0 where
  "switch_one_two0 f a s = (case s of
    S b r \<Rightarrow> S b (S a (f r)))"

corec switch_one_two where
  "switch_one_two s = (case s of
    S a (S b r) \<Rightarrow> S b (S a (switch_one_two r)))"

corec fibonacci where
  "fibonacci n m = S m (fibonacci (n + m) n)"

corec sequence2 where
  "sequence2 f u1 u0 = S u0 (sequence2 f (f u1 u0) u1)"

corec (friend) alternate_with_function where
  "alternate_with_function f s =
    (let f_head_s = f (head s) in S (head f_head_s) (alternate (tail f_head_s) (alternate_with_function f (tail s))))"

corec h where
  "h l s = (case l of
    [] \<Rightarrow> s
  | (S a s') # r \<Rightarrow> S a (alternate s (h r s')))"

friend_of_corec h where
  "h l s = (case l of
    [] \<Rightarrow> (case s of S a b \<Rightarrow> S a b)
  | (S a s') # r \<Rightarrow> S a (alternate s (h r s')))"
  sorry

corec z where
  "z = S 0 (S 0 z)"

lemma "\<And>x. x = S 0 (S 0 x) \<Longrightarrow> x = z"
  apply corec_unique
  apply (rule z.code)
  done

corec enum where
  "enum m = S m (enum (m + 1))"

lemma "(\<And>m. f m = S m (f (m + 1))) \<Longrightarrow> f m = enum m"
  apply corec_unique
  apply (rule enum.code)
  done

lemma "(\<forall>m. f m = S m (f (m + 1))) \<Longrightarrow> f m = enum m"
  apply corec_unique
  apply (rule enum.code)
  done


subsection \<open>Lazy Lists of Natural Numbers\<close>

codatatype llist = LNil | LCons nat llist

corec h1 where
  "h1 x = (if x = 1 then
    LNil
  else
    let x = if x mod 2 = 0 then x div 2 else 3 * x + 1 in
    LCons x (h1 x))"

corec h3 where
  "h3 s = (case s of
    LNil \<Rightarrow> LNil
  | LCons x r \<Rightarrow> LCons x (h3 r))"

corec fold_map where
  "fold_map f a s = (let v = f a (head s) in S v (fold_map f v (tail s)))"

friend_of_corec fold_map where
  "fold_map f a s = (let v = f a (head s) in S v (fold_map f v (tail s)))"
   apply (rule fold_map.code)
  sorry


subsection \<open>Coinductive Natural Numbers\<close>

codatatype conat = CoZero | CoSuc conat

corec sum where
  "sum x y = (case x of
      CoZero \<Rightarrow> y
    | CoSuc x \<Rightarrow> CoSuc (sum x y))"

friend_of_corec sum where
  "sum x y = (case x of
      CoZero \<Rightarrow> (case y of CoZero \<Rightarrow> CoZero | CoSuc y \<Rightarrow> CoSuc y)
    | CoSuc x \<Rightarrow> CoSuc (sum x y))"
  sorry

corec (friend) prod where
  "prod x y = (case (x, y) of
      (CoZero, _) \<Rightarrow> CoZero
    | (_, CoZero) \<Rightarrow> CoZero
    | (CoSuc x, CoSuc y) \<Rightarrow> CoSuc (sum (prod x y) (sum x y)))"

end
