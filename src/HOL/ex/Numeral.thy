(*  Title:      HOL/ex/Numeral.thy
    ID:         $Id$
    Author:     Florian Haftmann

An experimental alternative numeral representation.
*)

theory Numeral
imports Int Inductive
begin

subsection {* The @{text num} type *}

datatype num = One | Dig0 num | Dig1 num

text {* Increment function for type @{typ num} *}

primrec
  inc :: "num \<Rightarrow> num"
where
  "inc One = Dig0 One"
| "inc (Dig0 x) = Dig1 x"
| "inc (Dig1 x) = Dig0 (inc x)"

text {* Converting between type @{typ num} and type @{typ nat} *}

primrec
  nat_of_num :: "num \<Rightarrow> nat"
where
  "nat_of_num One = Suc 0"
| "nat_of_num (Dig0 x) = nat_of_num x + nat_of_num x"
| "nat_of_num (Dig1 x) = Suc (nat_of_num x + nat_of_num x)"

primrec
  num_of_nat :: "nat \<Rightarrow> num"
where
  "num_of_nat 0 = One"
| "num_of_nat (Suc n) = (if 0 < n then inc (num_of_nat n) else One)"

lemma nat_of_num_pos: "0 < nat_of_num x"
  by (induct x) simp_all

lemma nat_of_num_neq_0: " nat_of_num x \<noteq> 0"
  by (induct x) simp_all

lemma nat_of_num_inc: "nat_of_num (inc x) = Suc (nat_of_num x)"
  by (induct x) simp_all

lemma num_of_nat_double:
  "0 < n \<Longrightarrow> num_of_nat (n + n) = Dig0 (num_of_nat n)"
  by (induct n) simp_all

text {*
  Type @{typ num} is isomorphic to the strictly positive
  natural numbers.
*}

lemma nat_of_num_inverse: "num_of_nat (nat_of_num x) = x"
  by (induct x) (simp_all add: num_of_nat_double nat_of_num_pos)

lemma num_of_nat_inverse: "0 < n \<Longrightarrow> nat_of_num (num_of_nat n) = n"
  by (induct n) (simp_all add: nat_of_num_inc)

lemma num_eq_iff: "x = y \<longleftrightarrow> nat_of_num x = nat_of_num y"
  apply safe
  apply (drule arg_cong [where f=num_of_nat])
  apply (simp add: nat_of_num_inverse)
  done

lemma num_induct [case_names One inc]:
  fixes P :: "num \<Rightarrow> bool"
  assumes One: "P One"
    and inc: "\<And>x. P x \<Longrightarrow> P (inc x)"
  shows "P x"
proof -
  obtain n where n: "Suc n = nat_of_num x"
    by (cases "nat_of_num x", simp_all add: nat_of_num_neq_0)
  have "P (num_of_nat (Suc n))"
  proof (induct n)
    case 0 show ?case using One by simp
  next
    case (Suc n)
    then have "P (inc (num_of_nat (Suc n)))" by (rule inc)
    then show "P (num_of_nat (Suc (Suc n)))" by simp
  qed
  with n show "P x"
    by (simp add: nat_of_num_inverse)
qed

text {*
  From now on, there are two possible models for @{typ num}:
  as positive naturals (rule @{text "num_induct"})
  and as digit representation (rules @{text "num.induct"}, @{text "num.cases"}).

  It is not entirely clear in which context it is better to use
  the one or the other, or whether the construction should be reversed.
*}


subsection {* Numeral operations *}

ML {*
structure DigSimps =
  NamedThmsFun(val name = "numeral"; val description = "Simplification rules for numerals")
*}

setup DigSimps.setup

instantiation num :: "{plus,times,ord}"
begin

definition plus_num :: "num \<Rightarrow> num \<Rightarrow> num" where
  [code del]: "m + n = num_of_nat (nat_of_num m + nat_of_num n)"

definition times_num :: "num \<Rightarrow> num \<Rightarrow> num" where
  [code del]: "m * n = num_of_nat (nat_of_num m * nat_of_num n)"

definition less_eq_num :: "num \<Rightarrow> num \<Rightarrow> bool" where
  [code del]: "m \<le> n \<longleftrightarrow> nat_of_num m \<le> nat_of_num n"

definition less_num :: "num \<Rightarrow> num \<Rightarrow> bool" where
  [code del]: "m < n \<longleftrightarrow> nat_of_num m < nat_of_num n"

instance ..

end

lemma nat_of_num_add: "nat_of_num (x + y) = nat_of_num x + nat_of_num y"
  unfolding plus_num_def
  by (intro num_of_nat_inverse add_pos_pos nat_of_num_pos)

lemma nat_of_num_mult: "nat_of_num (x * y) = nat_of_num x * nat_of_num y"
  unfolding times_num_def
  by (intro num_of_nat_inverse mult_pos_pos nat_of_num_pos)

lemma Dig_plus [numeral, simp, code]:
  "One + One = Dig0 One"
  "One + Dig0 m = Dig1 m"
  "One + Dig1 m = Dig0 (m + One)"
  "Dig0 n + One = Dig1 n"
  "Dig0 n + Dig0 m = Dig0 (n + m)"
  "Dig0 n + Dig1 m = Dig1 (n + m)"
  "Dig1 n + One = Dig0 (n + One)"
  "Dig1 n + Dig0 m = Dig1 (n + m)"
  "Dig1 n + Dig1 m = Dig0 (n + m + One)"
  by (simp_all add: num_eq_iff nat_of_num_add)

lemma Dig_times [numeral, simp, code]:
  "One * One = One"
  "One * Dig0 n = Dig0 n"
  "One * Dig1 n = Dig1 n"
  "Dig0 n * One = Dig0 n"
  "Dig0 n * Dig0 m = Dig0 (n * Dig0 m)"
  "Dig0 n * Dig1 m = Dig0 (n * Dig1 m)"
  "Dig1 n * One = Dig1 n"
  "Dig1 n * Dig0 m = Dig0 (n * Dig0 m + m)"
  "Dig1 n * Dig1 m = Dig1 (n * Dig1 m + m)"
  by (simp_all add: num_eq_iff nat_of_num_add nat_of_num_mult
                    left_distrib right_distrib)

lemma less_eq_num_code [numeral, simp, code]:
  "One \<le> n \<longleftrightarrow> True"
  "Dig0 m \<le> One \<longleftrightarrow> False"
  "Dig1 m \<le> One \<longleftrightarrow> False"
  "Dig0 m \<le> Dig0 n \<longleftrightarrow> m \<le> n"
  "Dig0 m \<le> Dig1 n \<longleftrightarrow> m \<le> n"
  "Dig1 m \<le> Dig1 n \<longleftrightarrow> m \<le> n"
  "Dig1 m \<le> Dig0 n \<longleftrightarrow> m < n"
  using nat_of_num_pos [of n] nat_of_num_pos [of m]
  by (auto simp add: less_eq_num_def less_num_def)

lemma less_num_code [numeral, simp, code]:
  "m < One \<longleftrightarrow> False"
  "One < One \<longleftrightarrow> False"
  "One < Dig0 n \<longleftrightarrow> True"
  "One < Dig1 n \<longleftrightarrow> True"
  "Dig0 m < Dig0 n \<longleftrightarrow> m < n"
  "Dig0 m < Dig1 n \<longleftrightarrow> m \<le> n"
  "Dig1 m < Dig1 n \<longleftrightarrow> m < n"
  "Dig1 m < Dig0 n \<longleftrightarrow> m < n"
  using nat_of_num_pos [of n] nat_of_num_pos [of m]
  by (auto simp add: less_eq_num_def less_num_def)

text {* Rules using @{text One} and @{text inc} as constructors *}

lemma add_One: "x + One = inc x"
  by (simp add: num_eq_iff nat_of_num_add nat_of_num_inc)

lemma add_inc: "x + inc y = inc (x + y)"
  by (simp add: num_eq_iff nat_of_num_add nat_of_num_inc)

lemma mult_One: "x * One = x"
  by (simp add: num_eq_iff nat_of_num_mult)

lemma mult_inc: "x * inc y = x * y + x"
  by (simp add: num_eq_iff nat_of_num_mult nat_of_num_add nat_of_num_inc)

text {* A double-and-decrement function *}

primrec DigM :: "num \<Rightarrow> num" where
  "DigM One = One"
  | "DigM (Dig0 n) = Dig1 (DigM n)"
  | "DigM (Dig1 n) = Dig1 (Dig0 n)"

lemma DigM_plus_one: "DigM n + One = Dig0 n"
  by (induct n) simp_all

lemma add_One_commute: "One + n = n + One"
  by (induct n) simp_all

lemma one_plus_DigM: "One + DigM n = Dig0 n"
  unfolding add_One_commute DigM_plus_one ..


subsection {* Binary numerals *}

text {*
  We embed binary representations into a generic algebraic
  structure using @{text of_num}
*}

class semiring_numeral = semiring + monoid_mult
begin

primrec of_num :: "num \<Rightarrow> 'a" where
  of_num_one [numeral]: "of_num One = 1"
  | "of_num (Dig0 n) = of_num n + of_num n"
  | "of_num (Dig1 n) = of_num n + of_num n + 1"

lemma of_num_inc: "of_num (inc x) = of_num x + 1"
  by (induct x) (simp_all add: add_ac)

declare of_num.simps [simp del]

end

text {*
  ML stuff and syntax.
*}

ML {*
fun mk_num 1 = @{term One}
  | mk_num k =
      let
        val (l, b) = Integer.div_mod k 2;
        val bit = (if b = 0 then @{term Dig0} else @{term Dig1});
      in bit $ (mk_num l) end;

fun dest_num @{term One} = 1
  | dest_num (@{term Dig0} $ n) = 2 * dest_num n
  | dest_num (@{term Dig1} $ n) = 2 * dest_num n + 1;

(*FIXME these have to gain proper context via morphisms phi*)

fun mk_numeral T k = Const (@{const_name of_num}, @{typ num} --> T)
  $ mk_num k

fun dest_numeral (Const (@{const_name of_num}, Type ("fun", [@{typ num}, T])) $ t) =
  (T, dest_num t)
*}

syntax
  "_Numerals" :: "xnum \<Rightarrow> 'a"    ("_")

parse_translation {*
let
  fun num_of_int n = if n > 0 then case IntInf.quotRem (n, 2)
     of (0, 1) => Const (@{const_name One}, dummyT)
      | (n, 0) => Const (@{const_name Dig0}, dummyT) $ num_of_int n
      | (n, 1) => Const (@{const_name Dig1}, dummyT) $ num_of_int n
    else raise Match;
  fun numeral_tr [Free (num, _)] =
        let
          val {leading_zeros, value, ...} = Syntax.read_xnum num;
          val _ = leading_zeros = 0 andalso value > 0
            orelse error ("Bad numeral: " ^ num);
        in Const (@{const_name of_num}, @{typ num} --> dummyT) $ num_of_int value end
    | numeral_tr ts = raise TERM ("numeral_tr", ts);
in [("_Numerals", numeral_tr)] end
*}

typed_print_translation {*
let
  fun dig b n = b + 2 * n; 
  fun int_of_num' (Const (@{const_syntax Dig0}, _) $ n) =
        dig 0 (int_of_num' n)
    | int_of_num' (Const (@{const_syntax Dig1}, _) $ n) =
        dig 1 (int_of_num' n)
    | int_of_num' (Const (@{const_syntax One}, _)) = 1;
  fun num_tr' show_sorts T [n] =
    let
      val k = int_of_num' n;
      val t' = Syntax.const "_Numerals" $ Syntax.free ("#" ^ string_of_int k);
    in case T
     of Type ("fun", [_, T']) =>
         if not (! show_types) andalso can Term.dest_Type T' then t'
         else Syntax.const Syntax.constrainC $ t' $ Syntax.term_of_typ show_sorts T'
      | T' => if T' = dummyT then t' else raise Match
    end;
in [(@{const_syntax of_num}, num_tr')] end
*}

subsection {* Class-specific numeral rules *}

text {*
  @{const of_num} is a morphism.
*}

subsubsection {* Class @{text semiring_numeral} *}

context semiring_numeral
begin

abbreviation "Num1 \<equiv> of_num One"

text {*
  Alas, there is still the duplication of @{term 1},
  thought the duplicated @{term 0} has disappeared.
  We could get rid of it by replacing the constructor
  @{term 1} in @{typ num} by two constructors
  @{text two} and @{text three}, resulting in a further
  blow-up.  But it could be worth the effort.
*}

lemma of_num_plus_one [numeral]:
  "of_num n + 1 = of_num (n + One)"
  by (rule sym, induct n) (simp_all add: of_num.simps add_ac)

lemma of_num_one_plus [numeral]:
  "1 + of_num n = of_num (n + One)"
  unfolding of_num_plus_one [symmetric] add_commute ..

lemma of_num_plus [numeral]:
  "of_num m + of_num n = of_num (m + n)"
  by (induct n rule: num_induct)
     (simp_all add: add_One add_inc of_num_one of_num_inc add_ac)

lemma of_num_times_one [numeral]:
  "of_num n * 1 = of_num n"
  by simp

lemma of_num_one_times [numeral]:
  "1 * of_num n = of_num n"
  by simp

lemma of_num_times [numeral]:
  "of_num m * of_num n = of_num (m * n)"
  by (induct n rule: num_induct)
    (simp_all add: of_num_plus [symmetric] mult_One mult_inc
    semiring_class.right_distrib right_distrib of_num_one of_num_inc)

end

subsubsection {*
  Structures with a @{term 0}: class @{text semiring_1}
*}

context semiring_1
begin

subclass semiring_numeral ..

lemma of_nat_of_num [numeral]: "of_nat (of_num n) = of_num n"
  by (induct n)
    (simp_all add: semiring_numeral_class.of_num.simps of_num.simps add_ac)

declare of_nat_1 [numeral]

lemma Dig_plus_zero [numeral]:
  "0 + 1 = 1"
  "0 + of_num n = of_num n"
  "1 + 0 = 1"
  "of_num n + 0 = of_num n"
  by simp_all

lemma Dig_times_zero [numeral]:
  "0 * 1 = 0"
  "0 * of_num n = 0"
  "1 * 0 = 0"
  "of_num n * 0 = 0"
  by simp_all

end

lemma nat_of_num_of_num: "nat_of_num = of_num"
proof
  fix n
  have "of_num n = nat_of_num n"
    by (induct n) (simp_all add: of_num.simps)
  then show "nat_of_num n = of_num n" by simp
qed

subsubsection {*
  Equality: class @{text semiring_char_0}
*}

context semiring_char_0
begin

lemma of_num_eq_iff [numeral]:
  "of_num m = of_num n \<longleftrightarrow> m = n"
  unfolding of_nat_of_num [symmetric] nat_of_num_of_num [symmetric]
    of_nat_eq_iff num_eq_iff ..

lemma of_num_eq_one_iff [numeral]:
  "of_num n = 1 \<longleftrightarrow> n = One"
proof -
  have "of_num n = of_num One \<longleftrightarrow> n = One" unfolding of_num_eq_iff ..
  then show ?thesis by (simp add: of_num_one)
qed

lemma one_eq_of_num_iff [numeral]:
  "1 = of_num n \<longleftrightarrow> n = One"
  unfolding of_num_eq_one_iff [symmetric] by auto

end

subsubsection {*
  Comparisons: class @{text ordered_semidom}
*}

text {*  Could be perhaps more general than here. *}

lemma (in ordered_semidom) of_num_pos: "0 < of_num n"
proof -
  have "(0::nat) < of_num n"
    by (induct n) (simp_all add: semiring_numeral_class.of_num.simps)
  then have "of_nat 0 \<noteq> of_nat (of_num n)" 
    by (cases n) (simp_all only: semiring_numeral_class.of_num.simps of_nat_eq_iff)
  then have "0 \<noteq> of_num n"
    by (simp add: of_nat_of_num)
  moreover have "0 \<le> of_nat (of_num n)" by simp
  ultimately show ?thesis by (simp add: of_nat_of_num)
qed

context ordered_semidom
begin

lemma of_num_less_eq_iff [numeral]: "of_num m \<le> of_num n \<longleftrightarrow> m \<le> n"
proof -
  have "of_nat (of_num m) \<le> of_nat (of_num n) \<longleftrightarrow> m \<le> n"
    unfolding less_eq_num_def nat_of_num_of_num of_nat_le_iff ..
  then show ?thesis by (simp add: of_nat_of_num)
qed

lemma of_num_less_eq_one_iff [numeral]: "of_num n \<le> 1 \<longleftrightarrow> n = One"
proof -
  have "of_num n \<le> of_num One \<longleftrightarrow> n = One"
    by (cases n) (simp_all add: of_num_less_eq_iff)
  then show ?thesis by (simp add: of_num_one)
qed

lemma one_less_eq_of_num_iff [numeral]: "1 \<le> of_num n"
proof -
  have "of_num One \<le> of_num n"
    by (cases n) (simp_all add: of_num_less_eq_iff)
  then show ?thesis by (simp add: of_num_one)
qed

lemma of_num_less_iff [numeral]: "of_num m < of_num n \<longleftrightarrow> m < n"
proof -
  have "of_nat (of_num m) < of_nat (of_num n) \<longleftrightarrow> m < n"
    unfolding less_num_def nat_of_num_of_num of_nat_less_iff ..
  then show ?thesis by (simp add: of_nat_of_num)
qed

lemma of_num_less_one_iff [numeral]: "\<not> of_num n < 1"
proof -
  have "\<not> of_num n < of_num One"
    by (cases n) (simp_all add: of_num_less_iff)
  then show ?thesis by (simp add: of_num_one)
qed

lemma one_less_of_num_iff [numeral]: "1 < of_num n \<longleftrightarrow> n \<noteq> One"
proof -
  have "of_num One < of_num n \<longleftrightarrow> n \<noteq> One"
    by (cases n) (simp_all add: of_num_less_iff)
  then show ?thesis by (simp add: of_num_one)
qed

end

subsubsection {*
  Structures with subtraction @{term "op -"}: class @{text semiring_1_minus}
*}

class semiring_minus = semiring + minus + zero +
  assumes minus_inverts_plus1: "a + b = c \<Longrightarrow> c - b = a"
  assumes minus_minus_zero_inverts_plus1: "a + b = c \<Longrightarrow> b - c = 0 - a"
begin

lemma minus_inverts_plus2: "a + b = c \<Longrightarrow> c - a = b"
  by (simp add: add_ac minus_inverts_plus1 [of b a])

lemma minus_minus_zero_inverts_plus2: "a + b = c \<Longrightarrow> a - c = 0 - b"
  by (simp add: add_ac minus_minus_zero_inverts_plus1 [of b a])

end

class semiring_1_minus = semiring_1 + semiring_minus
begin

lemma Dig_of_num_pos:
  assumes "k + n = m"
  shows "of_num m - of_num n = of_num k"
  using assms by (simp add: of_num_plus minus_inverts_plus1)

lemma Dig_of_num_zero:
  shows "of_num n - of_num n = 0"
  by (rule minus_inverts_plus1) simp

lemma Dig_of_num_neg:
  assumes "k + m = n"
  shows "of_num m - of_num n = 0 - of_num k"
  by (rule minus_minus_zero_inverts_plus1) (simp add: of_num_plus assms)

lemmas Dig_plus_eval =
  of_num_plus of_num_eq_iff Dig_plus refl [of One, THEN eqTrueI] num.inject

simproc_setup numeral_minus ("of_num m - of_num n") = {*
  let
    (*TODO proper implicit use of morphism via pattern antiquotations*)
    fun cdest_of_num ct = (snd o split_last o snd o Drule.strip_comb) ct;
    fun cdest_minus ct = case (rev o snd o Drule.strip_comb) ct of [n, m] => (m, n);
    fun attach_num ct = (dest_num (Thm.term_of ct), ct);
    fun cdifference t = (pairself (attach_num o cdest_of_num) o cdest_minus) t;
    val simplify = MetaSimplifier.rewrite false (map mk_meta_eq @{thms Dig_plus_eval});
    fun cert ck cl cj = @{thm eqTrueE} OF [@{thm meta_eq_to_obj_eq} OF [simplify (Drule.list_comb (@{cterm "op = :: num \<Rightarrow> _"},
      [Drule.list_comb (@{cterm "op + :: num \<Rightarrow> _"}, [ck, cl]), cj]))]];
  in fn phi => fn _ => fn ct => case try cdifference ct
   of NONE => (NONE)
    | SOME ((k, ck), (l, cl)) => SOME (let val j = k - l in if j = 0
        then MetaSimplifier.rewrite false [mk_meta_eq (Morphism.thm phi @{thm Dig_of_num_zero})] ct
        else mk_meta_eq (let
          val cj = Thm.cterm_of (Thm.theory_of_cterm ct) (mk_num (abs j));
        in
          (if j > 0 then (Morphism.thm phi @{thm Dig_of_num_pos}) OF [cert cj cl ck]
          else (Morphism.thm phi @{thm Dig_of_num_neg}) OF [cert cj ck cl])
        end) end)
  end
*}

lemma Dig_of_num_minus_zero [numeral]:
  "of_num n - 0 = of_num n"
  by (simp add: minus_inverts_plus1)

lemma Dig_one_minus_zero [numeral]:
  "1 - 0 = 1"
  by (simp add: minus_inverts_plus1)

lemma Dig_one_minus_one [numeral]:
  "1 - 1 = 0"
  by (simp add: minus_inverts_plus1)

lemma Dig_of_num_minus_one [numeral]:
  "of_num (Dig0 n) - 1 = of_num (DigM n)"
  "of_num (Dig1 n) - 1 = of_num (Dig0 n)"
  by (auto intro: minus_inverts_plus1 simp add: DigM_plus_one of_num.simps of_num_plus_one)

lemma Dig_one_minus_of_num [numeral]:
  "1 - of_num (Dig0 n) = 0 - of_num (DigM n)"
  "1 - of_num (Dig1 n) = 0 - of_num (Dig0 n)"
  by (auto intro: minus_minus_zero_inverts_plus1 simp add: DigM_plus_one of_num.simps of_num_plus_one)

end

subsubsection {*
  Negation: class @{text ring_1}
*}

context ring_1
begin

subclass semiring_1_minus
  proof qed (simp_all add: algebra_simps)

lemma Dig_zero_minus_of_num [numeral]:
  "0 - of_num n = - of_num n"
  by simp

lemma Dig_zero_minus_one [numeral]:
  "0 - 1 = - 1"
  by simp

lemma Dig_uminus_uminus [numeral]:
  "- (- of_num n) = of_num n"
  by simp

lemma Dig_plus_uminus [numeral]:
  "of_num m + - of_num n = of_num m - of_num n"
  "- of_num m + of_num n = of_num n - of_num m"
  "- of_num m + - of_num n = - (of_num m + of_num n)"
  "of_num m - - of_num n = of_num m + of_num n"
  "- of_num m - of_num n = - (of_num m + of_num n)"
  "- of_num m - - of_num n = of_num n - of_num m"
  by (simp_all add: diff_minus add_commute)

lemma Dig_times_uminus [numeral]:
  "- of_num n * of_num m = - (of_num n * of_num m)"
  "of_num n * - of_num m = - (of_num n * of_num m)"
  "- of_num n * - of_num m = of_num n * of_num m"
  by (simp_all add: minus_mult_left [symmetric] minus_mult_right [symmetric])

lemma of_int_of_num [numeral]: "of_int (of_num n) = of_num n"
by (induct n)
  (simp_all only: of_num.simps semiring_numeral_class.of_num.simps of_int_add, simp_all)

declare of_int_1 [numeral]

end

subsubsection {*
  Greetings to @{typ nat}.
*}

instance nat :: semiring_1_minus proof qed simp_all

lemma Suc_of_num [numeral]: "Suc (of_num n) = of_num (n + One)"
  unfolding of_num_plus_one [symmetric] by simp

lemma nat_number:
  "1 = Suc 0"
  "of_num One = Suc 0"
  "of_num (Dig0 n) = Suc (of_num (DigM n))"
  "of_num (Dig1 n) = Suc (of_num (Dig0 n))"
  by (simp_all add: of_num.simps DigM_plus_one Suc_of_num)

declare diff_0_eq_0 [numeral]


subsection {* Code generator setup for @{typ int} *}

definition Pls :: "num \<Rightarrow> int" where
  [simp, code post]: "Pls n = of_num n"

definition Mns :: "num \<Rightarrow> int" where
  [simp, code post]: "Mns n = - of_num n"

code_datatype "0::int" Pls Mns

lemmas [code inline] = Pls_def [symmetric] Mns_def [symmetric]

definition sub :: "num \<Rightarrow> num \<Rightarrow> int" where
  [simp, code del]: "sub m n = (of_num m - of_num n)"

definition dup :: "int \<Rightarrow> int" where
  [code del]: "dup k = 2 * k"

lemma Dig_sub [code]:
  "sub One One = 0"
  "sub (Dig0 m) One = of_num (DigM m)"
  "sub (Dig1 m) One = of_num (Dig0 m)"
  "sub One (Dig0 n) = - of_num (DigM n)"
  "sub One (Dig1 n) = - of_num (Dig0 n)"
  "sub (Dig0 m) (Dig0 n) = dup (sub m n)"
  "sub (Dig1 m) (Dig1 n) = dup (sub m n)"
  "sub (Dig1 m) (Dig0 n) = dup (sub m n) + 1"
  "sub (Dig0 m) (Dig1 n) = dup (sub m n) - 1"
  apply (simp_all add: dup_def algebra_simps)
  apply (simp_all add: of_num_plus one_plus_DigM)[4]
  apply (simp_all add: of_num.simps)
  done

lemma dup_code [code]:
  "dup 0 = 0"
  "dup (Pls n) = Pls (Dig0 n)"
  "dup (Mns n) = Mns (Dig0 n)"
  by (simp_all add: dup_def of_num.simps)
  
lemma [code, code del]:
  "(1 :: int) = 1"
  "(op + :: int \<Rightarrow> int \<Rightarrow> int) = op +"
  "(uminus :: int \<Rightarrow> int) = uminus"
  "(op - :: int \<Rightarrow> int \<Rightarrow> int) = op -"
  "(op * :: int \<Rightarrow> int \<Rightarrow> int) = op *"
  "(eq_class.eq :: int \<Rightarrow> int \<Rightarrow> bool) = eq_class.eq"
  "(op \<le> :: int \<Rightarrow> int \<Rightarrow> bool) = op \<le>"
  "(op < :: int \<Rightarrow> int \<Rightarrow> bool) = op <"
  by rule+

lemma one_int_code [code]:
  "1 = Pls One"
  by (simp add: of_num_one)

lemma plus_int_code [code]:
  "k + 0 = (k::int)"
  "0 + l = (l::int)"
  "Pls m + Pls n = Pls (m + n)"
  "Pls m - Pls n = sub m n"
  "Mns m + Mns n = Mns (m + n)"
  "Mns m - Mns n = sub n m"
  by (simp_all add: of_num_plus [symmetric])

lemma uminus_int_code [code]:
  "uminus 0 = (0::int)"
  "uminus (Pls m) = Mns m"
  "uminus (Mns m) = Pls m"
  by simp_all

lemma minus_int_code [code]:
  "k - 0 = (k::int)"
  "0 - l = uminus (l::int)"
  "Pls m - Pls n = sub m n"
  "Pls m - Mns n = Pls (m + n)"
  "Mns m - Pls n = Mns (m + n)"
  "Mns m - Mns n = sub n m"
  by (simp_all add: of_num_plus [symmetric])

lemma times_int_code [code]:
  "k * 0 = (0::int)"
  "0 * l = (0::int)"
  "Pls m * Pls n = Pls (m * n)"
  "Pls m * Mns n = Mns (m * n)"
  "Mns m * Pls n = Mns (m * n)"
  "Mns m * Mns n = Pls (m * n)"
  by (simp_all add: of_num_times [symmetric])

lemma eq_int_code [code]:
  "eq_class.eq 0 (0::int) \<longleftrightarrow> True"
  "eq_class.eq 0 (Pls l) \<longleftrightarrow> False"
  "eq_class.eq 0 (Mns l) \<longleftrightarrow> False"
  "eq_class.eq (Pls k) 0 \<longleftrightarrow> False"
  "eq_class.eq (Pls k) (Pls l) \<longleftrightarrow> eq_class.eq k l"
  "eq_class.eq (Pls k) (Mns l) \<longleftrightarrow> False"
  "eq_class.eq (Mns k) 0 \<longleftrightarrow> False"
  "eq_class.eq (Mns k) (Pls l) \<longleftrightarrow> False"
  "eq_class.eq (Mns k) (Mns l) \<longleftrightarrow> eq_class.eq k l"
  using of_num_pos [of l, where ?'a = int] of_num_pos [of k, where ?'a = int]
  by (simp_all add: of_num_eq_iff eq)

lemma less_eq_int_code [code]:
  "0 \<le> (0::int) \<longleftrightarrow> True"
  "0 \<le> Pls l \<longleftrightarrow> True"
  "0 \<le> Mns l \<longleftrightarrow> False"
  "Pls k \<le> 0 \<longleftrightarrow> False"
  "Pls k \<le> Pls l \<longleftrightarrow> k \<le> l"
  "Pls k \<le> Mns l \<longleftrightarrow> False"
  "Mns k \<le> 0 \<longleftrightarrow> True"
  "Mns k \<le> Pls l \<longleftrightarrow> True"
  "Mns k \<le> Mns l \<longleftrightarrow> l \<le> k"
  using of_num_pos [of l, where ?'a = int] of_num_pos [of k, where ?'a = int]
  by (simp_all add: of_num_less_eq_iff)

lemma less_int_code [code]:
  "0 < (0::int) \<longleftrightarrow> False"
  "0 < Pls l \<longleftrightarrow> True"
  "0 < Mns l \<longleftrightarrow> False"
  "Pls k < 0 \<longleftrightarrow> False"
  "Pls k < Pls l \<longleftrightarrow> k < l"
  "Pls k < Mns l \<longleftrightarrow> False"
  "Mns k < 0 \<longleftrightarrow> True"
  "Mns k < Pls l \<longleftrightarrow> True"
  "Mns k < Mns l \<longleftrightarrow> l < k"
  using of_num_pos [of l, where ?'a = int] of_num_pos [of k, where ?'a = int]
  by (simp_all add: of_num_less_iff)

lemma [code inline del]: "(0::int) \<equiv> Numeral0" by simp
lemma [code inline del]: "(1::int) \<equiv> Numeral1" by simp
declare zero_is_num_zero [code inline del]
declare one_is_num_one [code inline del]

hide (open) const sub dup


subsection {* Numeral equations as default simplification rules *}

text {* TODO.  Be more precise here with respect to subsumed facts. *}
declare (in semiring_numeral) numeral [simp]
declare (in semiring_1) numeral [simp]
declare (in semiring_char_0) numeral [simp]
declare (in ring_1) numeral [simp]
thm numeral


text {* Toy examples *}

definition "bar \<longleftrightarrow> #4 * #2 + #7 = (#8 :: nat) \<and> #4 * #2 + #7 \<ge> (#8 :: int) - #3"
code_thms bar
export_code bar in Haskell file -
export_code bar in OCaml module_name Foo file -
ML {* @{code bar} *}

end
