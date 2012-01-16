(*  Title:      HOL/ex/Binary.thy
    Author:     Makarius
*)

header {* Simple and efficient binary numerals *}

theory Binary
imports Main
begin

subsection {* Binary representation of natural numbers *}

definition
  bit :: "nat \<Rightarrow> bool \<Rightarrow> nat" where
  "bit n b = (if b then 2 * n + 1 else 2 * n)"

lemma bit_simps:
    "bit n False = 2 * n"
    "bit n True = 2 * n + 1"
  unfolding bit_def by simp_all

ML {*
  fun dest_bit (Const (@{const_name False}, _)) = 0
    | dest_bit (Const (@{const_name True}, _)) = 1
    | dest_bit t = raise TERM ("dest_bit", [t]);

  fun dest_binary (Const (@{const_name Groups.zero}, Type (@{type_name nat}, _))) = 0
    | dest_binary (Const (@{const_name Groups.one}, Type (@{type_name nat}, _))) = 1
    | dest_binary (Const (@{const_name bit}, _) $ bs $ b) = 2 * dest_binary bs + dest_bit b
    | dest_binary t = raise TERM ("dest_binary", [t]);

  fun mk_bit 0 = @{term False}
    | mk_bit 1 = @{term True}
    | mk_bit _ = raise TERM ("mk_bit", []);

  fun mk_binary 0 = @{term "0::nat"}
    | mk_binary 1 = @{term "1::nat"}
    | mk_binary n =
        if n < 0 then raise TERM ("mk_binary", [])
        else
          let val (q, r) = Integer.div_mod n 2
          in @{term bit} $ mk_binary q $ mk_bit r end;
*}


subsection {* Direct operations -- plain normalization *}

lemma binary_norm:
    "bit 0 False = 0"
    "bit 0 True = 1"
  unfolding bit_def by simp_all

lemma binary_add:
    "n + 0 = n"
    "0 + n = n"
    "1 + 1 = bit 1 False"
    "bit n False + 1 = bit n True"
    "bit n True + 1 = bit (n + 1) False"
    "1 + bit n False = bit n True"
    "1 + bit n True = bit (n + 1) False"
    "bit m False + bit n False = bit (m + n) False"
    "bit m False + bit n True = bit (m + n) True"
    "bit m True + bit n False = bit (m + n) True"
    "bit m True + bit n True = bit ((m + n) + 1) False"
  by (simp_all add: bit_simps)

lemma binary_mult:
    "n * 0 = 0"
    "0 * n = 0"
    "n * 1 = n"
    "1 * n = n"
    "bit m True * n = bit (m * n) False + n"
    "bit m False * n = bit (m * n) False"
    "n * bit m True = bit (m * n) False + n"
    "n * bit m False = bit (m * n) False"
  by (simp_all add: bit_simps)

lemmas binary_simps = binary_norm binary_add binary_mult


subsection {* Indirect operations -- ML will produce witnesses *}

lemma binary_less_eq:
  fixes n :: nat
  shows "n \<equiv> m + k \<Longrightarrow> (m \<le> n) \<equiv> True"
    and "m \<equiv> n + k + 1 \<Longrightarrow> (m \<le> n) \<equiv> False"
  by simp_all
  
lemma binary_less:
  fixes n :: nat
  shows "m \<equiv> n + k \<Longrightarrow> (m < n) \<equiv> False"
    and "n \<equiv> m + k + 1 \<Longrightarrow> (m < n) \<equiv> True"
  by simp_all

lemma binary_diff:
  fixes n :: nat
  shows "m \<equiv> n + k \<Longrightarrow> m - n \<equiv> k"
    and "n \<equiv> m + k \<Longrightarrow> m - n \<equiv> 0"
  by simp_all

lemma binary_divmod:
  fixes n :: nat
  assumes "m \<equiv> n * k + l" and "0 < n" and "l < n"
  shows "m div n \<equiv> k"
    and "m mod n \<equiv> l"
proof -
  from `m \<equiv> n * k + l` have "m = l + k * n" by simp
  with `0 < n` and `l < n` show "m div n \<equiv> k" and "m mod n \<equiv> l" by simp_all
qed

ML {*
local
  infix ==;
  val op == = Logic.mk_equals;
  fun plus m n = @{term "plus :: nat \<Rightarrow> nat \<Rightarrow> nat"} $ m $ n;
  fun mult m n = @{term "times :: nat \<Rightarrow> nat \<Rightarrow> nat"} $ m $ n;

  val binary_ss = HOL_basic_ss addsimps @{thms binary_simps};
  fun prove ctxt prop =
    Goal.prove ctxt [] [] prop (fn _ => ALLGOALS (full_simp_tac binary_ss));

  fun binary_proc proc ss ct =
    (case Thm.term_of ct of
      _ $ t $ u =>
      (case try (pairself (`dest_binary)) (t, u) of
        SOME args => proc (Simplifier.the_context ss) args
      | NONE => NONE)
    | _ => NONE);
in

val less_eq_proc = binary_proc (fn ctxt => fn ((m, t), (n, u)) =>
  let val k = n - m in
    if k >= 0 then
      SOME (@{thm binary_less_eq(1)} OF [prove ctxt (u == plus t (mk_binary k))])
    else
      SOME (@{thm binary_less_eq(2)} OF
        [prove ctxt (t == plus (plus u (mk_binary (~ k - 1))) (mk_binary 1))])
  end);

val less_proc = binary_proc (fn ctxt => fn ((m, t), (n, u)) =>
  let val k = m - n in
    if k >= 0 then
      SOME (@{thm binary_less(1)} OF [prove ctxt (t == plus u (mk_binary k))])
    else
      SOME (@{thm binary_less(2)} OF
        [prove ctxt (u == plus (plus t (mk_binary (~ k - 1))) (mk_binary 1))])
  end);

val diff_proc = binary_proc (fn ctxt => fn ((m, t), (n, u)) =>
  let val k = m - n in
    if k >= 0 then
      SOME (@{thm binary_diff(1)} OF [prove ctxt (t == plus u (mk_binary k))])
    else
      SOME (@{thm binary_diff(2)} OF [prove ctxt (u == plus t (mk_binary (~ k)))])
  end);

fun divmod_proc rule = binary_proc (fn ctxt => fn ((m, t), (n, u)) =>
  if n = 0 then NONE
  else
    let val (k, l) = Integer.div_mod m n
    in SOME (rule OF [prove ctxt (t == plus (mult u (mk_binary k)) (mk_binary l))]) end);

end;
*}

simproc_setup binary_nat_less_eq ("m <= (n::nat)") = {* K less_eq_proc *}
simproc_setup binary_nat_less ("m < (n::nat)") = {* K less_proc *}
simproc_setup binary_nat_diff ("m - (n::nat)") = {* K diff_proc *}
simproc_setup binary_nat_div ("m div (n::nat)") = {* K (divmod_proc @{thm binary_divmod(1)}) *}
simproc_setup binary_nat_mod ("m mod (n::nat)") = {* K (divmod_proc @{thm binary_divmod(2)}) *}

method_setup binary_simp = {*
  Scan.succeed (K (SIMPLE_METHOD'
    (full_simp_tac
      (HOL_basic_ss
        addsimps @{thms binary_simps}
        addsimprocs
         [@{simproc binary_nat_less_eq},
          @{simproc binary_nat_less},
          @{simproc binary_nat_diff},
          @{simproc binary_nat_div},
          @{simproc binary_nat_mod}]))))
*}


subsection {* Concrete syntax *}

syntax
  "_Binary" :: "num_const \<Rightarrow> 'a"    ("$_")

parse_translation {*
let
  val syntax_consts =
    map_aterms (fn Const (c, T) => Const (Lexicon.mark_const c, T) | a => a);

  fun binary_tr [(c as Const (@{syntax_const "_constrain"}, _)) $ t $ u] = c $ binary_tr [t] $ u
    | binary_tr [Const (num, _)] =
        let
          val {leading_zeros = z, value = n, ...} = Lexicon.read_xnum num;
          val _ = z = 0 andalso n >= 0 orelse error ("Bad binary number: " ^ num);
        in syntax_consts (mk_binary n) end
    | binary_tr ts = raise TERM ("binary_tr", ts);

in [(@{syntax_const "_Binary"}, binary_tr)] end
*}


subsection {* Examples *}

lemma "$6 = 6"
  by (simp add: bit_simps)

lemma "bit (bit (bit 0 False) False) True = 1"
  by (simp add: bit_simps)

lemma "bit (bit (bit 0 False) False) True = bit 0 True"
  by (simp add: bit_simps)

lemma "$5 + $3 = $8"
  by binary_simp

lemma "$5 * $3 = $15"
  by binary_simp

lemma "$5 - $3 = $2"
  by binary_simp

lemma "$3 - $5 = 0"
  by binary_simp

lemma "$123456789 - $123 = $123456666"
  by binary_simp

lemma "$1111111111222222222233333333334444444444 - $998877665544332211 =
  $1111111111222222222232334455668900112233"
  by binary_simp

lemma "(1111111111222222222233333333334444444444::nat) - 998877665544332211 =
  1111111111222222222232334455668900112233"
  by simp

lemma "(1111111111222222222233333333334444444444::int) - 998877665544332211 =
  1111111111222222222232334455668900112233"
  by simp

lemma "$1111111111222222222233333333334444444444 * $998877665544332211 =
    $1109864072938022197293802219729380221972383090160869185684"
  by binary_simp

lemma "$1111111111222222222233333333334444444444 * $998877665544332211 -
      $5555555555666666666677777777778888888888 =
    $1109864072938022191738246664062713555294605312381980296796"
  by binary_simp

lemma "$42 < $4 = False"
  by binary_simp

lemma "$4 < $42 = True"
  by binary_simp

lemma "$42 <= $4 = False"
  by binary_simp

lemma "$4 <= $42 = True"
  by binary_simp

lemma "$1111111111222222222233333333334444444444 < $998877665544332211 = False"
  by binary_simp

lemma "$998877665544332211 < $1111111111222222222233333333334444444444 = True"
  by binary_simp

lemma "$1111111111222222222233333333334444444444 <= $998877665544332211 = False"
  by binary_simp

lemma "$998877665544332211 <= $1111111111222222222233333333334444444444 = True"
  by binary_simp

lemma "$1234 div $23 = $53"
  by binary_simp

lemma "$1234 mod $23 = $15"
  by binary_simp

lemma "$1111111111222222222233333333334444444444 div $998877665544332211 =
    $1112359550673033707875"
  by binary_simp

lemma "$1111111111222222222233333333334444444444 mod $998877665544332211 =
    $42245174317582819"
  by binary_simp

lemma "(1111111111222222222233333333334444444444::int) div 998877665544332211 =
    1112359550673033707875"
  by simp  -- {* legacy numerals: 30 times slower *}

lemma "(1111111111222222222233333333334444444444::int) mod 998877665544332211 =
    42245174317582819"
  by simp  -- {* legacy numerals: 30 times slower *}

end
