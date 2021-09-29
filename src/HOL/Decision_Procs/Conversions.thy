(*  Title:      HOL/Decision_Procs/Conversions.thy
    Author:     Stefan Berghofer
*)

theory Conversions
imports Main
begin

ML \<open>
fun tactic_of_conv cv i st =
  if i > Thm.nprems_of st then Seq.empty
  else Seq.single (Conv.gconv_rule cv i st);

fun binop_conv cv cv' = Conv.combination_conv (Conv.arg_conv cv) cv';
\<close>

ML \<open>
fun err s ct =
   error (s ^ ": " ^ Syntax.string_of_term_global (Thm.theory_of_cterm ct) (Thm.term_of ct));
\<close>

attribute_setup meta =
  \<open>Scan.succeed (fn (ctxt, th) => (NONE, SOME (mk_meta_eq th)))\<close>
  \<open>convert equality to meta equality\<close>

ML \<open>
fun strip_app ct = ct |> Drule.strip_comb |>> Thm.term_of |>> dest_Const |>> fst;

fun inst cTs cts th =
  Thm.instantiate' (map SOME cTs) (map SOME cts) th;

fun transitive' eq eq' = Thm.transitive eq (eq' (Thm.rhs_of eq));

fun type_of_eqn eqn = Thm.ctyp_of_cterm (Thm.dest_arg1 (Thm.cprop_of eqn));

fun cong1 conv ct =
  Thm.combination (Thm.reflexive (Thm.dest_fun ct)) (conv (Thm.dest_arg ct));

fun cong1' conv' conv ct =
  let val eqn = conv (Thm.dest_arg ct)
  in
    Thm.transitive
      (Thm.combination (Thm.reflexive (Thm.dest_fun ct)) eqn)
      (conv' (Thm.rhs_of eqn))
  end;

fun cong2 conv1 conv2 ct =
  Thm.combination
    (Thm.combination
       (Thm.reflexive (Thm.dest_fun2 ct))
       (conv1 (Thm.dest_arg1 ct)))
    (conv2 (Thm.dest_arg ct));

fun cong2' conv conv1 conv2 ct =
  let
    val eqn1 = conv1 (Thm.dest_arg1 ct);
    val eqn2 = conv2 (Thm.dest_arg ct)
  in
    Thm.transitive
      (Thm.combination
         (Thm.combination (Thm.reflexive (Thm.dest_fun2 ct)) eqn1)
         eqn2)
      (conv (Thm.rhs_of eqn1) (Thm.rhs_of eqn2))
  end;

fun cong2'' conv eqn1 eqn2 =
  let val eqn3 = conv (Thm.rhs_of eqn1) (Thm.rhs_of eqn2)
  in
    Thm.transitive
      (Thm.combination
         (Thm.combination (Thm.reflexive (Thm.dest_fun2 (Thm.lhs_of eqn3))) eqn1)
         eqn2)
      eqn3
  end;

fun args1 conv ct = conv (Thm.dest_arg ct);
fun args2 conv ct = conv (Thm.dest_arg1 ct) (Thm.dest_arg ct);
\<close>

ML \<open>
fun strip_numeral ct = (case strip_app ct of
    (\<^const_name>\<open>uminus\<close>, [n]) => (case strip_app n of
      (\<^const_name>\<open>numeral\<close>, [b]) => (\<^const_name>\<open>uminus\<close>, [b])
    | _ => ("", []))
  | x => x);
\<close>

lemma nat_minus1_eq: "nat (- 1) = 0"
  by simp

ML \<open>
fun nat_conv i = (case strip_app i of
    (\<^const_name>\<open>zero_class.zero\<close>, []) => @{thm nat_0 [meta]}
  | (\<^const_name>\<open>one_class.one\<close>, []) => @{thm nat_one_as_int [meta, symmetric]}
  | (\<^const_name>\<open>numeral\<close>, [b]) => inst [] [b] @{thm nat_numeral [meta]}
  | (\<^const_name>\<open>uminus\<close>, [b]) => (case strip_app b of
      (\<^const_name>\<open>one_class.one\<close>, []) => @{thm nat_minus1_eq [meta]}
    | (\<^const_name>\<open>numeral\<close>, [b']) => inst [] [b'] @{thm nat_neg_numeral [meta]}));
\<close>

ML \<open>
fun add_num_conv b b' = (case (strip_app b, strip_app b') of
    ((\<^const_name>\<open>Num.One\<close>, []), (\<^const_name>\<open>Num.One\<close>, [])) =>
      @{thm add_num_simps(1) [meta]}
  | ((\<^const_name>\<open>Num.One\<close>, []), (\<^const_name>\<open>Num.Bit0\<close>, [n])) =>
      inst [] [n] @{thm add_num_simps(2) [meta]}
  | ((\<^const_name>\<open>Num.One\<close>, []), (\<^const_name>\<open>Num.Bit1\<close>, [n])) =>
      transitive'
        (inst [] [n] @{thm add_num_simps(3) [meta]})
        (cong1 (args2 add_num_conv))
  | ((\<^const_name>\<open>Num.Bit0\<close>, [m]), (\<^const_name>\<open>Num.One\<close>, [])) =>
      inst [] [m] @{thm add_num_simps(4) [meta]}
  | ((\<^const_name>\<open>Num.Bit0\<close>, [m]), (\<^const_name>\<open>Num.Bit0\<close>, [n])) =>
      transitive'
        (inst [] [m, n] @{thm add_num_simps(5) [meta]})
        (cong1 (args2 add_num_conv))
  | ((\<^const_name>\<open>Num.Bit0\<close>, [m]), (\<^const_name>\<open>Num.Bit1\<close>, [n])) =>
      transitive'
        (inst [] [m, n] @{thm add_num_simps(6) [meta]})
        (cong1 (args2 add_num_conv))
  | ((\<^const_name>\<open>Num.Bit1\<close>, [m]), (\<^const_name>\<open>Num.One\<close>, [])) =>
      transitive'
        (inst [] [m] @{thm add_num_simps(7) [meta]})
        (cong1 (args2 add_num_conv))
  | ((\<^const_name>\<open>Num.Bit1\<close>, [m]), (\<^const_name>\<open>Num.Bit0\<close>, [n])) =>
      transitive'
        (inst [] [m, n] @{thm add_num_simps(8) [meta]})
        (cong1 (args2 add_num_conv))
  | ((\<^const_name>\<open>Num.Bit1\<close>, [m]), (\<^const_name>\<open>Num.Bit1\<close>, [n])) =>
      transitive'
        (inst [] [m, n] @{thm add_num_simps(9) [meta]})
        (cong1 (cong2' add_num_conv (args2 add_num_conv) Thm.reflexive)));
\<close>

ML \<open>
fun BitM_conv m = (case strip_app m of
    (\<^const_name>\<open>Num.One\<close>, []) => @{thm BitM.simps(1) [meta]}
  | (\<^const_name>\<open>Num.Bit0\<close>, [n]) =>
      transitive'
        (inst [] [n] @{thm BitM.simps(2) [meta]})
        (cong1 (args1 BitM_conv))
  | (\<^const_name>\<open>Num.Bit1\<close>, [n]) =>
      inst [] [n] @{thm BitM.simps(3) [meta]});
\<close>

lemma dbl_neg_numeral:
  "Num.dbl (- Num.numeral k) = - Num.numeral (Num.Bit0 k)"
  by simp

ML \<open>
fun dbl_conv a =
  let
    val dbl_neg_numeral_a = inst [a] [] @{thm dbl_neg_numeral [meta]};
    val dbl_0_a = inst [a] [] @{thm dbl_simps(2) [meta]};
    val dbl_numeral_a = inst [a] [] @{thm dbl_simps(5) [meta]}
  in
    fn n =>
      case strip_numeral n of
        (\<^const_name>\<open>zero_class.zero\<close>, []) => dbl_0_a
      | (\<^const_name>\<open>numeral\<close>, [k]) => inst [] [k] dbl_numeral_a
      | (\<^const_name>\<open>uminus\<close>, [k]) => inst [] [k] dbl_neg_numeral_a
  end;
\<close>

lemma dbl_inc_neg_numeral:
  "Num.dbl_inc (- Num.numeral k) = - Num.numeral (Num.BitM k)"
  by simp

ML \<open>
fun dbl_inc_conv a =
  let
    val dbl_inc_neg_numeral_a = inst [a] [] @{thm dbl_inc_neg_numeral [meta]};
    val dbl_inc_0_a = inst [a] [] @{thm dbl_inc_simps(2) [folded numeral_One, meta]};
    val dbl_inc_numeral_a = inst [a] [] @{thm dbl_inc_simps(5) [meta]};
  in
    fn n =>
      case strip_numeral n of
        (\<^const_name>\<open>zero_class.zero\<close>, []) => dbl_inc_0_a
      | (\<^const_name>\<open>numeral\<close>, [k]) => inst [] [k] dbl_inc_numeral_a
      | (\<^const_name>\<open>uminus\<close>, [k]) =>
          transitive'
            (inst [] [k] dbl_inc_neg_numeral_a)
            (cong1 (cong1 (args1 BitM_conv)))
  end;
\<close>

lemma dbl_dec_neg_numeral:
  "Num.dbl_dec (- Num.numeral k) = - Num.numeral (Num.Bit1 k)"
  by simp

ML \<open>
fun dbl_dec_conv a =
  let
    val dbl_dec_neg_numeral_a = inst [a] [] @{thm dbl_dec_neg_numeral [meta]};
    val dbl_dec_0_a = inst [a] [] @{thm dbl_dec_simps(2) [folded numeral_One, meta]};
    val dbl_dec_numeral_a = inst [a] [] @{thm dbl_dec_simps(5) [meta]};
  in
    fn n =>
      case strip_numeral n of
        (\<^const_name>\<open>zero_class.zero\<close>, []) => dbl_dec_0_a
      | (\<^const_name>\<open>uminus\<close>, [k]) => inst [] [k] dbl_dec_neg_numeral_a
      | (\<^const_name>\<open>numeral\<close>, [k]) =>
          transitive'
            (inst [] [k] dbl_dec_numeral_a)
            (cong1 (args1 BitM_conv))
  end;
\<close>

ML \<open>
fun sub_conv a =
  let
    val [sub_One_One, sub_One_Bit0, sub_One_Bit1,
         sub_Bit0_One, sub_Bit1_One, sub_Bit0_Bit0,
         sub_Bit0_Bit1, sub_Bit1_Bit0, sub_Bit1_Bit1] =
      map (inst [a] []) @{thms sub_num_simps [meta]};
    val dbl_conv_a = dbl_conv a;
    val dbl_inc_conv_a = dbl_inc_conv a;
    val dbl_dec_conv_a = dbl_dec_conv a;

    fun conv m n = (case (strip_app m, strip_app n) of
        ((\<^const_name>\<open>Num.One\<close>, []), (\<^const_name>\<open>Num.One\<close>, [])) =>
          sub_One_One
      | ((\<^const_name>\<open>Num.One\<close>, []), (\<^const_name>\<open>Num.Bit0\<close>, [l])) =>
          transitive'
            (inst [] [l] sub_One_Bit0)
            (cong1 (cong1 (args1 BitM_conv)))
      | ((\<^const_name>\<open>Num.One\<close>, []), (\<^const_name>\<open>Num.Bit1\<close>, [l])) =>
          inst [] [l] sub_One_Bit1
      | ((\<^const_name>\<open>Num.Bit0\<close>, [k]), (\<^const_name>\<open>Num.One\<close>, [])) =>
          transitive'
            (inst [] [k] sub_Bit0_One)
            (cong1 (args1 BitM_conv))
      | ((\<^const_name>\<open>Num.Bit1\<close>, [k]), (\<^const_name>\<open>Num.One\<close>, [])) =>
          inst [] [k] sub_Bit1_One
      | ((\<^const_name>\<open>Num.Bit0\<close>, [k]), (\<^const_name>\<open>Num.Bit0\<close>, [l])) =>
          transitive'
            (inst [] [k, l] sub_Bit0_Bit0)
            (cong1' dbl_conv_a (args2 conv))
      | ((\<^const_name>\<open>Num.Bit0\<close>, [k]), (\<^const_name>\<open>Num.Bit1\<close>, [l])) =>
          transitive'
            (inst [] [k, l] sub_Bit0_Bit1)
            (cong1' dbl_dec_conv_a (args2 conv))
      | ((\<^const_name>\<open>Num.Bit1\<close>, [k]), (\<^const_name>\<open>Num.Bit0\<close>, [l])) =>
          transitive'
            (inst [] [k, l] sub_Bit1_Bit0)
            (cong1' dbl_inc_conv_a (args2 conv))
      | ((\<^const_name>\<open>Num.Bit1\<close>, [k]), (\<^const_name>\<open>Num.Bit1\<close>, [l])) =>
          transitive'
            (inst [] [k, l] sub_Bit1_Bit1)
            (cong1' dbl_conv_a (args2 conv)))
  in conv end;
\<close>

ML \<open>
fun expand1 a =
  let val numeral_1_eq_1_a = inst [a] [] @{thm numeral_One [meta, symmetric]}
  in
    fn n =>
      case Thm.term_of n of
        \<^Const_>\<open>one_class.one _\<close> => numeral_1_eq_1_a
      | \<^Const_>\<open>uminus _ for \<^Const_>\<open>one_class.one _\<close>\<close> =>
          Thm.combination (Thm.reflexive (Thm.dest_fun n)) numeral_1_eq_1_a
      | \<^Const_>\<open>zero_class.zero _\<close> => Thm.reflexive n
      | \<^Const_>\<open>numeral _ for _\<close> => Thm.reflexive n
      | \<^Const_>\<open>uminus _ for \<^Const_>\<open>numeral _ for _\<close>\<close> => Thm.reflexive n
      | _ => err "expand1" n
  end;

fun norm1_eq a =
  let val numeral_1_eq_1_a = inst [a] [] @{thm numeral_One [meta]}
  in
    fn eq =>
      case Thm.term_of (Thm.rhs_of eq) of
        \<^Const_>\<open>Num.numeral _ for \<^Const_>\<open>Num.One\<close>\<close> => Thm.transitive eq numeral_1_eq_1_a
      | \<^Const_>\<open>uminus _ for \<^Const_>\<open>Num.numeral _ for \<^Const_>\<open>Num.One\<close>\<close>\<close> =>
            Thm.transitive eq
              (Thm.combination (Thm.reflexive (Thm.dest_fun (Thm.rhs_of eq)))
                 numeral_1_eq_1_a)
      | _ => eq
  end;
\<close>

ML \<open>
fun plus_conv f a =
  let
    val add_0_a = inst [a] [] @{thm add_0 [meta]};
    val add_0_right_a = inst [a] [] @{thm add_0_right [meta]};
    val numeral_plus_numeral_a = inst [a] [] @{thm numeral_plus_numeral [meta]};
    val expand1_a = expand1 a;

    fun conv m n = (case (strip_app m, strip_app n) of
        ((\<^const_name>\<open>zero_class.zero\<close>, []), _) => inst [] [n] add_0_a
      | (_, (\<^const_name>\<open>zero_class.zero\<close>, [])) => inst [] [m] add_0_right_a
      | ((\<^const_name>\<open>numeral\<close>, [m]), (\<^const_name>\<open>numeral\<close>, [n])) =>
          transitive'
            (inst [] [m, n] numeral_plus_numeral_a)
            (cong1 (args2 add_num_conv))
      | _ => cong2'' (f conv) (expand1_a m) (expand1_a n))
  in f conv end;

val nat_plus_conv = plus_conv I \<^ctyp>\<open>nat\<close>;
\<close>

lemma neg_numeral_plus_neg_numeral:
  "- Num.numeral m + - Num.numeral n = (- Num.numeral (m + n) ::'a::neg_numeral)"
  by simp

ML \<open>
fun plus_neg_conv a =
  let
    val numeral_plus_neg_numeral_a =
      inst [a] [] @{thm add_neg_numeral_simps(1) [meta]};
    val neg_numeral_plus_numeral_a =
      inst [a] [] @{thm add_neg_numeral_simps(2) [meta]};
    val neg_numeral_plus_neg_numeral_a =
      inst [a] [] @{thm neg_numeral_plus_neg_numeral [meta]};
    val sub_conv_a = sub_conv a;
  in
    fn conv => fn m => fn n => 
      case (strip_numeral m, strip_numeral n) of
        ((\<^const_name>\<open>Num.numeral\<close>, [m]), (\<^const_name>\<open>uminus\<close>, [n])) =>
          Thm.transitive
            (inst [] [m, n] numeral_plus_neg_numeral_a)
            (sub_conv_a m n)
      | ((\<^const_name>\<open>uminus\<close>, [m]), (\<^const_name>\<open>Num.numeral\<close>, [n])) =>
          Thm.transitive
            (inst [] [m, n] neg_numeral_plus_numeral_a)
            (sub_conv_a n m)
      | ((\<^const_name>\<open>uminus\<close>, [m]), (\<^const_name>\<open>uminus\<close>, [n])) =>
          transitive'
            (inst [] [m, n] neg_numeral_plus_neg_numeral_a)
            (cong1 (cong1 (args2 add_num_conv)))
      | _ => conv m n
  end;

fun plus_conv' a = norm1_eq a oo plus_conv (plus_neg_conv a) a;

val int_plus_conv = plus_conv' \<^ctyp>\<open>int\<close>;
\<close>

lemma minus_one: "- 1 = - 1" by simp
lemma minus_numeral: "- numeral b = - numeral b" by simp

ML \<open>
fun uminus_conv a =
  let
    val minus_zero_a = inst [a] [] @{thm minus_zero [meta]};
    val minus_one_a = inst [a] [] @{thm minus_one [meta]};
    val minus_numeral_a = inst [a] [] @{thm minus_numeral [meta]};
    val minus_minus_a = inst [a] [] @{thm minus_minus [meta]}
  in
    fn n =>
      case strip_app n of
        (\<^const_name>\<open>zero_class.zero\<close>, []) => minus_zero_a
      | (\<^const_name>\<open>one_class.one\<close>, []) => minus_one_a
      | (\<^const_name>\<open>Num.numeral\<close>, [m]) => inst [] [m] minus_numeral_a
      | (\<^const_name>\<open>uminus\<close>, [m]) => inst [] [m] minus_minus_a
  end;

val int_neg_conv = uminus_conv \<^ctyp>\<open>int\<close>;
\<close>

ML \<open>
fun minus_conv a =
  let
    val [numeral_minus_numeral_a, numeral_minus_neg_numeral_a,
         neg_numeral_minus_numeral_a, neg_numeral_minus_neg_numeral_a] =
      map (inst [a] []) @{thms diff_numeral_simps [meta]};
    val diff_0_a = inst [a] [] @{thm diff_0 [meta]};
    val diff_0_right_a = inst [a] [] @{thm diff_0_right [meta]};
    val sub_conv_a = sub_conv a;
    val uminus_conv_a = uminus_conv a;
    val expand1_a = expand1 a;
    val norm1_eq_a = norm1_eq a;

    fun conv m n = (case (strip_numeral m, strip_numeral n) of
        ((\<^const_name>\<open>zero_class.zero\<close>, []), _) =>
          Thm.transitive (inst [] [n] diff_0_a) (uminus_conv_a n)
      | (_, (\<^const_name>\<open>zero_class.zero\<close>, [])) => inst [] [m] diff_0_right_a
      | ((\<^const_name>\<open>Num.numeral\<close>, [m]), (\<^const_name>\<open>Num.numeral\<close>, [n])) =>
          Thm.transitive
            (inst [] [m, n] numeral_minus_numeral_a)
            (sub_conv_a m n)
      | ((\<^const_name>\<open>Num.numeral\<close>, [m]), (\<^const_name>\<open>uminus\<close>, [n])) =>
          transitive'
            (inst [] [m, n] numeral_minus_neg_numeral_a)
            (cong1 (args2 add_num_conv))
      | ((\<^const_name>\<open>uminus\<close>, [m]), (\<^const_name>\<open>Num.numeral\<close>, [n])) =>
          transitive'
            (inst [] [m, n] neg_numeral_minus_numeral_a)
            (cong1 (cong1 (args2 add_num_conv)))
      | ((\<^const_name>\<open>uminus\<close>, [m]), (\<^const_name>\<open>uminus\<close>, [n])) =>
          Thm.transitive
            (inst [] [m, n] neg_numeral_minus_neg_numeral_a)
            (sub_conv_a n m)
      | _ => cong2'' conv (expand1_a m) (expand1_a n))
  in norm1_eq_a oo conv end;

val int_minus_conv = minus_conv \<^ctyp>\<open>int\<close>;
\<close>

ML \<open>
val int_numeral = Thm.apply \<^cterm>\<open>numeral :: num \<Rightarrow> int\<close>;

val nat_minus_refl = Thm.reflexive \<^cterm>\<open>minus :: nat \<Rightarrow> nat \<Rightarrow> nat\<close>;

val expand1_nat = expand1 \<^ctyp>\<open>nat\<close>;

fun nat_minus_conv m n = (case (strip_app m, strip_app n) of
    ((\<^const_name>\<open>zero_class.zero\<close>, []), _) =>
      inst [] [n] @{thm diff_0_eq_0 [meta]}
  | (_, (\<^const_name>\<open>zero_class.zero\<close>, [])) =>
      inst [] [m] @{thm minus_nat.diff_0 [meta]}
  | ((\<^const_name>\<open>numeral\<close>, [m]), (\<^const_name>\<open>numeral\<close>, [n])) =>
      transitive'
        (inst [] [m, n] @{thm diff_nat_numeral [meta]})
        (cong1' nat_conv (args2 int_minus_conv))
  | _ => cong2'' nat_minus_conv (expand1_nat m) (expand1_nat n));
\<close>

ML \<open>
fun mult_num_conv m n = (case (strip_app m, strip_app n) of
    (_, (\<^const_name>\<open>Num.One\<close>, [])) =>
      inst [] [m] @{thm mult_num_simps(1) [meta]}
  | ((\<^const_name>\<open>Num.One\<close>, []), _) =>
      inst [] [n] @{thm mult_num_simps(2) [meta]}
  | ((\<^const_name>\<open>Num.Bit0\<close>, [m]), (\<^const_name>\<open>Num.Bit0\<close>, [n])) =>
      transitive'
        (inst [] [m, n] @{thm mult_num_simps(3) [meta]})
        (cong1 (cong1 (args2 mult_num_conv)))
  | ((\<^const_name>\<open>Num.Bit0\<close>, [m]), (\<^const_name>\<open>Num.Bit1\<close>, [n'])) =>
      transitive'
        (inst [] [m, n'] @{thm mult_num_simps(4) [meta]})
        (cong1 (args2 mult_num_conv))
  | ((\<^const_name>\<open>Num.Bit1\<close>, [m']), (\<^const_name>\<open>Num.Bit0\<close>, [n])) =>
      transitive'
        (inst [] [m', n] @{thm mult_num_simps(5) [meta]})
        (cong1 (args2 mult_num_conv))
  | ((\<^const_name>\<open>Num.Bit1\<close>, [m]), (\<^const_name>\<open>Num.Bit1\<close>, [n])) =>
      transitive'
        (inst [] [m, n] @{thm mult_num_simps(6) [meta]})
        (cong1 (cong2' add_num_conv
           (args2 add_num_conv)
           (cong1 (args2 mult_num_conv)))));
\<close>

ML \<open>
fun mult_conv f a =
  let
    val mult_zero_left_a = inst [a] [] @{thm mult_zero_left [meta]};
    val mult_zero_right_a = inst [a] [] @{thm mult_zero_right [meta]};
    val numeral_times_numeral_a = inst [a] [] @{thm numeral_times_numeral [meta]};
    val expand1_a = expand1 a;
    val norm1_eq_a = norm1_eq a;

    fun conv m n = (case (strip_app m, strip_app n) of
        ((\<^const_name>\<open>zero_class.zero\<close>, []), _) => inst [] [n] mult_zero_left_a
      | (_, (\<^const_name>\<open>zero_class.zero\<close>, [])) => inst [] [m] mult_zero_right_a
      | ((\<^const_name>\<open>numeral\<close>, [m]), (\<^const_name>\<open>numeral\<close>, [n])) =>
          transitive'
            (inst [] [m, n] numeral_times_numeral_a)
            (cong1 (args2 mult_num_conv))
      | _ => cong2'' (f conv) (expand1_a m) (expand1_a n))
  in norm1_eq_a oo f conv end;

val nat_mult_conv = mult_conv I \<^ctyp>\<open>nat\<close>;
\<close>

ML \<open>
fun mult_neg_conv a =
  let
    val [neg_numeral_times_neg_numeral_a, neg_numeral_times_numeral_a,
         numeral_times_neg_numeral_a] =
      map (inst [a] []) @{thms mult_neg_numeral_simps [meta]};
  in
    fn conv => fn m => fn n =>
      case (strip_numeral m, strip_numeral n) of
        ((\<^const_name>\<open>uminus\<close>, [m]), (\<^const_name>\<open>uminus\<close>, [n])) =>
          transitive'
            (inst [] [m, n] neg_numeral_times_neg_numeral_a)
            (cong1 (args2 mult_num_conv))
      | ((\<^const_name>\<open>uminus\<close>, [m]), (\<^const_name>\<open>numeral\<close>, [n])) =>
          transitive'
            (inst [] [m, n] neg_numeral_times_numeral_a)
            (cong1 (cong1 (args2 mult_num_conv)))
      | ((\<^const_name>\<open>numeral\<close>, [m]), (\<^const_name>\<open>uminus\<close>, [n])) =>
          transitive'
            (inst [] [m, n] numeral_times_neg_numeral_a)
            (cong1 (cong1 (args2 mult_num_conv)))
      | _ => conv m n
  end;

fun mult_conv' a = mult_conv (mult_neg_conv a) a;

val int_mult_conv = mult_conv' \<^ctyp>\<open>int\<close>;
\<close>

ML \<open>
fun eq_num_conv m n = (case (strip_app m, strip_app n) of
    ((\<^const_name>\<open>Num.One\<close>, []), (\<^const_name>\<open>Num.One\<close>, [])) =>
      @{thm eq_num_simps(1) [meta]}
  | ((\<^const_name>\<open>Num.One\<close>, []), (\<^const_name>\<open>Num.Bit0\<close>, [n])) =>
      inst [] [n] @{thm eq_num_simps(2) [meta]}
  | ((\<^const_name>\<open>Num.One\<close>, []), (\<^const_name>\<open>Num.Bit1\<close>, [n])) =>
      inst [] [n] @{thm eq_num_simps(3) [meta]}
  | ((\<^const_name>\<open>Num.Bit0\<close>, [m]), (\<^const_name>\<open>Num.One\<close>, [])) =>
      inst [] [m] @{thm eq_num_simps(4) [meta]}
  | ((\<^const_name>\<open>Num.Bit1\<close>, [m]), (\<^const_name>\<open>Num.One\<close>, [])) =>
      inst [] [m] @{thm eq_num_simps(5) [meta]}
  | ((\<^const_name>\<open>Num.Bit0\<close>, [m]), (\<^const_name>\<open>Num.Bit0\<close>, [n])) =>
      Thm.transitive
        (inst [] [m, n] @{thm eq_num_simps(6) [meta]})
        (eq_num_conv m n)
  | ((\<^const_name>\<open>Num.Bit0\<close>, [m]), (\<^const_name>\<open>Num.Bit1\<close>, [n])) =>
      inst [] [m, n] @{thm eq_num_simps(7) [meta]}
  | ((\<^const_name>\<open>Num.Bit1\<close>, [m]), (\<^const_name>\<open>Num.Bit0\<close>, [n])) =>
      inst [] [m, n] @{thm eq_num_simps(8) [meta]}
  | ((\<^const_name>\<open>Num.Bit1\<close>, [m]), (\<^const_name>\<open>Num.Bit1\<close>, [n])) =>
      Thm.transitive
        (inst [] [m, n] @{thm eq_num_simps(9) [meta]})
        (eq_num_conv m n));
\<close>

ML \<open>
fun eq_conv f a =
  let
    val zero_eq_zero_a = inst [a] [] @{thm refl [of 0, THEN Eq_TrueI]};
    val zero_neq_numeral_a =
      inst [a] [] @{thm zero_neq_numeral [THEN Eq_FalseI]};
    val numeral_neq_zero_a =
      inst [a] [] @{thm numeral_neq_zero [THEN Eq_FalseI]};
    val numeral_eq_iff_a = inst [a] [] @{thm numeral_eq_iff [meta]};
    val expand1_a = expand1 a;

    fun conv m n = (case (strip_app m, strip_app n) of
        ((\<^const_name>\<open>zero_class.zero\<close>, []), (\<^const_name>\<open>zero_class.zero\<close>, [])) =>
          zero_eq_zero_a
      | ((\<^const_name>\<open>zero_class.zero\<close>, []), (\<^const_name>\<open>numeral\<close>, [n])) =>
          inst [] [n] zero_neq_numeral_a
      | ((\<^const_name>\<open>numeral\<close>, [m]), (\<^const_name>\<open>zero_class.zero\<close>, [])) =>
          inst [] [m] numeral_neq_zero_a
      | ((\<^const_name>\<open>numeral\<close>, [m]), (\<^const_name>\<open>numeral\<close>, [n])) =>
          Thm.transitive
            (inst [] [m, n] numeral_eq_iff_a)
            (eq_num_conv m n)
      | _ => cong2'' (f conv) (expand1_a m) (expand1_a n))
  in f conv end;

val nat_eq_conv = eq_conv I \<^ctyp>\<open>nat\<close>;
\<close>

ML \<open>
fun eq_neg_conv a =
  let
    val neg_numeral_neq_zero_a =
      inst [a] [] @{thm neg_numeral_neq_zero [THEN Eq_FalseI]};
    val zero_neq_neg_numeral_a =
      inst [a] [] @{thm zero_neq_neg_numeral [THEN Eq_FalseI]};
    val neg_numeral_neq_numeral_a =
      inst [a] [] @{thm neg_numeral_neq_numeral [THEN Eq_FalseI]};
    val numeral_neq_neg_numeral_a =
      inst [a] [] @{thm numeral_neq_neg_numeral [THEN Eq_FalseI]};
    val neg_numeral_eq_iff_a = inst [a] [] @{thm neg_numeral_eq_iff [meta]}
  in
    fn conv => fn m => fn n => 
      case (strip_numeral m, strip_numeral n) of
        ((\<^const_name>\<open>uminus\<close>, [m]), (\<^const_name>\<open>zero_class.zero\<close>, [])) =>
          inst [] [m] neg_numeral_neq_zero_a
      | ((\<^const_name>\<open>zero_class.zero\<close>, []), (\<^const_name>\<open>uminus\<close>, [n])) =>
          inst [] [n] zero_neq_neg_numeral_a
      | ((\<^const_name>\<open>Num.numeral\<close>, [m]), (\<^const_name>\<open>uminus\<close>, [n])) =>
          inst [] [m, n] numeral_neq_neg_numeral_a
      | ((\<^const_name>\<open>uminus\<close>, [m]), (\<^const_name>\<open>Num.numeral\<close>, [n])) =>
          inst [] [m, n] neg_numeral_neq_numeral_a
      | ((\<^const_name>\<open>uminus\<close>, [m]), (\<^const_name>\<open>uminus\<close>, [n])) =>
          Thm.transitive
            (inst [] [m, n] neg_numeral_eq_iff_a)
            (eq_num_conv m n)
      | _ => conv m n
  end;

fun eq_conv' a = eq_conv (eq_neg_conv a) a;

val int_eq_conv = eq_conv' \<^ctyp>\<open>int\<close>;
\<close>

ML \<open>
fun le_num_conv m n = (case (strip_app m, strip_app n) of
    ((\<^const_name>\<open>Num.One\<close>, []), _) =>
      inst [] [n] @{thm le_num_simps(1) [meta]}
  | ((\<^const_name>\<open>Num.Bit0\<close>, [m]), (\<^const_name>\<open>Num.One\<close>, [])) =>
      inst [] [m] @{thm le_num_simps(2) [meta]}
  | ((\<^const_name>\<open>Num.Bit1\<close>, [m]), (\<^const_name>\<open>Num.One\<close>, [])) =>
      inst [] [m] @{thm le_num_simps(3) [meta]}
  | ((\<^const_name>\<open>Num.Bit0\<close>, [m]), (\<^const_name>\<open>Num.Bit0\<close>, [n])) =>
      Thm.transitive
        (inst [] [m, n] @{thm le_num_simps(4) [meta]})
        (le_num_conv m n)
  | ((\<^const_name>\<open>Num.Bit0\<close>, [m]), (\<^const_name>\<open>Num.Bit1\<close>, [n])) =>
      Thm.transitive
        (inst [] [m, n] @{thm le_num_simps(5) [meta]})
        (le_num_conv m n)
  | ((\<^const_name>\<open>Num.Bit1\<close>, [m]), (\<^const_name>\<open>Num.Bit1\<close>, [n])) =>
      Thm.transitive
        (inst [] [m, n] @{thm le_num_simps(6) [meta]})
        (le_num_conv m n)
  | ((\<^const_name>\<open>Num.Bit1\<close>, [m]), (\<^const_name>\<open>Num.Bit0\<close>, [n])) =>
      Thm.transitive
        (inst [] [m, n] @{thm le_num_simps(7) [meta]})
        (less_num_conv m n))

and less_num_conv m n = (case (strip_app m, strip_app n) of
    (_, (\<^const_name>\<open>Num.One\<close>, [])) =>
      inst [] [m] @{thm less_num_simps(1) [meta]}
  | ((\<^const_name>\<open>Num.One\<close>, []), (\<^const_name>\<open>Num.Bit0\<close>, [n])) =>
      inst [] [n] @{thm less_num_simps(2) [meta]}
  | ((\<^const_name>\<open>Num.One\<close>, []), (\<^const_name>\<open>Num.Bit1\<close>, [n])) =>
      inst [] [n] @{thm less_num_simps(3) [meta]}
  | ((\<^const_name>\<open>Num.Bit0\<close>, [m]), (\<^const_name>\<open>Num.Bit0\<close>, [n])) =>
      Thm.transitive
        (inst [] [m, n] @{thm less_num_simps(4) [meta]})
        (less_num_conv m n)
  | ((\<^const_name>\<open>Num.Bit0\<close>, [m]), (\<^const_name>\<open>Num.Bit1\<close>, [n])) =>
      Thm.transitive
        (inst [] [m, n] @{thm less_num_simps(5) [meta]})
        (le_num_conv m n)
  | ((\<^const_name>\<open>Num.Bit1\<close>, [m]), (\<^const_name>\<open>Num.Bit1\<close>, [n])) =>
      Thm.transitive
        (inst [] [m, n] @{thm less_num_simps(6) [meta]})
        (less_num_conv m n)
  | ((\<^const_name>\<open>Num.Bit1\<close>, [m]), (\<^const_name>\<open>Num.Bit0\<close>, [n])) =>
      Thm.transitive
        (inst [] [m, n] @{thm less_num_simps(7) [meta]})
        (less_num_conv m n));
\<close>

ML \<open>
fun le_conv f a =
  let
    val zero_le_zero_a = inst [a] [] @{thm order_refl [of 0, THEN Eq_TrueI]};
    val zero_le_numeral_a =
      inst [a] [] @{thm zero_le_numeral [THEN Eq_TrueI]};
    val not_numeral_le_zero_a =
      inst [a] [] @{thm not_numeral_le_zero [THEN Eq_FalseI]};
    val numeral_le_iff_a = inst [a] [] @{thm numeral_le_iff [meta]};
    val expand1_a = expand1 a;

    fun conv m n = (case (strip_app m, strip_app n) of
        ((\<^const_name>\<open>zero_class.zero\<close>, []), (\<^const_name>\<open>zero_class.zero\<close>, [])) =>
          zero_le_zero_a
      | ((\<^const_name>\<open>zero_class.zero\<close>, []), (\<^const_name>\<open>numeral\<close>, [n])) =>
          inst [] [n] zero_le_numeral_a
      | ((\<^const_name>\<open>numeral\<close>, [m]), (\<^const_name>\<open>zero_class.zero\<close>, [])) =>
          inst [] [m] not_numeral_le_zero_a
      | ((\<^const_name>\<open>numeral\<close>, [m]), (\<^const_name>\<open>numeral\<close>, [n])) =>
          Thm.transitive
            (inst [] [m, n] numeral_le_iff_a)
            (le_num_conv m n)
      | _ => cong2'' (f conv) (expand1_a m) (expand1_a n))
  in f conv end;

val nat_le_conv = le_conv I \<^ctyp>\<open>nat\<close>;
\<close>

ML \<open>
fun le_neg_conv a =
  let
    val neg_numeral_le_zero_a =
      inst [a] [] @{thm neg_numeral_le_zero [THEN Eq_TrueI]};
    val not_zero_le_neg_numeral_a =
      inst [a] [] @{thm not_zero_le_neg_numeral [THEN Eq_FalseI]};
    val neg_numeral_le_numeral_a =
      inst [a] [] @{thm neg_numeral_le_numeral [THEN Eq_TrueI]};
    val not_numeral_le_neg_numeral_a =
      inst [a] [] @{thm not_numeral_le_neg_numeral [THEN Eq_FalseI]};
    val neg_numeral_le_iff_a = inst [a] [] @{thm neg_numeral_le_iff [meta]}
  in
    fn conv => fn m => fn n => 
      case (strip_numeral m, strip_numeral n) of
        ((\<^const_name>\<open>uminus\<close>, [m]), (\<^const_name>\<open>zero_class.zero\<close>, [])) =>
          inst [] [m] neg_numeral_le_zero_a
      | ((\<^const_name>\<open>zero_class.zero\<close>, []), (\<^const_name>\<open>uminus\<close>, [n])) =>
          inst [] [n] not_zero_le_neg_numeral_a
      | ((\<^const_name>\<open>Num.numeral\<close>, [m]), (\<^const_name>\<open>uminus\<close>, [n])) =>
          inst [] [m, n] not_numeral_le_neg_numeral_a
      | ((\<^const_name>\<open>uminus\<close>, [m]), (\<^const_name>\<open>Num.numeral\<close>, [n])) =>
          inst [] [m, n] neg_numeral_le_numeral_a
      | ((\<^const_name>\<open>uminus\<close>, [m]), (\<^const_name>\<open>uminus\<close>, [n])) =>
          Thm.transitive
            (inst [] [m, n] neg_numeral_le_iff_a)
            (le_num_conv n m)
      | _ => conv m n
  end;

fun le_conv' a = le_conv (le_neg_conv a) a;

val int_le_conv = le_conv' \<^ctyp>\<open>int\<close>;
\<close>

ML \<open>
fun less_conv f a =
  let
    val not_zero_less_zero_a = inst [a] [] @{thm less_irrefl [of 0, THEN Eq_FalseI]};
    val zero_less_numeral_a =
      inst [a] [] @{thm zero_less_numeral [THEN Eq_TrueI]};
    val not_numeral_less_zero_a =
      inst [a] [] @{thm not_numeral_less_zero [THEN Eq_FalseI]};
    val numeral_less_iff_a = inst [a] [] @{thm numeral_less_iff [meta]};
    val expand1_a = expand1 a;

    fun conv m n = (case (strip_app m, strip_app n) of
        ((\<^const_name>\<open>zero_class.zero\<close>, []), (\<^const_name>\<open>zero_class.zero\<close>, [])) =>
          not_zero_less_zero_a
      | ((\<^const_name>\<open>zero_class.zero\<close>, []), (\<^const_name>\<open>numeral\<close>, [n])) =>
          inst [] [n] zero_less_numeral_a
      | ((\<^const_name>\<open>numeral\<close>, [m]), (\<^const_name>\<open>zero_class.zero\<close>, [])) =>
          inst [] [m] not_numeral_less_zero_a
      | ((\<^const_name>\<open>numeral\<close>, [m]), (\<^const_name>\<open>numeral\<close>, [n])) =>
          Thm.transitive
            (inst [] [m, n] numeral_less_iff_a)
            (less_num_conv m n)
      | _ => cong2'' (f conv) (expand1_a m) (expand1_a n))
  in f conv end;

val nat_less_conv = less_conv I \<^ctyp>\<open>nat\<close>;
\<close>

ML \<open>
fun less_neg_conv a =
  let
    val neg_numeral_less_zero_a =
      inst [a] [] @{thm neg_numeral_less_zero [THEN Eq_TrueI]};
    val not_zero_less_neg_numeral_a =
      inst [a] [] @{thm not_zero_less_neg_numeral [THEN Eq_FalseI]};
    val neg_numeral_less_numeral_a =
      inst [a] [] @{thm neg_numeral_less_numeral [THEN Eq_TrueI]};
    val not_numeral_less_neg_numeral_a =
      inst [a] [] @{thm not_numeral_less_neg_numeral [THEN Eq_FalseI]};
    val neg_numeral_less_iff_a = inst [a] [] @{thm neg_numeral_less_iff [meta]}
  in
    fn conv => fn m => fn n => 
      case (strip_numeral m, strip_numeral n) of
        ((\<^const_name>\<open>uminus\<close>, [m]), (\<^const_name>\<open>zero_class.zero\<close>, [])) =>
          inst [] [m] neg_numeral_less_zero_a
      | ((\<^const_name>\<open>zero_class.zero\<close>, []), (\<^const_name>\<open>uminus\<close>, [n])) =>
          inst [] [n] not_zero_less_neg_numeral_a
      | ((\<^const_name>\<open>Num.numeral\<close>, [m]), (\<^const_name>\<open>uminus\<close>, [n])) =>
          inst [] [m, n] not_numeral_less_neg_numeral_a
      | ((\<^const_name>\<open>uminus\<close>, [m]), (\<^const_name>\<open>Num.numeral\<close>, [n])) =>
          inst [] [m, n] neg_numeral_less_numeral_a
      | ((\<^const_name>\<open>uminus\<close>, [m]), (\<^const_name>\<open>uminus\<close>, [n])) =>
          Thm.transitive
            (inst [] [m, n] neg_numeral_less_iff_a)
            (less_num_conv n m)
      | _ => conv m n
  end;

fun less_conv' a = less_conv (less_neg_conv a) a;

val int_less_conv = less_conv' \<^ctyp>\<open>int\<close>;
\<close>

ML \<open>
fun If_conv a =
  let
    val if_True = inst [a] [] @{thm if_True [meta]};
    val if_False = inst [a] [] @{thm if_False [meta]}
  in
    fn p => fn x => fn y => fn ct =>
      case strip_app ct of
        (\<^const_name>\<open>If\<close>, [cb, cx, cy]) =>
          let
            val p_eq = p cb
            val eq = Thm.combination (Thm.reflexive (Thm.dest_fun (Thm.dest_fun2 ct))) p_eq
          in
            case Thm.term_of (Thm.rhs_of p_eq) of
              \<^Const_>\<open>True\<close> =>
                let
                  val x_eq = x cx;
                  val cx = Thm.rhs_of x_eq;
                in
                  Thm.transitive
                    (Thm.combination
                       (Thm.combination eq x_eq)
                       (Thm.reflexive cy))
                    (inst [] [cx, cy] if_True)
                end
            | \<^Const_>\<open>False\<close> =>
                let
                  val y_eq = y cy;
                  val cy = Thm.rhs_of y_eq;
                in
                  Thm.transitive
                    (Thm.combination
                       (Thm.combination eq (Thm.reflexive cx))
                       y_eq)
                    (inst [] [cx, cy] if_False)
                end
            | _ => err "If_conv" (Thm.rhs_of p_eq)
          end
  end;
\<close>

ML \<open>
fun drop_conv a =
  let
    val drop_0_a = inst [a] [] @{thm drop_0 [meta]};
    val drop_Cons_a = inst [a] [] @{thm drop_Cons' [meta]};
    val If_conv_a = If_conv (type_of_eqn drop_0_a);

    fun conv n ys = (case Thm.term_of n of
        \<^Const_>\<open>zero_class.zero _\<close> => inst [] [ys] drop_0_a
      | _ => (case strip_app ys of
          (\<^const_name>\<open>Cons\<close>, [x, xs]) =>
            transitive'
              (inst [] [n, x, xs] drop_Cons_a)
              (If_conv_a (args2 nat_eq_conv)
                 Thm.reflexive
                 (cong2' conv (args2 nat_minus_conv) Thm.reflexive))))
  in conv end;
\<close>

ML \<open>
fun nth_conv a =
  let
    val nth_Cons_a = inst [a] [] @{thm nth_Cons' [meta]};
    val If_conv_a = If_conv a;

    fun conv ys n = (case strip_app ys of
        (\<^const_name>\<open>Cons\<close>, [x, xs]) =>
          transitive'
            (inst [] [x, xs, n] nth_Cons_a)
            (If_conv_a (args2 nat_eq_conv)
               Thm.reflexive
               (cong2' conv Thm.reflexive (args2 nat_minus_conv))))
  in conv end;
\<close>

end
