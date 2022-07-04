(*  Title:      HOL/Library/Code_Abstract_Char.thy
    Author:     Florian Haftmann, TU Muenchen
    Author:     René Thiemann, UIBK
*)

theory Code_Abstract_Char
  imports 
    Main
    "HOL-Library.Char_ord" 
begin

definition Chr :: \<open>integer \<Rightarrow> char\<close>
  where [simp]: \<open>Chr = char_of\<close>

lemma char_of_integer_of_char [code abstype]:
  \<open>Chr (integer_of_char c) = c\<close>
  by (simp add: integer_of_char_def)

lemma char_of_integer_code [code]:
  \<open>integer_of_char (char_of_integer k) = take_bit 8 k\<close>
  by (simp add: integer_of_char_def char_of_integer_def take_bit_eq_mod)

context comm_semiring_1
begin

definition byte :: \<open>bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> 'a\<close>
  where [simp]: \<open>byte b0 b1 b2 b3 b4 b5 b6 b7 = horner_sum of_bool 2 [b0, b1, b2, b3, b4, b5, b6, b7]\<close>

lemma byte_code [code]:
  \<open>byte b0 b1 b2 b3 b4 b5 b6 b7 = (
    let
      s0 = if b0 then 1 else 0;
      s1 = if b1 then s0 + 2 else s0;
      s2 = if b2 then s1 + 4 else s1;
      s3 = if b3 then s2 + 8 else s2;
      s4 = if b4 then s3 + 16 else s3;
      s5 = if b5 then s4 + 32 else s4;
      s6 = if b6 then s5 + 64 else s5;
      s7 = if b7 then s6 + 128 else s6
    in s7)\<close>
  by simp

end

lemma Char_code [code]:
  \<open>integer_of_char (Char b0 b1 b2 b3 b4 b5 b6 b7) = byte b0 b1 b2 b3 b4 b5 b6 b7\<close>
  by (simp add: integer_of_char_def)
                     
lemma digit_0_code [code]:
  \<open>digit0 c \<longleftrightarrow> bit (integer_of_char c) 0\<close>
  by (cases c) (simp add: integer_of_char_def)

lemma digit_1_code [code]:
  \<open>digit1 c \<longleftrightarrow> bit (integer_of_char c) 1\<close>
  by (cases c) (simp add: integer_of_char_def)

lemma digit_2_code [code]:
  \<open>digit2 c \<longleftrightarrow> bit (integer_of_char c) 2\<close>
  by (cases c) (simp add: integer_of_char_def)

lemma digit_3_code [code]:
  \<open>digit3 c \<longleftrightarrow> bit (integer_of_char c) 3\<close>
  by (cases c) (simp add: integer_of_char_def)

lemma digit_4_code [code]:
  \<open>digit4 c \<longleftrightarrow> bit (integer_of_char c) 4\<close>
  by (cases c) (simp add: integer_of_char_def)

lemma digit_5_code [code]:
  \<open>digit5 c \<longleftrightarrow> bit (integer_of_char c) 5\<close>
  by (cases c) (simp add: integer_of_char_def)

lemma digit_6_code [code]:
  \<open>digit6 c \<longleftrightarrow> bit (integer_of_char c) 6\<close>
  by (cases c) (simp add: integer_of_char_def)

lemma digit_7_code [code]:
  \<open>digit7 c \<longleftrightarrow> bit (integer_of_char c) 7\<close>
  by (cases c) (simp add: integer_of_char_def)

lemma case_char_code [code]:
  \<open>case_char f c = f (digit0 c) (digit1 c) (digit2 c) (digit3 c) (digit4 c) (digit5 c) (digit6 c) (digit7 c)\<close>
  by (fact char.case_eq_if)

lemma rec_char_code [code]:
  \<open>rec_char f c = f (digit0 c) (digit1 c) (digit2 c) (digit3 c) (digit4 c) (digit5 c) (digit6 c) (digit7 c)\<close>
  by (cases c) simp

lemma char_of_code [code]:
  \<open>integer_of_char (char_of a) =
    byte (bit a 0) (bit a 1) (bit a 2) (bit a 3) (bit a 4) (bit a 5) (bit a 6) (bit a 7)\<close>
  by (simp add: char_of_def integer_of_char_def)

lemma ascii_of_code [code]:
  \<open>integer_of_char (String.ascii_of c) = (let k = integer_of_char c in if k < 128 then k else k - 128)\<close>
proof (cases \<open>of_char c < (128 :: integer)\<close>)
  case True
  moreover have \<open>(of_nat 0 :: integer) \<le> of_nat (of_char c)\<close>
    by simp
  then have \<open>(0 :: integer) \<le> of_char c\<close>
    by (simp only: of_nat_0 of_nat_of_char)
  ultimately show ?thesis
    by (simp add: Let_def integer_of_char_def take_bit_eq_mod unique_euclidean_semiring_numeral_class.mod_less)
next
  case False
  then have \<open>(128 :: integer) \<le> of_char c\<close>
    by simp
  moreover have \<open>of_nat (of_char c) < (of_nat 256 :: integer)\<close>
    by (simp only: of_nat_less_iff) simp
  then have \<open>of_char c < (256 :: integer)\<close>
    by (simp add: of_nat_of_char)
  moreover define k :: integer where \<open>k = of_char c - 128\<close>
  then have \<open>of_char c = k + 128\<close>
    by simp
  ultimately show ?thesis
    by (simp add: Let_def integer_of_char_def take_bit_eq_mod unique_euclidean_semiring_numeral_class.mod_less)
qed    

lemma equal_char_code [code]:
  \<open>HOL.equal c d \<longleftrightarrow> integer_of_char c = integer_of_char d\<close>
  by (simp add: integer_of_char_def equal)

lemma less_eq_char_code [code]:
  \<open>c \<le> d \<longleftrightarrow> integer_of_char c \<le> integer_of_char d\<close> (is \<open>?P \<longleftrightarrow> ?Q\<close>)
proof -
  have \<open>?P \<longleftrightarrow> of_nat (of_char c) \<le> (of_nat (of_char d) :: integer)\<close>
    by (simp add: less_eq_char_def)
  also have \<open>\<dots> \<longleftrightarrow> ?Q\<close>
    by (simp add: of_nat_of_char integer_of_char_def)
  finally show ?thesis .
qed

lemma less_char_code [code]:
  \<open>c < d \<longleftrightarrow> integer_of_char c < integer_of_char d\<close> (is \<open>?P \<longleftrightarrow> ?Q\<close>)
proof -
  have \<open>?P \<longleftrightarrow> of_nat (of_char c) < (of_nat (of_char d) :: integer)\<close>
    by (simp add: less_char_def)
  also have \<open>\<dots> \<longleftrightarrow> ?Q\<close>
    by (simp add: of_nat_of_char integer_of_char_def)
  finally show ?thesis .
qed

lemma absdef_simps:
  \<open>horner_sum of_bool 2 [] = (0 :: integer)\<close>
  \<open>horner_sum of_bool 2 (False # bs) = (0 :: integer) \<longleftrightarrow> horner_sum of_bool 2 bs = (0 :: integer)\<close>
  \<open>horner_sum of_bool 2 (True # bs) = (1 :: integer) \<longleftrightarrow> horner_sum of_bool 2 bs = (0 :: integer)\<close>
  \<open>horner_sum of_bool 2 (False # bs) = (numeral (Num.Bit0 n) :: integer) \<longleftrightarrow> horner_sum of_bool 2 bs = (numeral n :: integer)\<close>
  \<open>horner_sum of_bool 2 (True # bs) = (numeral (Num.Bit1 n) :: integer) \<longleftrightarrow> horner_sum of_bool 2 bs = (numeral n :: integer)\<close>
  by auto (auto simp only: numeral_Bit0 [of n] numeral_Bit1 [of n] mult_2 [symmetric] add.commute [of _ 1] add.left_cancel mult_cancel_left)

local_setup \<open>
  let
    val simps = @{thms absdef_simps integer_of_char_def of_char_Char numeral_One}
    fun prove_eqn lthy n lhs def_eqn =
      let
        val eqn = (HOLogic.mk_Trueprop o HOLogic.mk_eq)
          (\<^term>\<open>integer_of_char\<close> $ lhs, HOLogic.mk_number \<^typ>\<open>integer\<close> n)
      in
        Goal.prove_future lthy [] [] eqn (fn {context = ctxt, ...} =>
          unfold_tac ctxt (def_eqn :: simps))
      end
    fun define n =
      let
        val s = "Char_" ^ String_Syntax.hex n;
        val b = Binding.name s;
        val b_def = Thm.def_binding b;
        val b_code = Binding.name (s ^ "_code");
      in
        Local_Theory.define ((b, Mixfix.NoSyn),
          ((Binding.empty, []), HOLogic.mk_char n))
        #-> (fn (lhs, (_, raw_def_eqn)) =>
          Local_Theory.note ((b_def, @{attributes [code_abbrev]}), [HOLogic.mk_obj_eq raw_def_eqn])
          #-> (fn (_, [def_eqn]) => `(fn lthy => prove_eqn lthy n lhs def_eqn))
          #-> (fn raw_code_eqn => Local_Theory.note ((b_code, []), [raw_code_eqn]))
          #-> (fn (_, [code_eqn]) => Code.declare_abstract_eqn code_eqn))
      end
  in
    fold define (0 upto 255)
  end
\<close>

code_identifier
  code_module Code_Abstract_Char \<rightharpoonup>
    (SML) Str and (OCaml) Str and (Haskell) Str and (Scala) Str

end
