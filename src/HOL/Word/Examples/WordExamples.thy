(* 
  Author: Gerwin Klein, NICTA

  Examples demonstrating and testing various word operations.
*)

header "Examples of word operations"

theory WordExamples
imports "../Word"
begin

type_synonym word32 = "32 word"
type_synonym word8 = "8 word"
type_synonym byte = word8

text "modulus"

lemma "(27 :: 4 word) = -5" by simp

lemma "(27 :: 4 word) = 11" by simp

lemma "27 \<noteq> (11 :: 6 word)" by simp

text "signed"

lemma "(127 :: 6 word) = -1" by simp

text "number ring simps"

lemma 
  "27 + 11 = (38::'a::len word)"
  "27 + 11 = (6::5 word)"
  "7 * 3 = (21::'a::len word)"
  "11 - 27 = (-16::'a::len word)"
  "- -11 = (11::'a::len word)"
  "-40 + 1 = (-39::'a::len word)"
  by simp_all

lemma "word_pred 2 = 1" by simp

lemma "word_succ -3 = -2" by simp
  
lemma "23 < (27::8 word)" by simp
lemma "23 \<le> (27::8 word)" by simp
lemma "\<not> 23 < (27::2 word)" by simp
lemma "0 < (4::3 word)" by simp
lemma "1 < (4::3 word)" by simp
lemma "0 < (1::3 word)" by simp

text "ring operations"

lemma "a + 2 * b + c - b = (b + c) + (a :: 32 word)" by simp

text "casting"

lemma "uint (234567 :: 10 word) = 71" by simp
lemma "uint (-234567 :: 10 word) = 953" by simp
lemma "sint (234567 :: 10 word) = 71" by simp
lemma "sint (-234567 :: 10 word) = -71" by simp
lemma "uint (1 :: 10 word) = 1" by simp

lemma "unat (-234567 :: 10 word) = 953" by simp
lemma "unat (1 :: 10 word) = 1" by simp

lemma "ucast (0b1010 :: 4 word) = (0b10 :: 2 word)" by simp
lemma "ucast (0b1010 :: 4 word) = (0b1010 :: 10 word)" by simp
lemma "scast (0b1010 :: 4 word) = (0b111010 :: 6 word)" by simp
lemma "ucast (1 :: 4 word) = (1 :: 2 word)" by simp

text "reducing goals to nat or int and arith:"
lemma "i < x ==> i < (i + 1 :: 'a :: len word)" by unat_arith
lemma "i < x ==> i < (i + 1 :: 'a :: len word)" by uint_arith

text "bool lists"

lemma "of_bl [True, False, True, True] = (0b1011::'a::len word)" by simp

lemma "to_bl (0b110::4 word) = [False, True, True, False]" by simp

text "this is not exactly fast, but bearable"
lemma "of_bl (replicate 32 True) = (0xFFFFFFFF::32 word)" by simp

text "this works only for replicate n True"
lemma "of_bl (replicate 32 True) = (0xFFFFFFFF::32 word)"
  by (unfold mask_bl [symmetric]) (simp add: mask_def)


text "bit operations"

lemma "0b110 AND 0b101 = (0b100 :: 32 word)" by simp
lemma "0b110 OR 0b011 = (0b111 :: 8 word)" by simp
lemma "0xF0 XOR 0xFF = (0x0F :: byte)" by simp
lemma "NOT (0xF0 :: 16 word) = 0xFF0F" by simp
lemma "0 AND 5 = (0 :: byte)" by simp
lemma "1 AND 1 = (1 :: byte)" by simp
lemma "1 AND 0 = (0 :: byte)" by simp
lemma "1 AND 5 = (1 :: byte)" by simp
lemma "1 OR 6 = (7 :: byte)" by simp
lemma "1 OR 1 = (1 :: byte)" by simp
lemma "1 XOR 7 = (6 :: byte)" by simp
lemma "1 XOR 1 = (0 :: byte)" by simp
lemma "NOT 1 = (254 :: byte)" by simp
lemma "NOT 0 = (255 :: byte)" apply simp oops
(* FIXME: "NOT 0" rewrites to "max_word" instead of "-1" *)

lemma "(-1 :: 32 word) = 0xFFFFFFFF" by simp

lemma "(0b0010 :: 4 word) !! 1" by simp
lemma "\<not> (0b0010 :: 4 word) !! 0" by simp
lemma "\<not> (0b1000 :: 3 word) !! 4" by simp
lemma "\<not> (1 :: 3 word) !! 2" by simp

lemma "(0b11000 :: 10 word) !! n = (n = 4 \<or> n = 3)" 
  by (auto simp add: bin_nth_Bit0 bin_nth_Bit1)

lemma "set_bit 55 7 True = (183::'a::len0 word)" by simp
lemma "set_bit 0b0010 7 True = (0b10000010::'a::len0 word)" by simp
lemma "set_bit 0b0010 1 False = (0::'a::len0 word)" by simp
lemma "set_bit 1 3 True = (0b1001::'a::len0 word)" by simp
lemma "set_bit 1 0 False = (0::'a::len0 word)" by simp
lemma "set_bit 0 3 True = (0b1000::'a::len0 word)" by simp
lemma "set_bit 0 3 False = (0::'a::len0 word)" by simp

lemma "lsb (0b0101::'a::len word)" by simp
lemma "\<not> lsb (0b1000::'a::len word)" by simp
lemma "lsb (1::'a::len word)" by simp
lemma "\<not> lsb (0::'a::len word)" by simp

lemma "\<not> msb (0b0101::4 word)" by simp
lemma   "msb (0b1000::4 word)" by simp
lemma "\<not> msb (1::4 word)" by simp
lemma "\<not> msb (0::4 word)" by simp

lemma "word_cat (27::4 word) (27::8 word) = (2843::'a::len word)" by simp
lemma "word_cat (0b0011::4 word) (0b1111::6word) = (0b0011001111 :: 10 word)" 
  by simp

lemma "0b1011 << 2 = (0b101100::'a::len0 word)" by simp
lemma "0b1011 >> 2 = (0b10::8 word)" by simp
lemma "0b1011 >>> 2 = (0b10::8 word)" by simp
lemma "1 << 2 = (0b100::'a::len0 word)" apply simp? oops

lemma "slice 3 (0b101111::6 word) = (0b101::3 word)" by simp
lemma "slice 3 (1::6 word) = (0::3 word)" apply simp? oops

lemma "word_rotr 2 0b0110 = (0b1001::4 word)" by simp
lemma "word_rotl 1 0b1110 = (0b1101::4 word)" by simp
lemma "word_roti 2 0b1110 = (0b1011::4 word)" by simp
lemma "word_roti -2 0b0110 = (0b1001::4 word)" by simp
lemma "word_rotr 2 0 = (0::4 word)" by simp
lemma "word_rotr 2 1 = (0b0100::4 word)" apply simp? oops
lemma "word_rotl 2 1 = (0b0100::4 word)" apply simp? oops
lemma "word_roti -2 1 = (0b0100::4 word)" apply simp? oops

lemma "(x AND 0xff00) OR (x AND 0x00ff) = (x::16 word)"
proof -
  have "(x AND 0xff00) OR (x AND 0x00ff) = x AND (0xff00 OR 0x00ff)"
    by (simp only: word_ao_dist2)
  also have "0xff00 OR 0x00ff = (-1::16 word)"
    by simp
  also have "x AND -1 = x"
    by simp
  finally show ?thesis .
qed

end
