(*  Title:      HOL/Codegenerator_Test/Code_Test_GHC.thy
    Author:     Andreas Lochbihler, ETH Zurich
    Author:     Florian Haftmann, TU Muenchen
*)

theory Code_Test_GHC
imports
  "HOL-Library.Code_Test"
  Code_Lazy_Test
begin

text \<open>Test cases for \<^text>\<open>test_code\<close>\<close>

test_code "(14 + 7 * -12 :: integer) = 140 div -2" in GHC

value [GHC] "14 + 7 * -12 :: integer"

test_code \<comment> \<open>Tests for the serialisation of \<^const>\<open>gcd\<close> on \<^typ>\<open>integer\<close>\<close>
  "gcd 15 10 = (5 :: integer)"
  "gcd 15 (- 10) = (5 :: integer)"
  "gcd (- 10) 15 = (5 :: integer)"
  "gcd (- 10) (- 15) = (5 :: integer)"
  "gcd 0 (- 10) = (10 :: integer)"
  "gcd (- 10) 0 = (10 :: integer)"
  "gcd 0 0 = (0 :: integer)"
in GHC

test_code "stake 10 (cycle ''ab'') = ''ababababab''" in GHC

text \<open>Test cases for bit operations on target language numerals\<close>

unbundle bit_operations_syntax

lemma \<open>bit (473514 :: integer) 5\<close>
  by normalization

test_code \<open>bit (473514 :: integer) 5\<close> in GHC

lemma \<open>bit (- 805167 :: integer) 7\<close>
  by normalization

test_code \<open>bit (- 805167 :: integer) 7\<close> in GHC

lemma \<open>473514 AND (767063 :: integer) = 208898\<close>
  by normalization

test_code \<open>473514 AND (767063 :: integer) = 208898\<close> in GHC

lemma \<open>- 805167 AND (767063 :: integer) = 242769\<close>
  by normalization

test_code \<open>- 805167 AND (767063 :: integer) = 242769\<close> in GHC

lemma \<open>473514 AND (- 314527 :: integer) = 209184\<close>
  by normalization

test_code \<open>473514 AND (- 314527 :: integer) = 209184\<close> in GHC

lemma \<open>- 805167 AND (- 314527 :: integer) = - 839103\<close>
  by normalization

test_code \<open>- 805167 AND (- 314527 :: integer) = - 839103\<close> in GHC

lemma \<open>473514 OR (767063 :: integer) = 1031679\<close>
  by normalization

test_code \<open>473514 OR (767063 :: integer) = 1031679\<close> in GHC

lemma \<open>- 805167 OR (767063 :: integer) = - 280873\<close>
  by normalization

test_code \<open>- 805167 OR (767063 :: integer) = - 280873\<close> in GHC

lemma \<open>473514 OR (- 314527 :: integer) = - 50197\<close>
  by normalization

test_code \<open>473514 OR (- 314527 :: integer) = - 50197\<close> in GHC

lemma \<open>- 805167 OR (- 314527 :: integer) = - 280591\<close>
  by normalization

test_code \<open>- 805167 OR (- 314527 :: integer) = - 280591\<close> in GHC

lemma \<open>473514 XOR (767063 :: integer) = 822781\<close>
  by normalization

test_code \<open>473514 XOR (767063 :: integer) = 822781\<close> in GHC

lemma \<open>- 805167 XOR (767063 :: integer) = - 523642\<close>
  by normalization

test_code \<open>- 805167 XOR (767063 :: integer) = - 523642\<close> in GHC

lemma \<open>473514 XOR (- 314527 :: integer) = - 259381\<close>
  by normalization

test_code \<open>473514 XOR (- 314527 :: integer) = - 259381\<close> in GHC

lemma \<open>- 805167 XOR (- 314527 :: integer) = 558512\<close>
  by normalization

test_code \<open>- 805167 XOR (- 314527 :: integer) = 558512\<close> in GHC

lemma \<open>NOT (473513 :: integer) = - 473514\<close>
  by normalization

test_code \<open>NOT (473513 :: integer) = - 473514\<close> in GHC

lemma \<open>NOT (- 805167 :: integer) = 805166\<close>
  by normalization

test_code \<open>NOT (- 805167 :: integer) = 805166\<close> in GHC

lemma \<open>(mask 39 :: integer) = 549755813887\<close>
  by normalization

test_code \<open>(mask 39 :: integer) = 549755813887\<close> in GHC

lemma \<open>set_bit 15 (473514 :: integer) = 506282\<close>
  by normalization

test_code \<open>set_bit 15 (473514 :: integer) = 506282\<close> in GHC

lemma \<open>set_bit 11 (- 805167 :: integer) = - 803119\<close>
  by normalization

test_code \<open>set_bit 11 (- 805167 :: integer) = - 803119\<close> in GHC

lemma \<open>unset_bit 13 (473514 :: integer) = 465322\<close>
  by normalization

test_code \<open>unset_bit 13 (473514 :: integer) = 465322\<close> in GHC

lemma \<open>unset_bit 12 (- 805167 :: integer) = - 809263\<close>
  by normalization

test_code \<open>unset_bit 12 (- 805167 :: integer) = - 809263\<close> in GHC

lemma \<open>flip_bit 15 (473514 :: integer) = 506282\<close>
  by normalization

test_code \<open>flip_bit 15 (473514 :: integer) = 506282\<close> in GHC

lemma \<open>flip_bit 12 (- 805167 :: integer) = - 809263\<close>
  by normalization

test_code \<open>flip_bit 12 (- 805167 :: integer) = - 809263\<close> in GHC

lemma \<open>push_bit 12 (473514 :: integer) = 1939513344\<close>
  by normalization

test_code \<open>push_bit 12 (473514 :: integer) = 1939513344\<close> in GHC

lemma \<open>push_bit 12 (- 805167 :: integer) = - 3297964032\<close>
  by normalization

test_code \<open>push_bit 12 (- 805167 :: integer) = - 3297964032\<close> in GHC

lemma \<open>drop_bit 12 (473514 :: integer) = 115\<close>
  by normalization

test_code \<open>drop_bit 12 (473514 :: integer) = 115\<close> in GHC

lemma \<open>drop_bit 12 (- 805167 :: integer) = - 197\<close>
  by normalization

test_code \<open>drop_bit 12 (- 805167 :: integer) = - 197\<close> in GHC

lemma \<open>take_bit 12 (473514 :: integer) = 2474\<close>
  by normalization

test_code \<open>take_bit 12 (473514 :: integer) = 2474\<close> in GHC

lemma \<open>take_bit 12 (- 805167 :: integer) = 1745\<close>
  by normalization

test_code \<open>take_bit 12 (- 805167 :: integer) = 1745\<close> in GHC

lemma \<open>signed_take_bit 12 (473514 :: integer) = - 1622\<close>
  by normalization

test_code \<open>signed_take_bit 12 (473514 :: integer) = - 1622\<close> in GHC

lemma \<open>signed_take_bit 12 (- 805167 :: integer) = - 2351\<close>
  by normalization

test_code \<open>signed_take_bit 12 (- 805167 :: integer) = - 2351\<close> in GHC

end
