(*  Title:      HOL/ex/Hex_Bin_Examples.thy
    Author:     Gerwin Klein, NICTA
*)

section {* Examples for hexadecimal and binary numerals *}

theory Hex_Bin_Examples imports Main 
begin


text "Hex and bin numerals can be used like normal decimal numerals in input"
lemma "0xFF = 255" by (rule refl)
lemma "0xF = 0b1111" by (rule refl)

text {* 
  Just like decimal numeral they are polymorphic, for arithmetic 
  they need to be constrained
*}
lemma "0x0A + 0x10 = (0x1A :: nat)" by simp

text "The number of leading zeros is irrelevant"
lemma "0b00010000 = 0x10" by (rule refl) 

text "Unary minus works as for decimal numerals"
lemma "- 0x0A = - 10" by (rule refl)

text {*
  Hex and bin numerals are printed as decimal: @{term "0b10"}
*}
term "0b10"
term "0x0A"

text {* 
  The numerals 0 and 1 are syntactically different from the 
  constants 0 and 1. For the usual numeric types, their values 
  are the same, though.
*}
lemma "0x01 = 1" oops 
lemma "0x00 = 0" oops 

lemma "0x01 = (1::nat)" by simp
lemma "0b0000 = (0::int)" by simp


end

