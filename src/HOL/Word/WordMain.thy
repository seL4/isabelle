(* 
  ID:     $Id$
  Author: Gerwin Klein, NICTA

  The main interface of the word library to other theories.
*)

header {* Main Word Library *}

theory WordMain
imports WordGenLib
begin

lemmas word_no_1 [simp] = word_1_no [symmetric, unfolded BIT_simps]
lemmas word_no_0 [simp] = word_0_no [symmetric]

declare word_0_bl [simp]
declare bin_to_bl_def [simp]
declare to_bl_0 [simp]
declare of_bl_True [simp]

text "Examples"

types word32 = "32 word"
types word8 = "8 word"
types byte = word8

text {* for more see WordExamples.thy *}

end
