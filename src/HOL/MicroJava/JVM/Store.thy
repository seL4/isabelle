(*  Title:      HOL/MicroJava/JVM/Store.thy
    ID:         $Id$
    Author:     Cornelia Pusch
    Copyright   1999 Technische Universitaet Muenchen
*)

header {* Store of the JVM *}

theory Store = Conform:

text {*
The JVM builds on many notions already defined in Java.
Conform provides notions for the type safety proof of the Bytecode Verifier.
*}


constdefs
 newref :: "('a \<leadsto> 'b) => 'a"
 "newref s == SOME v. s v = None"


lemma newref_None:
  "hp x = None ==> hp (newref hp) = None"
by (auto intro: someI2_ex simp add: newref_def)

end
