(*  Title:      HOL/MicroJava/JVM/Store.thy
    ID:         $Id$
    Author:     Cornelia Pusch
    Copyright   1999 Technische Universitaet Muenchen

The store.

The JVM builds on many notions already defined in Java.
Conform provides notions for the type safety proof of the Bytecode Verifier.
*)

Store = Conform +  

constdefs
 newref :: "('a \\<leadsto> 'b) \\<Rightarrow> 'a"
 "newref s \\<equiv> \\<epsilon>v. s v = None"

end
