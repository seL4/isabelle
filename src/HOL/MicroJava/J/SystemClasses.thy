(*  Title:      HOL/MicroJava/J/SystemClasses.thy
    Author:     Gerwin Klein
    Copyright   2002 Technische Universitaet Muenchen
*)

section \<open>System Classes\<close>

theory SystemClasses imports Decl begin

text \<open>
  This theory provides definitions for the \<open>Object\<close> class,
  and the system exceptions.
\<close>

definition ObjectC :: "'c cdecl" where
  [code_unfold]: "ObjectC \<equiv> (Object, (undefined,[],[]))"

definition NullPointerC :: "'c cdecl" where
  [code_unfold]: "NullPointerC \<equiv> (Xcpt NullPointer, (Object,[],[]))"

definition ClassCastC :: "'c cdecl" where
  [code_unfold]: "ClassCastC \<equiv> (Xcpt ClassCast, (Object,[],[]))"

definition OutOfMemoryC :: "'c cdecl" where
  [code_unfold]: "OutOfMemoryC \<equiv> (Xcpt OutOfMemory, (Object,[],[]))"

definition SystemClasses :: "'c cdecl list" where
  [code_unfold]: "SystemClasses \<equiv> [ObjectC, NullPointerC, ClassCastC, OutOfMemoryC]"

end
