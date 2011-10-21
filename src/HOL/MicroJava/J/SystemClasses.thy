(*  Title:      HOL/MicroJava/J/SystemClasses.thy
    Author:     Gerwin Klein
    Copyright   2002 Technische Universitaet Muenchen
*)

header {* \isaheader{System Classes} *}

theory SystemClasses imports Decl begin

text {*
  This theory provides definitions for the @{text Object} class,
  and the system exceptions.
*}

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
