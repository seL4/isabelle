(*  Title:      HOL/MicroJava/J/SystemClasses.thy
    ID:         $Id$
    Author:     Gerwin Klein
    Copyright   2002 Technische Universitaet Muenchen
*)

header {* \isaheader{System Classes} *}

theory SystemClasses = Decl:

text {*
  This theory provides definitions for the @{text Object} class,
  and the system exceptions.
*}

constdefs
  ObjectC :: "'c cdecl"
  "ObjectC \<equiv> (Object, (arbitrary,[],[]))"

  NullPointerC :: "'c cdecl"
  "NullPointerC \<equiv> (Xcpt NullPointer, (Object,[],[]))"

  ClassCastC :: "'c cdecl"
  "ClassCastC \<equiv> (Xcpt ClassCast, (Object,[],[]))"

  OutOfMemoryC :: "'c cdecl"
  "OutOfMemoryC \<equiv> (Xcpt OutOfMemory, (Object,[],[]))"

  SystemClasses :: "'c cdecl list"
  "SystemClasses \<equiv> [ObjectC, NullPointerC, ClassCastC, OutOfMemoryC]"

end
