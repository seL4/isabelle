(*  Title:      HOL/Recdef.thy
    ID:         $Id$
    Author:     Konrad Slind

TFL: recursive function definitions.
*)

theory Recdef = WF_Rel + Datatype
files
  (*establish a base of common and/or helpful functions*)
  "../TFL/utils.sig"

  "../TFL/usyntax.sig"
  "../TFL/rules.sig"
  "../TFL/thry.sig"
  "../TFL/thms.sig"
  "../TFL/tfl.sig"
  "../TFL/utils.sml"

  (*supply implementations*)
  "../TFL/usyntax.sml"
  "../TFL/thms.sml"
  "../TFL/dcterm.sml"
  "../TFL/rules.sml"
  "../TFL/thry.sml"

  (*link system and specialize for Isabelle*)
  "../TFL/tfl.sml"
  "../TFL/post.sml"

  (*theory extender wrapper module*)
  "Tools/recdef_package.ML":

setup RecdefPackage.setup

end
