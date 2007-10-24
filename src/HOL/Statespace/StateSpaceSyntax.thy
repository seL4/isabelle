(*  Title:      StateSpaceSyntax.thy
    ID:         $Id$
    Author:     Norbert Schirmer, TU Muenchen
*)

header {* Syntax for State Space Lookup and Update \label{sec:StateSpaceSyntax}*}
theory StateSpaceSyntax
imports StateSpaceLocale

begin

text {* The state space syntax is kept in an extra theory so that you
can choose if you want to use it or not.  *}

syntax 
 "_statespace_lookup" :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'c" ("_\<cdot>_" [60,60] 60)
 "_statespace_update" :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'c \<Rightarrow> ('a \<Rightarrow> 'b)"
 "_statespace_updates" :: "('a \<Rightarrow> 'b) \<Rightarrow> updbinds \<Rightarrow> ('a \<Rightarrow> 'b)" ("_<_>" [900,0] 900)

translations
  "_statespace_updates f (_updbinds b bs)"  == 
     "_statespace_updates (_statespace_updates f b) bs"
  "s<x:=y>"                     == "_statespace_update s x y"


parse_translation (advanced)
{*
[("_statespace_lookup",StateSpace.lookup_tr),
 ("_get",StateSpace.lookup_tr),
 ("_statespace_update",StateSpace.update_tr)] 
*}


print_translation (advanced)
{*
[("lookup",StateSpace.lookup_tr'),
 ("StateFun.lookup",StateSpace.lookup_tr'),
 ("update",StateSpace.update_tr'),
 ("StateFun.update",StateSpace.update_tr')] 
*}

end