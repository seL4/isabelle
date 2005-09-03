(*  Title:      HOL/IOA/NTP/Multiset.thy
    ID:         $Id$
    Author:     Tobias Nipkow & Konrad Slind
*)

header {* Axiomatic multisets *}

theory Multiset
imports Lemmas
begin

typedecl
  'a multiset

consts

  "{|}"  :: "'a multiset"                        ("{|}")
  addm   :: "['a multiset, 'a] => 'a multiset"
  delm   :: "['a multiset, 'a] => 'a multiset"
  countm :: "['a multiset, 'a => bool] => nat"
  count  :: "['a multiset, 'a] => nat"

axioms

delm_empty_def:
  "delm {|} x = {|}"

delm_nonempty_def:
  "delm (addm M x) y == (if x=y then M else addm (delm M y) x)"

countm_empty_def:
   "countm {|} P == 0"

countm_nonempty_def:
   "countm (addm M x) P == countm M P + (if P x then Suc 0 else 0)"

count_def:
   "count M x == countm M (%y. y = x)"

"induction":
   "[| P({|}); !!M x. P(M) ==> P(addm M x) |] ==> P(M)"

ML {* use_text Context.ml_output true
  ("structure Multiset = struct " ^ legacy_bindings (the_context ()) ^ " end") *}
ML {* open Multiset *}

end
