(*  Title:      HOL/MicroJava/BV/Typing_Framework.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   2000 TUM
*)

header "Typing and Dataflow Analysis Framework"

theory Typing_Framework = Listn:

text {* 
  The relationship between dataflow analysis and a welltyped-insruction predicate. 
*}

constdefs
 bounded :: "(nat => nat list) => nat => bool"
"bounded succs n == !p<n. !q:set(succs p). q<n"

 stable :: "'s ord =>
           (nat => 's => 's)
           => (nat => nat list) => 's list => nat => bool"
"stable r step succs ss p == !q:set(succs p). step p (ss!p) <=_r ss!q"

 stables :: "'s ord => (nat => 's => 's)
            => (nat => nat list) => 's list => bool"
"stables r step succs ss == !p<size ss. stable r step succs ss p"

 is_bcv :: "'s ord => 's => (nat => 's => 's) => (nat => nat list)
           => nat => 's set => ('s list => 's list) => bool"
"is_bcv r T step succs n A bcv == !ss : list n A.
   (!p<n. (bcv ss)!p ~= T) =
   (? ts: list n A. ss <=[r] ts & welltyping r T step succs ts)"

 welltyping ::
"'s ord => 's => (nat => 's => 's) => (nat => nat list) => 's list => bool"
"welltyping r T step succs ts ==
 !p<size(ts). ts!p ~= T & stable r step succs ts p"

end
