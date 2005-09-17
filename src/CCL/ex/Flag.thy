(*  Title:      CCL/ex/Flag.thy
    ID:         $Id$
    Author:     Martin Coen, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge
*)

header {* Dutch national flag program -- except that the point of Dijkstra's example was to use
  arrays and this uses lists. *}

theory Flag
imports List
begin

consts
  Colour             :: "i set"
  red                :: "i"
  white              :: "i"
  blue               :: "i"
  ccase              :: "[i,i,i,i]=>i"
  flag               :: "i"

axioms

  Colour_def:  "Colour == Unit + Unit + Unit"
  red_def:        "red == inl(one)"
  white_def:    "white == inr(inl(one))"
  blue_def:     "blue == inr(inr(one))"

  ccase_def:   "ccase(c,r,w,b) == when(c,%x. r,%wb. when(wb,%x. w,%x. b))"

  flag_def:    "flag == lam l. letrec
      flagx l be lcase(l,<[],<[],[]>>,
                       %h t. split(flagx(t),%lr p. split(p,%lw lb.
                            ccase(h, <red$lr,<lw,lb>>,
                                     <lr,<white$lw,lb>>,
                                     <lr,<lw,blue$lb>>))))
      in flagx(l)"

  Flag_def:
     "Flag(l,x) == ALL lr:List(Colour).ALL lw:List(Colour).ALL lb:List(Colour).
                    x = <lr,<lw,lb>> -->
                  (ALL c:Colour.(c mem lr = true --> c=red) &
                                (c mem lw = true --> c=white) &
                                (c mem lb = true --> c=blue)) &
                  Perm(l,lr @ lw @ lb)"

ML {* use_legacy_bindings (the_context ()) *}

end
