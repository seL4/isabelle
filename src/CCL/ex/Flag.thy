(*  Title:      CCL/ex/flag.thy
    ID:         $Id$
    Author:     Martin Coen, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Dutch national flag program - except that the point of Dijkstra's example was to use 
arrays and this uses lists.

*)

Flag = List + 

consts

  Colour             :: "i set"
  red, white, blue   :: "i"
  ccase              :: "[i,i,i,i]=>i"
  flag               :: "i"

rules

  Colour_def  "Colour == Unit + Unit + Unit"
  red_def        "red == inl(one)"
  white_def    "white == inr(inl(one))"
  blue_def     "blue == inr(inr(one))"

  ccase_def   "ccase(c,r,w,b) == when(c,%x.r,%wb.when(wb,%x.w,%x.b))"

  flag_def    "flag == lam l.letrec 
      flagx l be lcase(l,<[],<[],[]>>, 
                       %h t. split(flagx(t),%lr p.split(p,%lw lb. 
                            ccase(h, <red$lr,<lw,lb>>, 
                                     <lr,<white$lw,lb>>, 
                                     <lr,<lw,blue$lb>>)))) 
      in flagx(l)"    

  Flag_def
     "Flag(l,x) == ALL lr:List(Colour).ALL lw:List(Colour).ALL lb:List(Colour). 
                    x = <lr,<lw,lb>> --> 
                  (ALL c:Colour.(c mem lr = true --> c=red) & 
                                (c mem lw = true --> c=white) & 
                                (c mem lb = true --> c=blue)) & 
                  Perm(l,lr @ lw @ lb)"

end



