(*  Title:      HOLCF/IOA/meta_theory/ShortExecutions.thy
    ID:         $Id$
    Author:     Olaf M"uller
    Copyright   1997  TU Muenchen

Some properties about (Cut ex), defined as follows:

For every execution ex there is another shorter execution (Cut ex) 
that has the same trace as ex, but its schedule ends with an external action.

*) 


ShortExecutions = Traces + 

consts 

  LastActExtex      ::"('a,'s)ioa => ('a,'s) pairs  => bool"
  LastActExtsch     ::"('a,'s)ioa => 'a Seq         => bool"

  Cut               ::"('a => bool) => 'a Seq    => 'a Seq"
 
  oraclebuild       ::"('a => bool) => 'a Seq -> 'a Seq -> 'a Seq"

defs

LastActExtsch_def
  "LastActExtsch A sch == (Cut (%x.x: ext A) sch = sch)"

LastActExtex_def
  "LastActExtex A ex == LastActExtsch A (filter_act`ex)"

Cut_def
  "Cut P s == oraclebuild P`s`(Filter P`s)"

oraclebuild_def
  "oraclebuild P == (fix`(LAM h s t. case t of 
       nil => nil
    | x##xs => 
      (case x of 
        Undef => UU
      | Def y => (Takewhile (%x.~P x)`s)
                  @@ (y>>(h`(TL`(Dropwhile (%x.~ P x)`s))`xs))
      )
    ))"




rules

execThruCut
  "is_execution_fragment A (s,ex) ==> is_execution_fragment A (s,Cut P ex)"

LastActExtsmall1
  "LastActExtsch A sch ==> LastActExtsch A (TL`(Dropwhile P`sch))"

LastActExtsmall2
  "[| Finite sch1; LastActExtsch A (sch1 @@ sch2) |] ==> LastActExtsch A sch2"

end

