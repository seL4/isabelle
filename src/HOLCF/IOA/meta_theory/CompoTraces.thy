(*  Title:      HOLCF/IOA/meta_theory/CompoTraces.thy
    ID:         $Id$
    Author:     Olaf M"uller
    Copyright   1996  TU Muenchen

Compositionality on Trace level.
*) 

CompoTraces = CompoScheds + ShortExecutions +
 

consts  

 mksch     ::"('a,'s)ioa => ('a,'t)ioa => 'a Seq -> 'a Seq -> 'a Seq -> 'a Seq" 


defs

mksch_def
  "mksch A B == (fix`(LAM h tr schA schB. case tr of 
       nil => nil
    | x##xs => 
      (case x of 
        Undef => UU
      | Def y => 
         (if y:act A then 
             (if y:act B then 
                   ((Takewhile (%a.a:int A)`schA)
                      @@ (Takewhile (%a.a:int B)`schB)
                           @@ (y>>(h`xs
                                    `(TL`(Dropwhile (%a.a:int A)`schA))
                                    `(TL`(Dropwhile (%a.a:int B)`schB))
                    )))
              else
                 ((Takewhile (%a.a:int A)`schA)
                  @@ (y>>(h`xs
                           `(TL`(Dropwhile (%a.a:int A)`schA))
                           `schB)))
              )
          else 
             (if y:act B then 
                 ((Takewhile (%a.a:int B)`schB)
                     @@ (y>>(h`xs
                              `schA
                              `(TL`(Dropwhile (%a.a:int B)`schB))
                              )))
             else
               UU
             )
         )
       )))"


rules


finiteR_mksch
  "Finite (mksch A B`tr`x`y) --> Finite tr"



end


