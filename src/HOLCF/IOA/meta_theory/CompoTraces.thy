(*  Title:      HOLCF/IOA/meta_theory/CompoTraces.thy
    ID:        
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

(* FIX: x:actions S is further assumption, see Asig.ML: how to fulfill this in proofs ? *)
not_ext_is_int_FIX
  "[|is_asig S|] ==> (x~:externals S) = (x: internals S)"

(* FIX: should be more general , something like subst *)
lemma12
"[| f << (g x) ; (x= (h x)) |] ==> f << g (h x)"

(* FIX: as above, should be done more intelligent *)
lemma22
"[| (f x) = y >> g ; x = h x |] ==> (f (h x)) = y >> g"

Finite_Conc
  "Finite (x @@ y) = (Finite x & Finite y)"

finiteR_mksch
  "Finite (mksch A B`tr`x`y) --> Finite tr"

finiteL_mksch
  "[| Finite tr; 
   Filter (%a. a:ext A)`x = Filter (%a. a:act A)`tr;
   Filter (%a. a:ext B)`y = Filter (%a. a:actB)`tr;
   Forall (%x. x:ext (A||B)) tr |]
   ==> Finite (mksch A B`tr`x`y)"

reduce_mksch
  "[| Finite bs; Forall (%x. x:act B & x~:act A) bs;
      Filter (%a. a:ext B)`y = Filter (%a. a:act B)`(bs @@ z) |] 
  ==> ? y1 y2.  (mksch A B`(bs @@ z)`x`y) = (y1 @@ (mksch A B`z`x`y2)) &
                Forall (%x. x:act B & x~:act A) y1 &
                Finite y1 & y = (y1 @@ y2) & 
                Filter (%a. a:ext B)`y1 = bs"

end


