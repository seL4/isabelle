(*  Title:      HOLCF/IOA/meta_theory/CompoScheds.thy
    ID:         $Id$
    Author:     Olaf M"uller
    Copyright   1996  TU Muenchen

Compositionality on Schedule level.
*) 

CompoScheds = CompoExecs + 



consts

 mkex     ::"('a,'s)ioa => ('a,'t)ioa => 'a Seq =>
              ('a,'s)execution => ('a,'t)execution =>('a,'s*'t)execution" 
 mkex2    ::"('a,'s)ioa => ('a,'t)ioa => 'a Seq -> 
              ('a,'s)pairs -> ('a,'t)pairs -> 
              ('s => 't => ('a,'s*'t)pairs)"


defs

mkex_def  
  "mkex A B sch exA exB == 
       ((fst exA,fst exB),
        (mkex2 A B`sch`(snd exA)`(snd exB)) (fst exA) (fst exB))"

mkex2_def
  "mkex2 A B == (fix`(LAM h sch exA exB. (%s t. case sch of 
       nil => nil
    | x##xs => 
      (case x of 
        Undef => UU
      | Def y => 
         (if y:act A then 
             (if y:act B then 
                (case HD`exA of
                   Undef => UU
                 | Def a => (case HD`exB of
                              Undef => UU
                            | Def b => 
                   (y,(snd a,snd b))>>
                     (h`xs`(TL`exA)`(TL`exB)) (snd a) (snd b)))
              else
                (case HD`exA of
                   Undef => UU
                 | Def a => 
                   (y,(snd a,t))>>(h`xs`(TL`exA)`exB) (snd a) t)
              )
          else 
             (if y:act B then 
                (case HD`exB of
                   Undef => UU
                 | Def b => 
                   (y,(s,snd b))>>(h`xs`exA`(TL`exB)) s (snd b))
             else
               UU
             )
         )
       ))))"

end