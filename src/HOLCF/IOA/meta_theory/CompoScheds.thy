(*  Title:      HOLCF/IOA/meta_theory/CompoScheds.thy
    ID:         $Id$
    Author:     Olaf Müller

Compositionality on Schedule level.
*) 

CompoScheds = CompoExecs + 



consts

 mkex     ::"('a,'s)ioa => ('a,'t)ioa => 'a Seq =>
              ('a,'s)execution => ('a,'t)execution =>('a,'s*'t)execution" 
 mkex2    ::"('a,'s)ioa => ('a,'t)ioa => 'a Seq -> 
              ('a,'s)pairs -> ('a,'t)pairs -> 
              ('s => 't => ('a,'s*'t)pairs)"
 par_scheds ::"['a schedule_module,'a schedule_module] => 'a schedule_module"



defs

mkex_def  
  "mkex A B sch exA exB == 
       ((fst exA,fst exB),
        (mkex2 A B$sch$(snd exA)$(snd exB)) (fst exA) (fst exB))"

mkex2_def
  "mkex2 A B == (fix$(LAM h sch exA exB. (%s t. case sch of 
       nil => nil
    | x##xs => 
      (case x of 
        UU => UU
      | Def y => 
         (if y:act A then 
             (if y:act B then 
                (case HD$exA of
                   UU => UU
                 | Def a => (case HD$exB of
                              UU => UU
                            | Def b => 
                   (y,(snd a,snd b))>>
                     (h$xs$(TL$exA)$(TL$exB)) (snd a) (snd b)))
              else
                (case HD$exA of
                   UU => UU
                 | Def a => 
                   (y,(snd a,t))>>(h$xs$(TL$exA)$exB) (snd a) t)
              )
          else 
             (if y:act B then 
                (case HD$exB of
                   UU => UU
                 | Def b => 
                   (y,(s,snd b))>>(h$xs$exA$(TL$exB)) s (snd b))
             else
               UU
             )
         )
       ))))"

par_scheds_def
  "par_scheds SchedsA SchedsB == 
       let schA = fst SchedsA; sigA = snd SchedsA; 
           schB = fst SchedsB; sigB = snd SchedsB       
       in
       (    {sch. Filter (%a. a:actions sigA)$sch : schA}
        Int {sch. Filter (%a. a:actions sigB)$sch : schB}
        Int {sch. Forall (%x. x:(actions sigA Un actions sigB)) sch},
        asig_comp sigA sigB)"

end
