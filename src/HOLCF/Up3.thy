(*  Title:      HOLCF/Up3.thy
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen


Class instance of  ('a)u for class pcpo

*)

Up3 = Up2 +

instance u :: (pcpo)pcpo      (least_up,cpo_up)

constdefs  
        up  :: "'a -> ('a)u"
       "up  == (LAM x. Iup(x))"
        fup :: "('a->'c)-> ('a)u -> 'c"
       "fup == (LAM f p. Ifup(f)(p))"

translations
"case l of up$x => t1" == "fup$(LAM x. t1)$l"

end



