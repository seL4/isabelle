(*  Title:      HOL/Modelcheck/CTL.thy
    ID:         $Id$
    Author:     Olaf Mueller, Jan Philipps, Robert Sandner
    Copyright   1997  TU Muenchen
*)

CTL = MuCalculus + 


types
  'a trans  = "('a * 'a) set"


consts

  CEX   ::"['a trans,'a pred, 'a]=>bool" 
  EG    ::"['a trans,'a pred]=> 'a pred" 
  EU    ::"['a trans,'a pred,'a pred]=> 'a pred" 
  EF    ::"['a trans,'a pred]=> 'a pred" 
  AX    ::"['a trans,'a pred]=> 'a pred" 
  AF    ::"['a trans,'a pred]=> 'a pred" 
  AG    ::"['a trans,'a pred]=> 'a pred" 
  AU    ::"['a trans,'a pred,'a pred]=> 'a pred" 
FairEG  ::"['a trans,'a pred,'a pred]=> 'a pred" 



defs
 
CEX_def  "CEX N f x  == (? y. (f y & (x,y):N))"
EG_def   "EG N f     == nu (% Q. % x.(f x & CEX N Q x))"
EU_def   "EU N f g   == mu (% Q. % x.(g x | (g x & CEX N Q x)))"
EF_def   "EF N f     == EU N (%x. True) f"

AX_def   "AX N f x   == ~ CEX N (%x. ~ f x) x"
AF_def   "AF N f x   == ~ EG N (%x. ~ f x) x"
AG_def   "AG N f x   == ~ EF N (%x. ~ f x) x"
AU_def   "AU N f g x == ~ EU N (%x. ~ g x) (%x. (~ f x) & (~ g x)) x & AF N g x"

FairEG_def "FairEG N f fc == nu (% Q. %x. (f x & 
             (mu (% P. CEX N (%y. f y & ((fc y & Q y) | P y)))) x))" 
 
end
