(*  Title:       NSInduct.thy
    Author:      Jacques D. Fleuriot
    Copyright:   2001  University of Edinburgh
    Description: Nonstandard characterization of induction etc.
*)

NSInduct =  Complex + 

constdefs

  starPNat :: (nat => bool) => hypnat => bool  ("*pNat* _" [80] 80)
  "*pNat* P == (%x. EX X. (X: Rep_hypnat(x) & 
                      {n. P(X n)} : FreeUltrafilterNat))" 


  starPNat2 :: (nat => nat => bool) => hypnat =>hypnat => bool  ("*pNat2* _" [80] 80)
  "*pNat2* P == (%x y. EX X. EX Y. (X: Rep_hypnat(x) & Y: Rep_hypnat(y) & 
                      {n. P(X n) (Y n)} : FreeUltrafilterNat))" 

  hSuc :: hypnat => hypnat
  "hSuc n == n + 1"
    
end