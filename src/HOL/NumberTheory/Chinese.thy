(*  Title:	Chinese.thy
    ID:         $Id$
    Author:	Thomas M. Rasmussen
    Copyright	2000  University of Cambridge
*)

Chinese = IntPrimes +

consts
  funprod     :: (nat => int) => nat => nat => int
  funsum      :: (nat => int) => nat => nat => int

primrec
  "funprod f i 0        = f i"
  "funprod f i (Suc n)  = (f (Suc (i+n)))*(funprod f i n)" 

primrec
  "funsum f i 0         = f i"
  "funsum f i (Suc n)   = (f (Suc (i+n)))+(funsum f i n)" 


consts
  m_cond      :: [nat,nat => int] => bool
  km_cond     :: [nat,nat => int,nat => int] => bool
  lincong_sol :: [nat,nat => int,nat => int,nat => int,int] => bool

  mhf         :: (nat => int) => nat => nat => int
  xilin_sol   :: [nat,nat,nat => int,nat => int,nat => int] => int
  x_sol       :: [nat,nat => int,nat => int,nat => int] => int  

defs
  m_cond_def   "m_cond n mf == 
                   (ALL i. i<=n --> #0 < mf i) & 
                   (ALL i j. i<=n & j<=n & i ~= j --> zgcd(mf i,mf j) = #1)"

  km_cond_def  "km_cond n kf mf == (ALL i. i<=n --> zgcd(kf i,mf i) = #1)"

  lincong_sol_def "lincong_sol n kf bf mf x == 
                   (ALL i. i<=n --> zcong ((kf i)*x) (bf i) (mf i))"

  mhf_def  "mhf mf n i == (if i=0 then (funprod mf 1 (n-1)) 
                           else (if i=n then (funprod mf 0 (n-1))
                           else ((funprod mf 0 (i-1)) * 
                                 (funprod mf (i+1) (n-1-i)))))"

  xilin_sol_def "xilin_sol i n kf bf mf ==
                  (if 0<n & i<=n & m_cond n mf & km_cond n kf mf then
                    (@ x. #0<=x & x<(mf i) & 
                          zcong ((kf i)*(mhf mf n i)*x) (bf i) (mf i))
                    else #0)"

  x_sol_def "x_sol n kf bf mf ==
              (funsum (%i. (xilin_sol i n kf bf mf)*(mhf mf n i)) 0 n)"

end
