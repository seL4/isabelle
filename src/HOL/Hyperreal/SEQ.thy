(*  Title       : SEQ.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Description : Convergence of sequences and series
*) 

SEQ = NatStar + HyperPow + 

constdefs

  (* Standard definition of convergence of sequence *)           
  LIMSEQ :: [nat=>real,real] => bool    ("((_)/ ----> (_))" [60, 60] 60)
  "X ----> L == (ALL r. Numeral0 < r --> (EX no. ALL n. no <= n --> abs (X n + -L) < r))"
  
  (* Nonstandard definition of convergence of sequence *)
  NSLIMSEQ :: [nat=>real,real] => bool    ("((_)/ ----NS> (_))" [60, 60] 60)
  "X ----NS> L == (ALL N: HNatInfinite. (*fNat* X) N @= hypreal_of_real L)"

  (* define value of limit using choice operator*)
  lim :: (nat => real) => real
  "lim X == (@L. (X ----> L))"

  nslim :: (nat => real) => real
  "nslim X == (@L. (X ----NS> L))"

  (* Standard definition of convergence *)
  convergent :: (nat => real) => bool
  "convergent X == (EX L. (X ----> L))"

  (* Nonstandard definition of convergence *)
  NSconvergent :: (nat => real) => bool
  "NSconvergent X == (EX L. (X ----NS> L))"

  (* Standard definition for bounded sequence *)
  Bseq :: (nat => real) => bool
  "Bseq X == (EX K. (Numeral0 < K & (ALL n. abs(X n) <= K)))"
 
  (* Nonstandard definition for bounded sequence *)
  NSBseq :: (nat=>real) => bool
  "NSBseq X == (ALL N: HNatInfinite. (*fNat* X) N : HFinite)" 

  (* Definition for monotonicity *)
  monoseq :: (nat=>real)=>bool
  "monoseq X == ((ALL (m::nat) n. m <= n --> X m <= X n) |
                 (ALL m n. m <= n --> X n <= X m))"   

  (* Definition of subsequence *)
  subseq :: (nat => nat) => bool
  "subseq f == (ALL m n. m < n --> (f m) < (f n))"

  (** Cauchy condition **)

  (* Standard definition *)
  Cauchy :: (nat => real) => bool
  "Cauchy X == (ALL e. (Numeral0 < e -->
                       (EX M. (ALL m n. M <= m & M <= n 
                             --> abs((X m) + -(X n)) < e))))"

  NSCauchy :: (nat => real) => bool
  "NSCauchy X == (ALL M: HNatInfinite. ALL N: HNatInfinite.
                      (*fNat* X) M @= (*fNat* X) N)"
end

