(*  Title       : Integration.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 2000  University of Edinburgh
    Description : Theory of integration (cf. Harrison's HOL development)
*)

Integration = MacLaurin + 


constdefs

  
(* ------------------------------------------------------------------------ *)
(* Partitions and tagged partitions etc.                                    *)
(* ------------------------------------------------------------------------ *)

  partition :: "[(real*real),nat => real] => bool"
  "partition == %(a,b) D. ((D 0 = a) & 
                         (EX N. ((ALL n. n < N --> D(n) < D(Suc n)) &
                            (ALL n. N <= n --> (D(n) = b)))))"
  
  psize :: (nat => real) => nat
  "psize D == @N. (ALL n. n < N --> D(n) < D(Suc n)) &
                  (ALL n. N <= n --> (D(n) = D(N)))"
  
  tpart :: "[(real*real),((nat => real)*(nat =>real))] => bool"
  "tpart == %(a,b) (D,p). partition(a,b) D &
                          (ALL n. D(n) <= p(n) & p(n) <= D(Suc n))"

(* ------------------------------------------------------------------------ *)
(* Gauges and gauge-fine divisions                                          *)
(* ------------------------------------------------------------------------ *)
  
  gauge :: [real => bool, real => real] => bool
  "gauge E g == ALL x. E x --> 0 < g(x)"

  fine :: "[real => real, ((nat => real)*(nat => real))] => bool"
  "fine == % g (D,p). ALL n. n < (psize D) --> D(Suc n) - D(n) < g(p n)"

(* ------------------------------------------------------------------------ *)
(* Riemann sum                                                              *)
(* ------------------------------------------------------------------------ *)

  rsum :: "[((nat=>real)*(nat=>real)),real=>real] => real"
  "rsum == %(D,p) f. sumr 0 (psize(D)) (%n. f(p n) * (D(Suc n) - D(n)))"

(* ------------------------------------------------------------------------ *)
(* Gauge integrability (definite)                                           *)
(* ------------------------------------------------------------------------ *)

   Integral :: "[(real*real),real=>real,real] => bool"
   "Integral == %(a,b) f k. ALL e. 0 < e -->
                               (EX g. gauge(%x. a <= x & x <= b) g &
                               (ALL D p. tpart(a,b) (D,p) & fine(g)(D,p) -->
                                         abs(rsum(D,p) f - k) < e))"    
end


