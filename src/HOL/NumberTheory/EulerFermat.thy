(*  Title:	EulerFermat.thy
    ID:         $Id$
    Author:	Thomas M. Rasmussen
    Copyright	2000  University of Cambridge
*)

EulerFermat = BijectionRel + IntFact +

consts
  RsetR        :: "int => int set set"
  BnorRset     :: "int*int=>int set" 
  norRRset     :: int => int set
  noXRRset     :: [int, int] => int set
  phi          :: int => nat
  is_RRset     :: [int set, int] => bool
  RRset2norRR  :: [int set, int, int] => int

inductive "RsetR m"
intrs
  empty  "{} : RsetR m"
  insert "[| A : RsetR m; zgcd(a,m) = #1; \
\            ALL a'. a':A --> ~ zcong a a' m |] \
\        ==> insert a A : RsetR m"

recdef BnorRset "measure ((% (a,m).(nat a)) ::int*int=>nat)"
    "BnorRset (a,m) = (if #0<a then let na = BnorRset (a-#1,m) in
                         (if zgcd(a,m) = #1 then insert a na else na) 
                       else {})"

defs
  norRRset_def "norRRset m   == BnorRset (m-#1,m)"

  noXRRset_def "noXRRset m x == (%a. a*x)``(norRRset m)"

  phi_def      "phi m == card (norRRset m)"

  is_RRset_def "is_RRset A m ==  (A : (RsetR m)) & card(A) = (phi m)"

  RRset2norRR_def "RRset2norRR A m a == 
                     (if #1<m & (is_RRset A m) & a:A 
                      then @b. zcong a b m & b:(norRRset m) else #0)"

consts zcongm :: int => [int, int] => bool
defs zcongm_def "zcongm m == (%a b. zcong a b m)"

end
