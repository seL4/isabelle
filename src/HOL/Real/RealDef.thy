(*  Title       : Real/RealDef.thy
    ID          : $Id$
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Description : The reals
*) 

RealDef = PReal +

instance preal :: order (preal_le_refl,preal_le_trans,preal_le_anti_sym,
                         preal_less_le)

constdefs
  realrel   ::  "((preal * preal) * (preal * preal)) set"
  "realrel == {p. EX x1 y1 x2 y2. p = ((x1,y1),(x2,y2)) & x1+y2 = x2+y1}" 

typedef (REAL)
  real = "UNIV//realrel"  (Equiv.quotient_def)


instance
   real  :: {ord, zero, one, plus, times, minus, inverse}

consts 
   (*Overloaded constants denoting the Nat and Real subsets of enclosing
     types such as hypreal and complex*)
   Nats, Reals :: "'a set"
  
   (*overloaded constant for injecting other types into "real"*)
   real :: 'a => real


defs

  real_zero_def  
  "0 == Abs_REAL(realrel``{(preal_of_prat(prat_of_pnat 1),
			    preal_of_prat(prat_of_pnat 1))})"

  real_one_def   
  "1 == Abs_REAL(realrel``
               {(preal_of_prat(prat_of_pnat 1) + preal_of_prat(prat_of_pnat 1),
		 preal_of_prat(prat_of_pnat 1))})"

  real_minus_def
  "- R ==  Abs_REAL(UN (x,y):Rep_REAL(R). realrel``{(y,x)})"

  real_diff_def
  "R - (S::real) == R + - S"

  real_inverse_def
  "inverse (R::real) == (SOME S. (R = 0 & S = 0) | S * R = 1)"

  real_divide_def
  "R / (S::real) == R * inverse S"
  
constdefs

  (** these don't use the overloaded "real" function: users don't see them **)
  
  real_of_preal :: preal => real            
  "real_of_preal m     ==
           Abs_REAL(realrel``{(m + preal_of_prat(prat_of_pnat 1),
                               preal_of_prat(prat_of_pnat 1))})"

  real_of_posnat :: nat => real             
  "real_of_posnat n == real_of_preal(preal_of_prat(prat_of_pnat(pnat_of_nat n)))"


defs

  (*overloaded*)
  real_of_nat_def   "real n == real_of_posnat n + (- 1)"

  real_add_def  
  "P+Q == Abs_REAL(UN p1:Rep_REAL(P). UN p2:Rep_REAL(Q).
                   (%(x1,y1). (%(x2,y2). realrel``{(x1+x2, y1+y2)}) p2) p1)"
  
  real_mult_def  
  "P*Q == Abs_REAL(UN p1:Rep_REAL(P). UN p2:Rep_REAL(Q).
                   (%(x1,y1). (%(x2,y2). realrel``{(x1*x2+y1*y2,x1*y2+x2*y1)})
		   p2) p1)"

  real_less_def
  "P<Q == EX x1 y1 x2 y2. x1 + y2 < x2 + y1 & 
                            (x1,y1):Rep_REAL(P) & (x2,y2):Rep_REAL(Q)" 
  real_le_def
  "P <= (Q::real) == ~(Q < P)"

syntax (xsymbols)
  Reals     :: "'a set"                   ("\\<real>")
  Nats      :: "'a set"                   ("\\<nat>")

end
