(*  Title       : HOL/Real/Hyperreal/HyperDef.thy
    ID          : $Id$
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Description : Construction of hyperreals using ultrafilters
*) 

HyperDef = Filter + Real +

consts 
 
    FreeUltrafilterNat   :: nat set set    ("\\<U>")

defs

    FreeUltrafilterNat_def
    "FreeUltrafilterNat    ==   (@U. U : FreeUltrafilter (UNIV:: nat set))"


constdefs
    hyprel :: "((nat=>real)*(nat=>real)) set"
    "hyprel == {p. ? X Y. p = ((X::nat=>real),Y) & 
                   {n::nat. X(n) = Y(n)}: FreeUltrafilterNat}"

typedef hypreal = "UNIV//hyprel"   (Equiv.quotient_def)

instance
   hypreal  :: {ord, zero, plus, times, minus, inverse}

consts 

  "1hr"       :: hypreal               ("1hr")  
  "whr"       :: hypreal               ("whr")  
  "ehr"       :: hypreal               ("ehr")  


defs

  hypreal_zero_def
  "0 == Abs_hypreal(hyprel```{%n::nat. (#0::real)})"

  hypreal_one_def
  "1hr == Abs_hypreal(hyprel```{%n::nat. (#1::real)})"

  (* an infinite number = [<1,2,3,...>] *)
  omega_def
  "whr == Abs_hypreal(hyprel```{%n::nat. real_of_nat (Suc n)})"
    
  (* an infinitesimal number = [<1,1/2,1/3,...>] *)
  epsilon_def
  "ehr == Abs_hypreal(hyprel```{%n::nat. inverse (real_of_nat (Suc n))})"

  hypreal_minus_def
  "- P == Abs_hypreal(UN X: Rep_hypreal(P). hyprel```{%n::nat. - (X n)})"

  hypreal_diff_def 
  "x - y == x + -(y::hypreal)"

  hypreal_inverse_def
  "inverse P == Abs_hypreal(UN X: Rep_hypreal(P). 
                    hyprel```{%n. if X n = #0 then #0 else inverse (X n)})"

  hypreal_divide_def
  "P / Q::hypreal == P * inverse Q"
  
constdefs

  hypreal_of_real  :: real => hypreal                 
  "hypreal_of_real r         == Abs_hypreal(hyprel```{%n::nat. r})"

defs 

  hypreal_add_def  
  "P + Q == Abs_hypreal(UN X:Rep_hypreal(P). UN Y:Rep_hypreal(Q).
                hyprel```{%n::nat. X n + Y n})"

  hypreal_mult_def  
  "P * Q == Abs_hypreal(UN X:Rep_hypreal(P). UN Y:Rep_hypreal(Q).
                hyprel```{%n::nat. X n * Y n})"

  hypreal_less_def
  "P < (Q::hypreal) == EX X Y. X: Rep_hypreal(P) & 
                               Y: Rep_hypreal(Q) & 
                               {n::nat. X n < Y n} : FreeUltrafilterNat"
  hypreal_le_def
  "P <= (Q::hypreal) == ~(Q < P)" 

end
 

