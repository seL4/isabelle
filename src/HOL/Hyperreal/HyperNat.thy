(*  Title       : HyperNat.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Description : Explicit construction of hypernaturals using 
                  ultrafilters
*) 

HyperNat = Star + 

constdefs
    hypnatrel :: "((nat=>nat)*(nat=>nat)) set"
    "hypnatrel == {p. EX X Y. p = ((X::nat=>nat),Y) & 
                       {n::nat. X(n) = Y(n)} : FreeUltrafilterNat}"

typedef hypnat = "UNIV//hypnatrel"              (Equiv.quotient_def)

instance
   hypnat  :: {ord,zero,plus,times,minus}

consts
  "1hn"       :: hypnat               ("1hn")  
  "whn"       :: hypnat               ("whn")  

constdefs

  (* embedding the naturals in the hypernaturals *)
  hypnat_of_nat   :: nat => hypnat
  "hypnat_of_nat m  == Abs_hypnat(hypnatrel``{%n::nat. m})"

  (* hypernaturals as members of the hyperreals; the set is defined as  *)
  (* the nonstandard extension of set of naturals embedded in the reals *)
  HNat         :: "hypreal set"
  "HNat == *s* {n. EX no::nat. n = real no}"

  (* the set of infinite hypernatural numbers *)
  HNatInfinite :: "hypnat set"
  "HNatInfinite == {n. n ~: Nats}"

  (* explicit embedding of the hypernaturals in the hyperreals *)    
  hypreal_of_hypnat :: hypnat => hypreal
  "hypreal_of_hypnat N  == Abs_hypreal(UN X: Rep_hypnat(N). 
                                       hyprel``{%n::nat. real (X n)})"
  
defs

  (** the overloaded constant "Nats" **)
  
  (* set of naturals embedded in the hyperreals*)
  SNat_def             "Nats == {n. EX N. n = hypreal_of_nat N}"  

  (* set of naturals embedded in the hypernaturals*)
  SHNat_def            "Nats == {n. EX N. n = hypnat_of_nat N}"  

  (** hypernatural arithmetic **)
  
  hypnat_zero_def      "0 == Abs_hypnat(hypnatrel``{%n::nat. 0})"
  hypnat_one_def       "1hn == Abs_hypnat(hypnatrel``{%n::nat. 1})"

  (* omega is in fact an infinite hypernatural number = [<1,2,3,...>] *)
  hypnat_omega_def     "whn == Abs_hypnat(hypnatrel``{%n::nat. n})"
 
  hypnat_add_def  
  "P + Q == Abs_hypnat(UN X:Rep_hypnat(P). UN Y:Rep_hypnat(Q).
                hypnatrel``{%n::nat. X n + Y n})"

  hypnat_mult_def  
  "P * Q == Abs_hypnat(UN X:Rep_hypnat(P). UN Y:Rep_hypnat(Q).
                hypnatrel``{%n::nat. X n * Y n})"

  hypnat_minus_def  
  "P - Q == Abs_hypnat(UN X:Rep_hypnat(P). UN Y:Rep_hypnat(Q).
                hypnatrel``{%n::nat. X n - Y n})"

  hypnat_less_def
  "P < (Q::hypnat) == EX X Y. X: Rep_hypnat(P) & 
                               Y: Rep_hypnat(Q) & 
                               {n::nat. X n < Y n} : FreeUltrafilterNat"
  hypnat_le_def
  "P <= (Q::hypnat) == ~(Q < P)" 

end



