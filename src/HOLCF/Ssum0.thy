(*  Title:      HOLCF/Ssum0.thy
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993  Technische Universitaet Muenchen

Strict sum with typedef
*)

Ssum0 = Cfun3 +

constdefs
  Sinl_Rep      :: ['a,'a,'b,bool]=>bool
 "Sinl_Rep == (%a.%x y p. (a~=UU --> x=a & p))"
  Sinr_Rep      :: ['b,'a,'b,bool]=>bool
 "Sinr_Rep == (%b.%x y p.(b~=UU --> y=b & ~p))"

typedef (Ssum)  ('a, 'b) "++" (infixr 10) = 
	"{f.(? a.f=Sinl_Rep(a))|(? b.f=Sinr_Rep(b))}"

syntax (symbols)
  "++"		:: [type, type] => type	("(_ \\<oplus>/ _)" [21, 20] 20)

consts
  Isinl         :: "'a => ('a ++ 'b)"
  Isinr         :: "'b => ('a ++ 'b)"
  Iwhen         :: "('a->'c)=>('b->'c)=>('a ++ 'b)=> 'c"

defs   (*defining the abstract constants*)
  Isinl_def     "Isinl(a) == Abs_Ssum(Sinl_Rep(a))"
  Isinr_def     "Isinr(b) == Abs_Ssum(Sinr_Rep(b))"

  Iwhen_def     "Iwhen(f)(g)(s) == @z.
                                    (s=Isinl(UU) --> z=UU)
                        &(!a. a~=UU & s=Isinl(a) --> z=f`a)  
                        &(!b. b~=UU & s=Isinr(b) --> z=g`b)"  

end

