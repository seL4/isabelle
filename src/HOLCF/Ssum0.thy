(*  Title:      HOLCF/ssum0.thy
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993  Technische Universitaet Muenchen

Strict sum
*)

Ssum0 = Cfun3 +

(* new type for strict sum *)

types "++" 2        (infixr 10)

arities "++" :: (pcpo,pcpo)term 

syntax (symbols)

  "++"		:: [type, type] => type		("(_ \\<oplus>/ _)" [21, 20] 20)

consts
  Ssum          :: "(['a,'b,bool]=>bool)set"
  Sinl_Rep      :: "['a,'a,'b,bool]=>bool"
  Sinr_Rep      :: "['b,'a,'b,bool]=>bool"
  Rep_Ssum      :: "('a ++ 'b) => (['a,'b,bool]=>bool)"
  Abs_Ssum      :: "(['a,'b,bool]=>bool) => ('a ++ 'b)"
  Isinl         :: "'a => ('a ++ 'b)"
  Isinr         :: "'b => ('a ++ 'b)"
  Iwhen         :: "('a->'c)=>('b->'c)=>('a ++ 'b)=> 'c"

defs

  Sinl_Rep_def          "Sinl_Rep == (%a.%x y p.
                                (a~=UU --> x=a  & p))"

  Sinr_Rep_def          "Sinr_Rep == (%b.%x y p.
                                (b~=UU --> y=b  & ~p))"

  Ssum_def              "Ssum =={f.(? a.f=Sinl_Rep(a))|(? b.f=Sinr_Rep(b))}"

rules
  (*faking a type definition... *)
  (* "++" is isomorphic to Ssum *)

  Rep_Ssum              "Rep_Ssum(p):Ssum"              
  Rep_Ssum_inverse      "Abs_Ssum(Rep_Ssum(p)) = p"     
  Abs_Ssum_inverse      "f:Ssum ==> Rep_Ssum(Abs_Ssum(f)) = f"

defs   (*defining the abstract constants*)
  Isinl_def     "Isinl(a) == Abs_Ssum(Sinl_Rep(a))"
  Isinr_def     "Isinr(b) == Abs_Ssum(Sinr_Rep(b))"

  Iwhen_def     "Iwhen(f)(g)(s) == @z.
                                    (s=Isinl(UU) --> z=UU)
                        &(!a. a~=UU & s=Isinl(a) --> z=f`a)  
                        &(!b. b~=UU & s=Isinr(b) --> z=g`b)"  

end

