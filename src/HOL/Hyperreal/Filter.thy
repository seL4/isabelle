(*  Title       : Filter.thy
    ID          : $Id$
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Description : Filters and Ultrafilters
*) 

Filter = Zorn + 

constdefs

  is_Filter       :: ['a set set,'a set] => bool
  "is_Filter F S == (F <= Pow(S) & S : F & {} ~: F &
                   (ALL u: F. ALL v: F. u Int v : F) &
                   (ALL u v. u: F & u <= v & v <= S --> v: F))" 

  Filter          :: 'a set => 'a set set set
  "Filter S == {X. is_Filter X S}"
 
  (* free filter does not contain any finite set *)

  Freefilter      :: 'a set => 'a set set set
  "Freefilter S == {X. X: Filter S & (ALL x: X. ~ finite x)}"

  Ultrafilter     :: 'a set => 'a set set set
  "Ultrafilter S == {X. X: Filter S & (ALL A: Pow(S). A: X | S - A : X)}"

  FreeUltrafilter :: 'a set => 'a set set set
  "FreeUltrafilter S == {X. X: Ultrafilter S & (ALL x: X. ~ finite x)}" 

  (* A locale makes proof of Ultrafilter Theorem more modular *)
locale UFT = 
       fixes     frechet :: "'a set => 'a set set"
                 superfrechet :: "'a set => 'a set set set"

       assumes   not_finite_UNIV "~finite (UNIV :: 'a set)"

       defines   frechet_def "frechet S == {A. finite (S - A)}"
                 superfrechet_def "superfrechet S == 
                                   {G.  G: Filter S & frechet S <= G}"
end




