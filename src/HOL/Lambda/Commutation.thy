(*  Title: 	HOL/Lambda/Commutation.thy
    ID:         $Id$
    Author: 	Tobias Nipkow
    Copyright   1995  TU Muenchen

Abstract commutation and confluence notions.
*)

Commutation = Trancl +

consts
  reflcl  :: "('a*'a)set => ('a*'a)set"               ("(_^=)" [100] 100)
  square  :: "[('a*'a)set,('a*'a)set,('a*'a)set,('a*'a)set] => bool"
  commute :: "[('a*'a)set,('a*'a)set] => bool"
  confluent, diamond, Church_Rosser :: "('a*'a)set => bool"

defs
  square_def
 "square R S T U == !x y.(x,y):R --> (!z.(x,z):S --> (? u. (y,u):T & (z,u):U))"

  commute_def "commute R S == square R S S R"
  diamond_def "diamond R   == commute R R"

  Church_Rosser_def "Church_Rosser(R) ==   
  !x y. (x,y) : (R Un converse(R))^* --> (? z. (x,z) : R^* & (y,z) : R^*)"

translations
  "r^="   == "r Un id"
  "confluent R" == "diamond(R^*)"

end
