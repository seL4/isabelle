(*  Title:      HOL/ex/Recdefs.thy
    ID:         $Id$
    Author:     Konrad Slind and Lawrence C Paulson
    Copyright   1996  University of Cambridge

Examples of recdef definitions.  Most, but not all, are handled automatically.
*)

Recdefs = Main +

consts fact :: "nat => nat"
recdef fact "less_than"
    "fact x = (if (x = 0) then 1 else x * fact (x - 1))"

consts Fact :: "nat => nat"
recdef Fact "less_than"
    "Fact 0 = 1"
    "Fact (Suc x) = (Fact x * Suc x)"

consts map2 :: "('a => 'b => 'c) * 'a list * 'b list => 'c list"
recdef map2 "measure(%(f,l1,l2).size l1)"
    "map2(f, [], [])  = []"
    "map2(f, h#t, []) = []"
    "map2(f, h1#t1, h2#t2) = f h1 h2 # map2 (f, t1, t2)"

consts finiteRchain :: "(['a,'a] => bool) * 'a list => bool"
recdef finiteRchain "measure (%(R,l).size l)"
    "finiteRchain(R,  []) = True"
    "finiteRchain(R, [x]) = True"
    "finiteRchain(R, x#y#rst) = (R x y & finiteRchain(R, y#rst))"

(*Not handled automatically: too complicated.*)
consts variant :: "nat * nat list => nat"
recdef variant "measure(%(n::nat, ns). size(filter(%y. n <= y) ns))"
    "variant(x, L) = (if (x mem L) then variant(Suc x, L) else x)"

consts gcd :: "nat * nat => nat"
recdef gcd "measure (%(x,y).x+y)"
    "gcd (0,y)          = y"
    "gcd (Suc x, 0)     = Suc x"
    "gcd (Suc x, Suc y) = (if (y <= x) then gcd(x - y, Suc y)  
                                       else gcd(Suc x, y - x))"

(*Not handled automatically.  In fact, g is the zero constant function.*)
consts g   :: "nat => nat"
recdef g "less_than"
    "g 0 = 0"
    "g(Suc x) = g(g x)"

consts Div :: "nat * nat => nat * nat"
recdef Div "measure fst"
    "Div(0,x)      = (0,0)"
    "Div(Suc x, y) =      
         (let (q,r) = Div(x,y)
          in                      
          if (y <= Suc r) then (Suc q,0) else (q, Suc r))"

(*Not handled automatically.  Should be the predecessor function, but there
  is an unnecessary "looping" recursive call in k(1) *)
consts k   :: "nat => nat"
recdef k "less_than"
    "k 0 = 0"
    "k (Suc n) = (let x = k 1  
                  in if (0=1) then k (Suc 1) else n)"

consts part :: "('a=>bool) * 'a list * 'a list * 'a list => 'a list * 'a list"
recdef part "measure (%(P,l,l1,l2).size l)"
    "part(P, [], l1,l2) = (l1,l2)"
    "part(P, h#rst, l1,l2) =  
        (if P h then part(P,rst, h#l1,  l2)  
                else part(P,rst,  l1,  h#l2))"

consts fqsort :: "(['a,'a] => bool) * 'a list => 'a list"
recdef fqsort "measure (size o snd)"
    "fqsort(ord,[]) = []"
    "fqsort(ord, x#rst) =    
     (let (less,more) = part((%y. ord y x), rst, ([],[]))
      in  
      fqsort(ord,less)@[x]@fqsort(ord,more))"

(* silly example which demonstrates the occasional need for additional
   congruence rules (here: map_cong from List). If the congruence rule is
   removed, an unprovable termination condition is generated!
   Termination not proved automatically; see the ML file.
   TFL requires (%x.mapf x) instead of mapf.
*)
consts mapf :: nat => nat list
recdef mapf "measure(%m. m)"
congs map_cong
"mapf 0 = []"
"mapf (Suc n) = concat(map (%x. mapf x) (replicate n n))"

end
