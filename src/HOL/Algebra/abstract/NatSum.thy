(*
    Sums with naturals as index domain
    $Id$
    Author: Clemens Ballarin, started 12 December 1996
*)

NatSum = Ring +

consts
  SUM		:: [nat, nat => 'a] => 'a::ringS

defs
  SUM_def	"SUM n f == nat_rec <0> (%m sum. f m + sum) (Suc n)"

end
