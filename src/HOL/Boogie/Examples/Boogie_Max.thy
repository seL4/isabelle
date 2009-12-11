(*  Title:      HOL/Boogie/Examples/Boogie_Max.thy
    Author:     Sascha Boehme, TU Muenchen
*)

header {* Boogie example: get the greatest element of a list *}

theory Boogie_Max
imports Boogie
begin

text {*
We prove correct the verification condition generated from the following
Boogie code:

\begin{verbatim}
procedure max(array : [int]int, length : int)
  returns (max : int);
  requires (0 < length);
  ensures (forall i: int :: 0 <= i && i < length ==> array[i] <= max);
  ensures (exists i: int :: 0 <= i && i < length ==> array[i] == max);

implementation max(array : [int]int, length : int) returns (max : int)
{
  var p : int, k : int;
  max := array[0];
  k := 0;
  p := 1;
  while (p < length)
    invariant (forall i: int :: 0 <= i && i < p ==> array[i] <= max);
    invariant (array[k] == max);
  {
    if (array[p] > max) { max := array[p]; k := p; }
    p := p + 1;
  }
}
\end{verbatim}
*}

boogie_open "~~/src/HOL/Boogie/Examples/Boogie_Max"

boogie_vc max
  using [[z3_proofs=true]]
  using [[smt_cert="~~/src/HOL/Boogie/Examples/cert/Boogie_max"]]
  by boogie

boogie_end

end
