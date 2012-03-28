(*  Title:      HOL/Boogie/Examples/Boogie_Max.thy
    Author:     Sascha Boehme, TU Muenchen
*)

header {* Boogie example: get the greatest element of a list *}

theory Boogie_Max
imports Boogie
uses ("Boogie_Max.b2i")
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

boogie_open "Boogie_Max.b2i"

declare [[smt_certificates = "Boogie_Max.certs"]]
declare [[smt_read_only_certificates = true]]
declare [[smt_oracle = false]]

boogie_vc max
  by boogie

boogie_end

end
