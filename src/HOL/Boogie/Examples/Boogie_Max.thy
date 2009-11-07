(*  Title:      HOL/Boogie/Examples/Boogie_Dijkstra.thy
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

text {*
Approach 1: Discharge the verification condition fully automatically by SMT:
*}
boogie_vc max
  unfolding labels
  using [[smt_cert="~~/src/HOL/Boogie/Examples/cert/Boogie_max"]]
  using [[z3_proofs=true]]
  by (smt boogie)

text {*
Approach 2: Split the verification condition, try to solve the splinters by
a selection of automated proof tools, and show the remaining subgoals by an
explicit proof. This approach is most useful in an interactive debug-and-fix
mode. 
*}
boogie_vc max
proof (split_vc (verbose) try: fast simp)
  print_cases
  case L_14_5c
  thus ?case by (metis abs_of_nonneg zabs_less_one_iff zle_linear)
next
  case L_14_5b
  thus ?case by (metis less_le_not_le linorder_not_le xt1(10) zle_linear
    zless_add1_eq)
next
  case L_14_5a
  thus ?case by (metis less_le_not_le zle_add1_eq_le zless_linear)
qed

boogie_end

end
