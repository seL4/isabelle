(*  Title:      HOL/Boogie/Examples/Boogie_Max_Stepwise.thy
    Author:     Sascha Boehme, TU Muenchen
*)

header {* Boogie example: get the greatest element of a list *}

theory Boogie_Max_Stepwise
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

boogie_open "Boogie_Max.b2i"

boogie_status -- {* gives an overview of all verification conditions *}

boogie_status max -- {* shows the names of all unproved assertions
  of the verification condition @{text max} *}

boogie_status (full) max -- {* shows the state of all assertions
  of the verification condition @{text max} *}

boogie_status (paths) max -- {* shows the names of all unproved assertions,
  grouped by program paths, of the verification condition @{text max} *}

boogie_status (full paths) max -- {* shows the state of all assertions
  of the verification condition @{text max}, grouped by program paths,
  with already proved or irrelevant assertions written in parentheses *}


text {* Let's find out which assertions of @{text max} are hard to prove: *}

boogie_status (narrow step_timeout: 4 final_timeout: 15) max
  (simp add: labels, (fast | metis)?)
  -- {* The argument @{text step_timeout} is optional, restricting the runtime
        of each intermediate narrowing step by the given number of seconds. *}
  -- {* The argument @{text final_timeout} is optional, restricting the
        runtime of the final narrowing steps by the given number of seconds. *}
  -- {* The last argument should be a method to be applied at each narrowing
        step. Note that different methods may be composed to one method by
        a language similar to regular expressions. *}

boogie_status (scan timeout: 4) max
  (simp add: labels, (fast | metis)?)
  -- {* finds the first hard assertion wrt. to the given method *}


text {* Now, let's prove the three hard assertions of @{text max}: *}

boogie_vc max (examine: L_14_5c L_14_5b L_14_5a) 
proof boogie_cases
  case L_14_5c
  thus ?case by (metis less_le_not_le zle_add1_eq_le less_linear)
next
  case L_14_5b
  thus ?case by (metis less_le_not_le xt1(10) linorder_linear zless_add1_eq)
next
  case L_14_5a
  note max0 = `max0 = array 0`
  {
    fix i :: int
    assume "0 \<le> i \<and> i < 1"
    hence "i = 0" by simp
    with max0 have "array i \<le> max0" by simp
  }
  thus ?case by simp
qed


boogie_status max -- {* the above proved assertions are not shown anymore *}

boogie_status (full) max -- {* states the above proved assertions as proved
  and all other assertions as not proved *}

boogie_status (paths) max

boogie_status (full paths) max


text {* Now we prove the remaining assertions all at once: *}

boogie_vc max by (auto simp add: labels)


boogie_status -- {* @{text max} has been completely proved *}

boogie_end

end
