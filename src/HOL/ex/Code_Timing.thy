(*  Title: HOL/ex/Code_Timing.thy
    Author: Florian Haftmann, TU Muenchen, 2016
*)

section \<open>Examples for code generation timing measures\<close>

theory Code_Timing
imports "HOL-Number_Theory.Eratosthenes"
begin

declare [[code_timing]]

definition primes_upto :: "nat \<Rightarrow> int list"
where
  "primes_upto = map int \<circ> Eratosthenes.primes_upto"

definition "required_symbols _ = (primes_upto, 0 :: nat, Suc, 1 :: nat,
  numeral :: num \<Rightarrow> nat, Num.One, Num.Bit0, Num.Bit1,
  Code_Evaluation.TERM_OF_EQUAL :: int list itself)"

ML \<open>
local
  val ctxt = @{context};
  val consts = [@{const_name required_symbols}];
in
  val simp = Code_Simp.static_conv
    { ctxt = ctxt, consts = consts, simpset = NONE };
  val nbe = Nbe.static_conv
    { ctxt = ctxt, consts = consts };
end;
\<close>

ML_val \<open>
  simp @{context} @{cterm "primes_upto 100"}
\<close>

ML_val \<open>
  simp @{context} @{cterm "primes_upto 200"}
\<close>

ML_val \<open>
  nbe @{context} @{cterm "primes_upto 200"}
\<close>

ML_val \<open>
  nbe @{context} @{cterm "primes_upto 400"}
\<close>

ML_val \<open>
  nbe @{context} @{cterm "primes_upto 600"}
\<close>

end
