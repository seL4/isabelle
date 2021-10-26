
(* Author: Florian Haftmann, TU Muenchen *)

section \<open>Pervasive test of code generator\<close>

theory Generate_Target_Nat
imports
  Candidates
  "HOL-Library.AList_Mapping"
  "HOL-Library.Finite_Lattice"
  "HOL-Library.Code_Target_Numeral"
begin

text \<open>
  If any of the checks fails, inspect the code generated
  by a corresponding \<open>export_code\<close> command.
\<close>

lemma take_bit_num_code [code]: \<comment> \<open>TODO: move\<close>
  \<open>take_bit_num n m = (case (n, m)
   of (0, _) \<Rightarrow> None
    | (Suc n, Num.One) \<Rightarrow> Some Num.One
    | (Suc n, Num.Bit0 m) \<Rightarrow> (case take_bit_num n m of None \<Rightarrow> None | Some q \<Rightarrow> Some (Num.Bit0 q))
    | (Suc n, Num.Bit1 m) \<Rightarrow> Some (case take_bit_num n m of None \<Rightarrow> Num.One | Some q \<Rightarrow> Num.Bit1 q))\<close>
  by (cases n; cases m) simp_all

export_code _ checking SML OCaml? Haskell? Scala

end
