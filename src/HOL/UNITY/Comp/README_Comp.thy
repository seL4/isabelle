theory README_Comp imports Main
begin

section \<open>UNITY: Examples Involving Program Composition\<close>

text \<open>
  The directory presents verification examples involving program composition.
  They are mostly taken from the works of Chandy, Charpentier and Chandy.

  \<^item> examples of \<^emph>\<open>universal properties\<close>: the counter (\<^file>\<open>Counter.thy\<close>) and
    priority system (\<^file>\<open>Priority.thy\<close>)
  \<^item> the allocation system (\<^file>\<open>Alloc.thy\<close>)
  \<^item> client implementation (\<^file>\<open>Client.thy\<close>)
  \<^item> allocator implementation (\<^file>\<open>AllocImpl.thy\<close>)
  \<^item> the handshake protocol (\<^file>\<open>Handshake.thy\<close>)
  \<^item> the timer array (demonstrates arrays of processes) (\<^file>\<open>TimerArray.thy\<close>)

  Safety proofs (invariants) are often proved automatically. Progress proofs
  involving ENSURES can sometimes be proved automatically. The level of
  automation appears to be about the same as in HOL-UNITY by Flemming Andersen
  et al.
\<close>

end
