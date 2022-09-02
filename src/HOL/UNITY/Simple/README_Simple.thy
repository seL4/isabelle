theory README_Simple imports Main
begin

section \<open>UNITY: Examples Involving Single Programs\<close>

text \<open>
  The directory presents verification examples that do not involve program
  composition. They are mostly taken from Misra's 1994 papers on ``New
  UNITY'':

    \<^item> common meeting time (\<^file>\<open>Common.thy\<close>)
    \<^item> the token ring (\<^file>\<open>Token.thy\<close>)
    \<^item> the communication network (\<^file>\<open>Network.thy\<close>)
    \<^item> the lift controller (a standard benchmark) (\<^file>\<open>Lift.thy\<close>)
    \<^item> a mutual exclusion algorithm (\<^file>\<open>Mutex.thy\<close>)
    \<^item> \<open>n\<close>-process deadlock (\<^file>\<open>Deadlock.thy\<close>)
    \<^item> unordered channel (\<^file>\<open>Channel.thy\<close>)
    \<^item> reachability in directed graphs (section 6.4 of the book)
      (\<^file>\<open>Reach.thy\<close> and \<^file>\<open>Reachability.thy\<close>>
\<close>

end
