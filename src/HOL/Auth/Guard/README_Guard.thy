theory README_Guard imports Main
begin

section \<open>Protocol-Independent Secrecy Results\<close>

text \<open>
  \<^item> date: April 2002
  \<^item> author: Frederic Blanqui
  \<^item> email: blanqui@lri.fr

  The current development is built above the HOL (Higher-Order Logic) Isabelle
  theory and the formalization of protocols introduced by Larry Paulson. More
  details are in his paper
  \<^url>\<open>https://www.cl.cam.ac.uk/users/lcp/papers/Auth/jcs.pdf\<close>: \<^emph>\<open>The Inductive
  approach to verifying cryptographic protocols\<close> (J. Computer Security 6,
  pages 85-128, 1998).

  This directory contains a number of files:

    \<^item> \<^file>\<open>Extensions.thy\<close> contains extensions of Larry Paulson's files with
      many useful lemmas.

    \<^item> \<^file>\<open>Analz.thy\<close> contains an important theorem about the decomposition of
    analz between pparts (pairs) and kparts (messages that are not pairs).

    \<^item> \<^file>\<open>Guard.thy\<close> contains the protocol-independent secrecy theorem for
      nonces.

    \<^item> \<^file>\<open>GuardK.thy\<close> is the same for keys.

    \<^item> \<^file>\<open>Guard_Public.thy\<close> extends \<^file>\<open>Guard.thy\<close> and \<^file>\<open>GuardK.thy\<close> for
    public-key protocols.

    \<^item> \<^file>\<open>Guard_Shared.thy\<close> extends \<^file>\<open>Guard.thy\<close> and \<^file>\<open>GuardK.thy\<close> for
    symmetric-key protocols.

    \<^item> \<^file>\<open>List_Msg.thy\<close> contains definitions on lists (inside messages).

    \<^item> \<^file>\<open>P1.thy\<close> contains the definition of the protocol P1 and the proof of
      its properties (strong forward integrity, insertion resilience,
      truncation resilience, data confidentiality and non-repudiability).

    \<^item> \<^file>\<open>P2.thy\<close> is the same for the protocol P2

    \<^item> \<^file>\<open>Guard_NS_Public.thy\<close> is for Needham-Schroeder-Lowe

    \<^item> \<^file>\<open>Guard_OtwayRees.thy\<close> is for Otway-Rees

    \<^item> \<^file>\<open>Guard_Yahalom.thy\<close> is for Yahalom

    \<^item> \<^file>\<open>Proto.thy\<close> contains a more precise formalization of protocols with
      rules and a protocol-independent theorem for proving guardness from a
      preservation property. It also contains the proofs for Needham-Schroeder
      as an example.
\<close>

end
