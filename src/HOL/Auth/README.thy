theory README imports Main
begin

section \<open>Auth--The Inductive Approach to Verifying Security Protocols\<close>

text \<open>
  Cryptographic protocols are of major importance, especially with the growing
  use of the Internet. This directory demonstrates the ``inductive method'' of
  protocol verification, which is described in papers:
  \<^url>\<open>http://www.cl.cam.ac.uk/users/lcp/papers/protocols.html\<close>. The operational
  semantics of protocol participants is defined inductively.

  This directory contains proofs concerning:

    \<^item> three versions of the Otway-Rees protocol

    \<^item> the Needham-Schroeder shared-key protocol

    \<^item> the Needham-Schroeder public-key protocol (original and with Lowe's
      modification)

    \<^item> two versions of Kerberos: the simplified form published in the BAN paper
    and also the full protocol (Kerberos IV)

    \<^item> three versions of the Yahalom protocol, including a bad one that
      illustrates the purpose of the Oops rule

    \<^item> a novel recursive authentication protocol

    \<^item> the Internet protocol TLS

    \<^item> The certified e-mail protocol of Abadi et al.

  Frederic Blanqui has contributed a theory of guardedness, which is
  demonstrated by proofs of some roving agent protocols.
\<close>

end
