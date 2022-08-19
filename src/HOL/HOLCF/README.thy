theory README imports Main
begin

section \<open>HOLCF: A higher-order version of LCF based on Isabelle/HOL\<close>

text \<open>
  HOLCF is the definitional extension of Church's Higher-Order Logic with
  Scott's Logic for Computable Functions that has been implemented in the
  theorem prover Isabelle. This results in a flexible setup for reasoning
  about functional programs. HOLCF supports standard domain theory (in
  particular fixpoint reasoning and recursive domain equations) but also
  coinductive arguments about lazy datatypes.

  The most recent description of HOLCF is found here:

    \<^item> \<^emph>\<open>HOLCF '11: A Definitional Domain Theory for Verifying Functional
    Programs\<close> \<^url>\<open>http://web.cecs.pdx.edu/~brianh/phdthesis.html\<close>, Brian
    Huffman. Ph.D. thesis, Portland State University. 2012.

  Descriptions of earlier versions can also be found online:

    \<^item> \<^emph>\<open>HOLCF = HOL+LCF\<close> \<^url>\<open>https://www21.in.tum.de/~nipkow/pubs/jfp99.html\<close>

  A detailed description (in German) of the entire development can be found
  in:

    \<^item> \<^emph>\<open>HOLCF: eine konservative Erweiterung von HOL um LCF\<close>
    \<^url>\<open>http://www4.informatik.tu-muenchen.de/publ/papers/Diss_Regensbu.pdf\<close>,
    Franz Regensburger. Dissertation Technische Universität München. 1994.

  A short survey is available in:

    \<^item> \<^emph>\<open>HOLCF: Higher Order Logic of Computable Functions\<close>
    \<^url>\<open>http://www4.informatik.tu-muenchen.de/publ/papers/Regensburger_HOLT1995.pdf\<close>
\<close>

end
