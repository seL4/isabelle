(*  Title:      HOL/GroupTheory/Sylow
    ID:         $Id$
    Author:     Florian Kammueller, with new proofs by L C Paulson
    Copyright   1998-2001  University of Cambridge

Sylow's theorem using locales (combinatorial argument in Exponent.thy)

See Florian Kamm\"uller and L. C. Paulson,
    A Formal Proof of Sylow's theorem:
	An Experiment in Abstract Algebra with Isabelle HOL
    J. Automated Reasoning 23 (1999), 235-264
*)

Sylow =  Coset +

locale sylow = coset +
  fixes 
    p        :: "nat"
    a        :: "nat"
    m        :: "nat"
    calM      :: "'a set set"
    RelM      ::  "('a set * 'a set)set"
  assumes
    prime_p   "p\\<in>prime"
    order_G   "order(G) = (p^a) * m"
    finite_G  "finite (carrier G)"
  defines
    calM_def "calM == {s. s <= carrier(G) & card(s) = p^a}"
    RelM_def "RelM == {(N1,N2). (N1,N2) \\<in> calM \\<times> calM &
			        (\\<exists>g \\<in> carrier(G). N1 = (N2 #> g) )}"

locale sylow_central = sylow +
  fixes
    H :: "'a set"
    M :: "'a set set"
    M1 :: "'a set"
  assumes
    M_in_quot "M \\<in> calM // RelM"
    not_dvd_M "~(p ^ (exponent p m + 1) dvd card(M))"
    M1_in_M   "M1 \\<in> M"
  defines
   H_def "H == {g. g\\<in>carrier G & M1 #> g = M1}"

end
