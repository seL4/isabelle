(*  Title:      HOL/GroupTheory/FactGroup
    ID:         $Id$
    Author:     Florian Kammueller, with new proofs by L C Paulson
    Copyright   1998-2001  University of Cambridge

Factorization of a group
*)

FactGroup = Coset +

constdefs
  FactGroup :: "(['a grouptype, 'a set] => ('a set) grouptype)"

   "FactGroup ==
     lam G: Group. lam H: {H. H <| G}.
      (| carrier = set_r_cos G H,
	 bin_op = (lam X: set_r_cos G H. lam Y: set_r_cos G H. set_prod G X Y),
	 inverse = (lam X: set_r_cos G H. set_inv G X), 
	 unit = H |)"

syntax
  "@Fact" :: "['a grouptype, 'a set] => ('a set) grouptype"
              ("_ Mod _" [60,61]60)

translations
  "G Mod H" == "FactGroup G H"

locale factgroup = coset +
fixes 
  F :: "('a set) grouptype"
  H :: "('a set)"
assumes
  H_normal "H <| G"
defines
  F_def "F == FactGroup G H"

end
  