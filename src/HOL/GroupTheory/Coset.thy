(*  Title:      HOL/GroupTheory/Coset
    ID:         $Id$
    Author:     Florian Kammueller, with new proofs by L C Paulson
    Copyright   1998-2001  University of Cambridge

Theory of cosets, using locales
*)

Coset =  Group + Exponent +

constdefs
  r_coset    :: "['a grouptype,'a set, 'a] => 'a set"    
   "r_coset G H a == (% x. (bin_op G) x a) ` H"

  l_coset    :: "['a grouptype, 'a, 'a set] => 'a set"
   "l_coset G a H == (% x. (bin_op G) a x) ` H"

  set_r_cos  :: "['a grouptype,'a set] => ('a set)set"
   "set_r_cos G H == r_coset G H ` (carrier G)"

  set_prod  :: "['a grouptype,'a set,'a set] => 'a set"
   "set_prod G H1 H2 == (%x. (bin_op G) (fst x)(snd x)) ` (H1 \\<times> H2)"
  set_inv   :: "['a grouptype,'a set] => 'a set"
   "set_inv G H == (%x. (inverse G) x) ` H"

  normal     :: "('a grouptype * 'a set)set"     
   "normal == \\<Sigma>G \\<in> Group. {H. H <<= G & 
                            (\\<forall>x \\<in> carrier G. r_coset G H x = l_coset G x H)}"


syntax
  "@NS"  :: "['a set, 'a grouptype] => bool" ("_ <| _"   [60,61]60)

syntax (xsymbols)
  "@NS"  :: "['a set, 'a grouptype] => bool" ("_ \\<lhd> _"   [60,61]60)

translations
  "N <| G" == "(G,N) \\<in> normal"

locale coset = group +
  fixes 
    rcos      :: "['a set, 'a] => 'a set"   ("_ #> _" [60,61]60)
    lcos      :: "['a, 'a set] => 'a set"   ("_ <# _" [60,61]60)
    setprod   :: "['a set, 'a set] => 'a set"         ("_ <#> _" [60,61]60)
    setinv    :: "'a set => 'a set"                   ("I (_)"      [90]91)
    setrcos   :: "'a set => 'a set set"               ("{*_*}"  [90]91)
  assumes

  defines
    rcos_def "H #> x == r_coset G H x"
    lcos_def "x <# H == l_coset G x H"
    setprod_def "H1 <#> H2 == set_prod G H1 H2"
    setinv_def  "I(H)  == set_inv G H"
    setrcos_def "{*H*} == set_r_cos G H"

end


