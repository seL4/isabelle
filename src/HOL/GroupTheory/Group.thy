(*  Title:      HOL/GroupTheory/Group
    ID:         $Id$
    Author:     Florian Kammueller, with new proofs by L C Paulson
    Copyright   1998-2001  University of Cambridge

Group theory using locales
*)

Group = Main +

  (*Giving funcset the nice arrow syntax \\<rightarrow> *)
syntax (xsymbols)
  "op funcset" :: "['a set, 'b set] => ('a => 'b) set"  (infixr "\\<rightarrow>" 60) 


record 'a semigrouptype = 
  carrier  :: "'a set"    
  bin_op   :: "['a, 'a] => 'a"


record 'a grouptype = 'a semigrouptype +
  inverse  :: "'a => 'a"
  unit     :: "'a"

syntax 
  "@carrier" :: "'a semigrouptype => 'a set"            ("_ .<cr>"  [10] 10)
  "@bin_op"  :: "'a semigrouptype => (['a, 'a] => 'a)"  ("_ .<f>"   [10] 10)
  "@inverse" :: "'a grouptype => ('a => 'a)"        ("_ .<inv>" [10] 10)
  "@unit"    :: "'a grouptype => 'a"                ("_ .<e>"   [10] 10) 

translations
  "G.<cr>"  => "carrier G"
  "G.<f>"   => "bin_op G"
  "G.<inv>" => "inverse G"
  "G.<e>"   => "unit G"

constdefs
  Semigroup :: "('a semigrouptype)set"
  "Semigroup == {G. (bin_op G): carrier G \\<rightarrow> carrier G \\<rightarrow> carrier G  &
             (! x: carrier G. ! y: carrier G. !z: carrier G.
                    (bin_op G (bin_op G x y) z = bin_op G (x) (bin_op G y z)))}"


constdefs
  Group :: "('a grouptype)set"
  "Group == {G. (bin_op G): carrier G \\<rightarrow> carrier G \\<rightarrow> carrier G & inverse G : carrier G \\<rightarrow> carrier G 
             & unit G : carrier G &
             (! x: carrier G. ! y: carrier G. !z: carrier G.
                       (bin_op G (inverse G x) x = unit G) 
                     & (bin_op G (unit G) x = x) 
                     & (bin_op G (bin_op G x y) z = bin_op G (x) (bin_op G y z)))}"

  order     :: "'a grouptype => nat"            "order(G) == card(carrier G)"
  
  AbelianGroup :: "('a grouptype) set"
  "AbelianGroup == {G. G : Group &
                       (! x:(G.<cr>). ! y:(G.<cr>). ((G.<f>) x y = (G.<f>) y x))}"
consts
  subgroup :: "('a grouptype * 'a set)set"

defs
  subgroup_def  "subgroup == SIGMA G: Group. {H. H <= carrier G & 
        ((| carrier = H, bin_op = %x: H. %y: H. (bin_op G) x y, 
            inverse = %x: H. (inverse G) x, unit = unit G |) : Group)}"

syntax
  "@SG"  :: "['a set, 'a grouptype] => bool" ("_ <<= _" [51,50]50)

translations
  "H <<= G" == "(G,H) : subgroup"

locale group = 
  fixes 
    G        ::"'a grouptype"
    e        :: "'a"
    binop    :: "'a => 'a => 'a" 	(infixr "##" 80)
    INV      :: "'a => 'a"              ("i (_)"      [90]91)
  assumes
    Group_G   "G: Group"
  defines
    e_def     "e == unit G"
    binop_def "op ## == bin_op G"
    inv_def   "INV == inverse G"
end

