(*  Title:      HOL/GroupTheory/Bij
    ID:         $Id$
    Author:     Florian Kammueller, with new proofs by L C Paulson
    Copyright   1998-2001  University of Cambridge

Bijections of a set and the group of bijections
	Sigma version with locales
*)

Bij = Group +

constdefs
  Bij :: "'a set => (('a => 'a)set)" 
    "Bij S == {f. f \\<in> S \\<rightarrow> S & f`S = S & inj_on f S}"

constdefs 
BijGroup ::  "'a set => (('a => 'a) grouptype)"
"BijGroup S == (| carrier = Bij S, 
                  bin_op  = %g: Bij S. %f: Bij S. compose S g f,
                  inverse = %f: Bij S. %x: S. (Inv S f) x, 
                  unit    = %x: S. x |)"

locale bij = 
  fixes 
    S :: "'a set"
    B :: "('a => 'a)set"
    comp :: "[('a => 'a),('a => 'a)]=>('a => 'a)" (infixr "o''" 80)
    inv'   :: "('a => 'a)=>('a => 'a)"              
    e'   :: "('a => 'a)"
  defines
    B_def    "B == Bij S"
    o'_def   "g o' f == compose S g f"
    inv'_def   "inv' f == Inv S f"
    e'_def   "e'  == (%x: S. x)"

locale bijgroup = bij +
  fixes 
    BG :: "('a => 'a) grouptype"
  defines
    BG_def "BG == BijGroup S"
end

