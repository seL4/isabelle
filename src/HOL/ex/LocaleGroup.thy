(*  Title:      HOL/ex/LocaleGroup.thy
    ID:         $Id$
    Author:     Florian Kammueller, University of Cambridge

Group theory via records and locales.
*)

LocaleGroup =   PiSets + Record +

record 'a grouptype = 
  carrier  :: "'a set"    
  bin_op   :: "['a, 'a] => 'a"
  inverse  :: "'a => 'a"
  unit     :: "'a"

constdefs
  Group :: "('a, 'more::more) grouptype_scheme set"
  "Group == {G. (bin_op G): carrier G -> carrier G -> carrier G &
	        inverse G : carrier G -> carrier G 
             & unit G : carrier G &
             (! x: carrier G. ! y: carrier G. !z: carrier G.
                       (bin_op G (inverse G x) x = unit G) 
                     & (bin_op G (unit G) x = x) 
                     & (bin_op G (bin_op G x y) z =
			bin_op G (x) (bin_op G y z)))}"

locale groups =
  fixes 
    G        ::"('a, 'more :: more) grouptype_scheme"
    e        :: "'a"
    binop    :: "'a => 'a => 'a" 	(infixr "#" 80)
	(*INV renamed from inv temporarily to avoid clash with Fun.inv*)
    INV      :: "'a => 'a"              ("i'(_')")
  assumes
    Group_G   "G: Group"
  defines
    e_def      "e == unit G"
    binop_def  "x # y == bin_op G x y"
    inv_def    "INV == inverse G"

end
