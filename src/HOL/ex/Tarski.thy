(*  Title:      HOL/ex/Tarski
    ID:         $Id$
    Author:     Florian Kammueller, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge

Minimal version of lattice theory plus the full theorem of Tarski:
   The fixedpoints of a complete lattice themselves form a complete lattice.

Illustrates first-class theories, using the Sigma representation of structures
*)

Tarski = Main + 


record 'a potype = 
  pset  :: "'a set"
  order :: "('a * 'a) set"

syntax
  "@pset" :: "'a potype => 'a set"             ("_ .<A>"  [90] 90)
  "@order" :: "'a potype => ('a *'a)set"       ("_ .<r>"  [90] 90) 

translations
  "po.<A>" == "pset po"
  "po.<r>" == "order po"

constdefs
  monotone :: "['a => 'a, 'a set, ('a *'a)set] => bool"
    "monotone f A r == ! x: A. ! y: A. (x, y): r --> ((f x), (f y)) : r"

  least :: "['a => bool, 'a potype] => 'a"
   "least P po == @ x. x: po.<A> & P x &
                       (! y: po.<A>. P y --> (x,y): po.<r>)"

  greatest :: "['a => bool, 'a potype] => 'a"
   "greatest P po == @ x. x: po.<A> & P x &
                          (! y: po.<A>. P y --> (y,x): po.<r>)"

  lub  :: "['a set, 'a potype] => 'a"
   "lub S po == least (%x. ! y: S. (y,x): po.<r>) po"

  glb  :: "['a set, 'a potype] => 'a"
   "glb S po == greatest (%x. ! y: S. (x,y): po.<r>) po"

  islub :: "['a set, 'a potype, 'a] => bool"
   "islub S po == %L. (L: po.<A> & (! y: S. (y,L): po.<r>) &
                      (! z:po.<A>. (! y: S. (y,z): po.<r>) --> (L,z): po.<r>))"

  isglb :: "['a set, 'a potype, 'a] => bool"
   "isglb S po == %G. (G: po.<A> & (! y: S. (G,y): po.<r>) &
                     (! z: po.<A>. (! y: S. (z,y): po.<r>) --> (z,G): po.<r>))"

  fix    :: "[('a => 'a), 'a set] => 'a set"
   "fix f A  == {x. x: A & f x = x}"

  interval :: "[('a*'a) set,'a, 'a ] => 'a set"
   "interval r a b == {x. (a,x): r & (x,b): r}"


constdefs
  Bot :: "'a potype => 'a"
   "Bot po == least (%x. True) po"

  Top :: "'a potype => 'a"
   "Top po == greatest (%x. True) po"

  PartialOrder :: "('a potype) set"
   "PartialOrder == {P. refl (P.<A>) (P.<r>) & antisym (P.<r>) &
		        trans (P.<r>)}"

  CompleteLattice :: "('a potype) set"
   "CompleteLattice == {cl. cl: PartialOrder & 
			(! S. S <= cl.<A> --> (? L. islub S cl L)) &
			(! S. S <= cl.<A> --> (? G. isglb S cl G))}"

  CLF :: "('a potype * ('a => 'a)) set"
   "CLF == SIGMA cl: CompleteLattice.
             {f. f: cl.<A> funcset cl.<A> & monotone f (cl.<A>) (cl.<r>)}"
  
  induced :: "['a set, ('a * 'a) set] => ('a *'a)set"
   "induced A r == {(a,b). a : A & b: A & (a,b): r}"




constdefs
  sublattice :: "('a potype * 'a set)set"
   "sublattice == 
      SIGMA cl: CompleteLattice.
          {S. S <= cl.<A> &
	   (| pset = S, order = induced S (cl.<r>) |): CompleteLattice }"

syntax
  "@SL"  :: "['a set, 'a potype] => bool" ("_ <<= _" [51,50]50)

translations
  "S <<= cl" == "S : sublattice ^^ {cl}"

constdefs
  dual :: "'a potype => 'a potype"
   "dual po == (| pset = po.<A>, order = converse (po.<r>) |)"

locale PO = 
fixes 
  cl :: "'a potype"
  A  :: "'a set"
  r  :: "('a * 'a) set"
assumes 
  cl_po  "cl : PartialOrder"
defines
  A_def "A == cl.<A>"
  r_def "r == cl.<r>"

locale CL = PO +
fixes 
assumes 
  cl_co  "cl : CompleteLattice"

locale CLF = CL +
fixes
  f :: "'a => 'a"
  P :: "'a set"
assumes 
  f_cl "f : CLF ^^{cl}"
defines
  P_def "P == fix f A"


locale Tarski = CLF + 
fixes
  Y :: "'a set"
  intY1 :: "'a set"
  v     :: "'a"
assumes
  Y_ss "Y <= P"
defines
  intY1_def "intY1 == interval r (lub Y cl) (Top cl)"
  v_def "v == glb {x. ((lam x: intY1. f x) x, x): induced intY1 r & x: intY1}
	          (| pset=intY1, order=induced intY1 r|)"

end
