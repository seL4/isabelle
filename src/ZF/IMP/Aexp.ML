(*  Title: 	ZF/IMP/Aexp.ML
    ID:         $Id$
    Author: 	Heiko Loetzbeyer & Robert Sandner, TUM
    Copyright   1994 TUM
*)

structure Aexp = Datatype_Fun
 (
  val thy = Univ.thy |> add_consts [("loc", "i", NoSyn)]
  val thy_name = "Aexp"
  val rec_specs = 
      [(
        "aexp", "univ(loc Un (nat->nat) Un ((nat*nat) -> nat) )",
          [
           (["N","X"],	"i => i", NoSyn),
           (["Op1"],    "[i,i] => i", NoSyn),
           (["Op2"],    "[i,i,i] => i", NoSyn) 
          ]
       )];

  val rec_styp = "i";
  val ext = None;

  val sintrs = 
      [
       "n:nat ==> N(n) : aexp", 
       "x:loc ==> X(x) : aexp",
       "[| f: nat -> nat; a : aexp |] ==> Op1(f,a) : aexp",
       "[| f: (nat * nat) -> nat; a0 : aexp; a1: aexp |] \
\          ==> Op2(f,a0,a1) : aexp"
      ];
  val monos = [];
  val type_intrs = datatype_intrs;
  val type_elims = datatype_elims;
 );
