(*  Title: 	ZF/IMP/Bexp.ML
    ID:         $Id$
    Author: 	Heiko Loetzbeyer & Robert Sandner, TUM
    Copyright   1994 TUM
*)

structure Bexp = Datatype_Fun
 (
  val thy = Aexp.thy;
  val thy_name = "Bexp"
  val rec_specs = 
      [
       (
        "bexp", "univ(aexp Un ((nat*nat)->bool) )",
	  [
           ( ["true","false"],	"i", NoSyn),
	   ( ["noti"],		"i => i", NoSyn),
	   ( ["andi"], 	"[i,i]=>i", Infixl 60),
	   ( ["ori"], 	"[i,i]=>i", Infixl 60),
           ( ["ROp"], "[i,i,i] => i", NoSyn)
          ]
       )
      ];

  val rec_styp = "i";
  val sintrs = 
       [
        "true : bexp",
	"false : bexp",
	"[| a0 : aexp; a1 : aexp; f: (nat*nat)->bool |] ==> ROp(f,a0,a1) : bexp",
	"b : bexp ==> noti(b) : bexp",
	"[| b0 : bexp; b1 : bexp |] ==> b0 andi b1 : bexp",
	"[| b0 : bexp; b1 : bexp |] ==> b0 ori b1 : bexp"
       ];
  val monos = [];
  val type_intrs = datatype_intrs;
  val type_elims = datatype_elims;
 );
