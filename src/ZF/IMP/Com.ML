(*  Title: 	ZF/IMP/Com.ML
    ID:         $Id$
    Author: 	Heiko Loetzbeyer & Robert Sandner, TUM
    Copyright   1994 TUM
*)

structure Com = Datatype_Fun
 (
  val thy = Bexp.thy;
  val thy_name = "Com";
  val rec_specs = 
      [
       (
        "com", "univ(aexp Un bexp)",
	  [
           (["skip"],		"i", NoSyn),
	   ([":="],	"[i,i] => i", Infixl 60),
	   ([";"],	"[i,i] => i", Infixl 60),
	   (["whileC"], 	"[i,i] => i", Mixfix("while _ do _",[],60)),
	   (["ifC"],		"[i,i,i] => i",
              Mixfix("ifc _ then _ else _",[],60))
          ]
       )
      ];

  val rec_styp = "i";

  val sintrs = 
       [
	"skip : com",
	"[| x:loc; a:aexp|] ==> X(x) := a : com",
	"[| c0:com; c1:com|] ==> c0 ; c1 : com",
	"[| b:bexp; c:com|] ==> while b do c : com",
	"[| b:bexp; c0:com; c1:com|] ==> ifc b then c0 else c1 : com"
       ];
  val monos = [];
  val type_intrs = datatype_intrs@Aexp.intrs;
  val type_elims = datatype_elims
 );
