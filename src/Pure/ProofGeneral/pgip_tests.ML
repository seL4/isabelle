(*  Title:      Pure/ProofGeneral/pgip_tests.ML
    Author:     David Aspinall

A test suite for the PGIP abstraction code (in progress).
Run to provide some mild insurance against breakage in Isabelle here.
*)

(** pgip_types.ML **)

local
fun asseq_p toS a b =
    if a=b then ()
    else error("PGIP test: expected these two values to be equal:\n" ^
               (toS a) ^"\n and: \n" ^ (toS b))

val asseqx = asseq_p XML.string_of
val asseqs = asseq_p I
val asseqb = asseq_p (fn b=>if b then "true" else "false")

open PgipTypes;
in

val _ = asseqx (pgiptype_to_xml Pgipnull) (XML.parse "<pgipnull/>");
val _ = asseqx (pgiptype_to_xml Pgipbool) (XML.parse "<pgipbool/>");
val _ = asseqx (pgiptype_to_xml (Pgipint (NONE,NONE))) (XML.parse "<pgipint/>");
val _ = asseqx (pgiptype_to_xml (Pgipint (SOME 5,SOME 7))) (XML.parse "<pgipint min='5' max='7'/>");
val _ = asseqx (pgiptype_to_xml (Pgipint (NONE,SOME 7))) (XML.parse "<pgipint max='7'/>");
val _ = asseqx (pgiptype_to_xml (Pgipint (SOME ~5,NONE))) (XML.parse "<pgipint min='-5'/>");
val _ = asseqx (pgiptype_to_xml Pgipstring) (XML.parse "<pgipstring/>");
val _ = asseqx (pgiptype_to_xml (Pgipconst "radio1"))  (XML.parse "<pgipconst name='radio1'/>");
val _ = asseqx (pgiptype_to_xml (Pgipchoice [Pgipdtype (SOME "the best choice",Pgipbool)]))
       (XML.parse "<pgipchoice><pgipbool descr='the best choice'/></pgipchoice>");

val _ = asseqs (pgval_to_string (read_pgval Pgipbool "true")) "true";
val _ = asseqs (pgval_to_string (read_pgval Pgipbool "false")) "false";
val _ = asseqs (pgval_to_string (read_pgval (Pgipint(NONE,NONE)) "-37")) "-37";
val _ = asseqs (pgval_to_string (read_pgval Pgipnat "45")) "45";
val _ = asseqs (pgval_to_string (read_pgval Pgipstring "stringvalue")) "stringvalue";

local
    val choices = Pgipchoice [Pgipdtype (NONE,Pgipbool), Pgipdtype (NONE,Pgipnat), 
                              Pgipdtype (NONE,Pgipnull), Pgipdtype (NONE,Pgipconst "foo")]
in
val _ = asseqs (pgval_to_string (read_pgval choices "45")) "45";
val _ = asseqs (pgval_to_string (read_pgval choices "foo")) "foo";
val _ = asseqs (pgval_to_string (read_pgval choices "true")) "true";
val _ = asseqs (pgval_to_string (read_pgval choices "")) "";
val _ = (asseqs (pgval_to_string (read_pgval choices "-37")) "-37"; 
         error "pgip_tests: should fail") handle PGIP _ => ()
end

val _ = asseqx (haspref {name="provewithgusto",descr=SOME "use energetic proofs",
                 default=SOME "true", pgiptype=Pgipbool})
       (XML.parse "<haspref name='provewithgusto' descr='use energetic proofs' default='true'><pgipbool/></haspref>");
end


(** pgip_input.ML **)
local

fun e str = case XML.parse str of 
                (XML.Elem args) => args
              | _ => error("Expected to get an XML Element")

open PgipInput;
open PgipTypes;
open PgipIsabelle;

fun asseqi a b =
    if input (e a) = b then ()
    else error("PGIP test: expected two inputs to be equal, for input:\n" ^ a)

in

val _ = asseqi "<askpgip/>" (SOME (Askpgip()));
val _ = asseqi "<askpgml/>" (SOME (Askpgml()));
val _ = asseqi "<askconfig/>" (SOME (Askconfig()));
(* FIXME: new tests:
val _ = asseqi "<pgmlsymbolson/>" (SOME (Pgmlsymbolson()));
val _ = asseqi "<pgmlsymbolsoff/>" (SOME (Pgmlsymbolsoff()));
val _ = asseqi "<startquiet/>" (SOME (Startquiet()));
val _ = asseqi "<stopquiet/>" (SOME (Stopquiet()));
*)
val _ = asseqi "<askrefs thyname='foo' objtype='theory'/>" (SOME (Askrefs {url=NONE, thyname=SOME "foo",
                                                                          objtype=SOME ObjTheory,name=NONE}));
val _ = asseqi "<otherelt/>" NONE;

end

(** pgip_markup.ML **)
local
open PgipMarkup
in
val _ = ()
end


(** pgip_output.ML **)
local
open PgipOutput
in
val _ = ()
end


(** pgip_parser.ML **)
local
open PgipMarkup
open PgipParser
open PgipIsabelle

fun asseqp a b =
    if pgip_parser Position.none a = b then ()
    else error("PGIP test: expected two parses to be equal, for input:\n" ^ a)

in
val _ = 
    asseqp "theory A imports Bthy Cthy Dthy begin"
    [Opentheory
         {text = "theory A imports Bthy Cthy Dthy begin",
          thyname = SOME "A",
          parentnames = ["Bthy", "Cthy", "Dthy"]},
     Openblock {metavarid=NONE,name=NONE,objtype=SOME ObjTheoryBody}];

val _ = 
    asseqp "end" 
   [Closeblock {}, Closetheory {text = "end"}];

end
