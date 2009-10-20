(*  Title:      Pure/ProofGeneral/pgip_parser.ML
    Author:     David Aspinall and Makarius

Parsing theory sources without execution (via keyword classification).
*)

signature PGIP_PARSER =
sig
  val pgip_parser: Position.T -> string -> PgipMarkup.pgipdocument
end

structure PgipParser: PGIP_PARSER =
struct

structure K = OuterKeyword;
structure D = PgipMarkup;
structure I = PgipIsabelle;


fun badcmd text = [D.Badcmd {text = text}];

fun thy_begin text =
  (case try (Thy_Header.read Position.none) (Source.of_string text) of
    NONE => D.Opentheory {thyname = NONE, parentnames = [], text = text}
  | SOME (name, imports, _) =>
       D.Opentheory {thyname = SOME name, parentnames = imports, text = text})
  :: [D.Openblock {metavarid = NONE, name = NONE, objtype = SOME I.ObjTheoryBody}];

fun thy_heading text =
  [D.Closeblock {},
   D.Doccomment {text = text},
   D.Openblock {metavarid = NONE, name = NONE, objtype = SOME I.ObjTheoryBody}];

fun thy_decl text =
  [D.Theoryitem {name = NONE, objtype = SOME I.ObjTheoryDecl, text = text}];

fun goal text =
  [D.Opengoal {thmname = NONE, text = text},
   D.Openblock {metavarid = NONE, name = NONE, objtype = SOME I.ObjProofBody}];

fun prf_block text =
  [D.Closeblock {},
   D.Proofstep {text = text},
   D.Openblock {metavarid = NONE, name = NONE, objtype = SOME I.ObjProofBody}];

fun prf_open text =
 [D.Openblock {metavarid = NONE, name = NONE, objtype = SOME I.ObjProofBody},
  D.Proofstep {text = text}];

fun proofstep text = [D.Proofstep {text = text}];
fun closegoal text = [D.Closegoal {text = text}, D.Closeblock {}];


fun command k f = Symtab.update_new (OuterKeyword.kind_of k, f);

val command_keywords = Symtab.empty
  |> command K.control          badcmd
  |> command K.diag             (fn text => [D.Spuriouscmd {text = text}])
  |> command K.thy_begin        thy_begin
  |> command K.thy_switch       badcmd
  |> command K.thy_end          (fn text => [D.Closeblock {}, D.Closetheory {text = text}])
  |> command K.thy_heading      thy_heading
  |> command K.thy_decl         thy_decl
  |> command K.thy_script       thy_decl
  |> command K.thy_goal         goal
  |> command K.qed              closegoal
  |> command K.qed_block        closegoal
  |> command K.qed_global       (fn text => [D.Giveupgoal {text = text}])
  |> command K.prf_heading      (fn text => [D.Doccomment {text = text}])
  |> command K.prf_goal         goal
  |> command K.prf_block        prf_block
  |> command K.prf_open         prf_open
  |> command K.prf_close        (fn text => [D.Proofstep {text = text}, D.Closeblock {}])
  |> command K.prf_chain        proofstep
  |> command K.prf_decl         proofstep
  |> command K.prf_asm          proofstep
  |> command K.prf_asm_goal     goal
  |> command K.prf_script       proofstep;

val _ = gen_subset (op =) (OuterKeyword.kinds, Symtab.keys command_keywords)
  orelse sys_error "Incomplete coverage of command keywords";

fun parse_command "sorry" text = [D.Postponegoal {text = text}, D.Closeblock {}]
  | parse_command name text =
      (case OuterKeyword.command_keyword name of
        NONE => [D.Unparseable {text = text}]
      | SOME k =>
          (case Symtab.lookup command_keywords (OuterKeyword.kind_of k) of
            NONE => [D.Unparseable {text = text}]
          | SOME f => f text));

fun parse_span span =
  let
    val kind = ThySyntax.span_kind span;
    val toks = ThySyntax.span_content span;
    val text = implode (map (PrintMode.setmp [] ThySyntax.present_token) toks);
  in
    (case kind of
      ThySyntax.Command name => parse_command name text
    | ThySyntax.Ignored => [D.Whitespace {text = text}]
    | ThySyntax.Malformed => [D.Unparseable {text = text}])
  end;


fun pgip_parser pos str =
  maps parse_span (ThySyntax.parse_spans (OuterKeyword.get_lexicons ()) pos str);

end;
