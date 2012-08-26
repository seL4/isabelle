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

structure D = PgipMarkup;
structure I = PgipIsabelle;


fun badcmd text = [D.Badcmd {text = text}];

fun thy_begin text =
  (case try (Thy_Header.read Position.none) text of
    NONE => D.Opentheory {thyname = NONE, parentnames = [], text = text}
  | SOME {name = (name, _), imports, ...} =>
       D.Opentheory {thyname = SOME name, parentnames = map #1 imports, text = text})
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


fun command k f = Symtab.update_new (Keyword.kind_of k, f);

val command_keywords = Symtab.empty
  |> command Keyword.control          badcmd
  |> command Keyword.diag             (fn text => [D.Spuriouscmd {text = text}])
  |> command Keyword.thy_begin        thy_begin
  |> command Keyword.thy_end          (fn text => [D.Closeblock {}, D.Closetheory {text = text}])
  |> command Keyword.thy_heading1     thy_heading
  |> command Keyword.thy_heading2     thy_heading
  |> command Keyword.thy_heading3     thy_heading
  |> command Keyword.thy_heading4     thy_heading
  |> command Keyword.thy_load         thy_decl
  |> command Keyword.thy_decl         thy_decl
  |> command Keyword.thy_script       thy_decl
  |> command Keyword.thy_goal         goal
  |> command Keyword.thy_schematic_goal goal
  |> command Keyword.qed              closegoal
  |> command Keyword.qed_block        closegoal
  |> command Keyword.qed_global       (fn text => [D.Giveupgoal {text = text}])
  |> command Keyword.prf_heading2     (fn text => [D.Doccomment {text = text}])
  |> command Keyword.prf_heading3     (fn text => [D.Doccomment {text = text}])
  |> command Keyword.prf_heading4     (fn text => [D.Doccomment {text = text}])
  |> command Keyword.prf_goal         goal
  |> command Keyword.prf_block        prf_block
  |> command Keyword.prf_open         prf_open
  |> command Keyword.prf_close        (fn text => [D.Proofstep {text = text}, D.Closeblock {}])
  |> command Keyword.prf_chain        proofstep
  |> command Keyword.prf_decl         proofstep
  |> command Keyword.prf_asm          proofstep
  |> command Keyword.prf_asm_goal     goal
  |> command Keyword.prf_script       proofstep;

val _ = subset (op =) (map Keyword.kind_of Keyword.kinds, Symtab.keys command_keywords)
  orelse raise Fail "Incomplete coverage of command keywords";

fun parse_command "sorry" text = [D.Postponegoal {text = text}, D.Closeblock {}]
  | parse_command name text =
      (case Keyword.command_keyword name of
        NONE => [D.Unparseable {text = text}]
      | SOME k =>
          (case Symtab.lookup command_keywords (Keyword.kind_of k) of
            NONE => [D.Unparseable {text = text}]
          | SOME f => f text));

fun parse_span span =
  let
    val kind = Thy_Syntax.span_kind span;
    val toks = Thy_Syntax.span_content span;
    val text = implode (map (Print_Mode.setmp [] Thy_Syntax.present_token) toks);
  in
    (case kind of
      Thy_Syntax.Command (name, _) => parse_command name text
    | Thy_Syntax.Ignored => [D.Whitespace {text = text}]
    | Thy_Syntax.Malformed => [D.Unparseable {text = text}])
  end;


fun pgip_parser pos str =
  Thy_Syntax.parse_tokens (Keyword.get_lexicons ()) pos str
  |> Thy_Syntax.parse_spans
  |> maps parse_span;

end;
