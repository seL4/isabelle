(*  Title:      Tools/WWW_Find/find_theorems.ML
    Author:     Timothy Bourke, NICTA

Simple find_theorems server.
*)

local
val default_limit = 20;
val thy_names = sort string_ord (ThyInfo.get_names ());

val find_theorems_url = "find_theorems";

fun is_sorry thm =
  Thm.proof_of thm
  |> Proofterm.approximate_proof_body
  |> Proofterm.all_oracles_of
  |> exists (fn (x, _) => x = "Pure.skip_proof");

local open Xhtml in
fun find_theorems_form thy_name (query, limit, withdups) =
  let
    val query_input =
      input (id "query", {
        name = "query",
        itype = TextInput { value = query, maxlength = NONE }});

    val max_results = divele noid
      [
        label (noid, { for = "limit" }, "Max. results:"),
        input (id "limit",
          { name = "limit",
            itype = TextInput { value = SOME (Int.toString limit),
                                maxlength = NONE }})
      ];

    val theories = divele noid
      [
        label (noid, { for = "theory" }, "Search in:"),
        select (id "theory", { name = "theory", value = SOME thy_name })
               thy_names
      ];

    val with_dups = divele noid
      [
        label (noid, { for = "withdups" }, "Allow duplicates:"),
        input (id "withdups",
          { name = "withdups",
            itype = Checkbox { checked = withdups, value = SOME "true" }})
      ];

    val help = divele (class "help")
      [ a { href="/pasting_help.html", text="(pasting from proof general)" } ];
  in
    form (id "findtheorems", { method = "post", action = "/isabelle/find_theorems" })
      [tag "fieldset" []
        [tag "legend" [] [text "find_theorems"],
         (add_script (OnKeyPress, "encodequery(this)")
          o add_script (OnChange, "encodequery(this)")
          o add_script (OnMouseUp, "encodequery(this)")) query_input,
         divele (class "settings") [ max_results, theories, with_dups, help ],
         divele (class "mainbuttons")
           [ reset_button (id "reset"), submit_button (id "submit") ]
        ]
      ]
  end;

fun html_header thy_name args =
  html { lang = "en" } [
    head { title = "Find Theorems: results", stylesheet_href = "/basic.css" }
         [script (noid, { script_type="text/javascript",
                          src="/find_theorems.js" })],
    add_script (OnLoad, "encodequery(document.getElementById('query'))")
      (body noid [
          h (noid, 1, "Theory " ^ thy_name),
          find_theorems_form thy_name args,
          divele noid []
         ])
  ];

fun html_error msg = p ((class "error"), msg);

val find_theorems_table =
  table (class "findtheorems")
    [
      thead noid [tr [th (noid, "name"), th (noid, "theorem")]],
      tbody noid []
    ];

fun show_criterion (b, c) =
  let
    fun prfx s = let
        val (c, v) = if b then ("criterion", s) else ("ncriterion", "-" ^ s);
      in span (class c, v) end;

    fun prfxwith s = let
        val (c, v) =
          if b
          then ("criterion", "with " ^ s)
          else ("ncriterion", "without " ^ s);
      in span (class c, v) end;
  in
    (case c of
      Find_Theorems.Name name => prfx ("name: " ^ quote name)
    | Find_Theorems.Intro => prfx "intro"
    | Find_Theorems.IntroIff => prfx "introiff"
    | Find_Theorems.Elim => prfx "elim"
    | Find_Theorems.Dest => prfx "dest"
    | Find_Theorems.Solves => prfx "solves"
    | Find_Theorems.Simp pat => prfx ("simp: \"" ^ pat ^ "\"")
    | Find_Theorems.Pattern pat => prfx ("\"" ^ pat ^ "\""))
  end;

fun find_theorems_summary (othmslen, thmslen, query, args) =
  let
    val args =
      (case othmslen of
         NONE => args
       | SOME l => Symtab.update ("limit", Int.toString l) args)
    val qargs = HttpUtil.make_query_string args;

    val num_found_text =
      (case othmslen of
         NONE => text (Int.toString thmslen)
       | SOME l =>
           a { href = find_theorems_url ^
               (if qargs = "" then "" else "?" ^ qargs),
           text = Int.toString l })
    val found = [text "found ", num_found_text, text " theorems"] : tag list;
    val displayed =
      if is_some othmslen
      then " (" ^ Int.toString thmslen ^ " displayed)"
      else "";
    fun show_search c = tr [ td' noid [show_criterion c] ];
  in
    table (class "findtheoremsquery")
    (* [ tr [ th (noid, "searched for:") ] ]
       @ map show_search query @ *)
      [ tr [ th' noid (found @ [text (displayed ^ ":")]) ] ]
  end

fun sorry_class thm = if is_sorry thm then class "sorried" else noid;

fun html_thm ctxt (n, (thmref, thm)) =
  let
    val string_of_thm =
      Output.output o Pretty.setmp_margin_CRITICAL 100 Pretty.string_of o
        setmp_CRITICAL show_question_marks false (Display.pretty_thm ctxt);
  in
    tag' "tr" (class ("row" ^ Int.toString (n mod 2)))
      [
        tag' "td" (class "name")
          [span' (sorry_class thm)
             [raw_text (Facts.string_of_ref thmref)]
          ],
        tag' "td" (class "thm") [pre noid (string_of_thm thm)]
      ]
  end;

end;

structure P = OuterParse
      and K = OuterKeyword
      and FT = Find_Theorems;

val criterion =
  P.reserved "name" |-- P.!!! (P.$$$ ":" |-- P.xname) >> Find_Theorems.Name ||
  P.reserved "intro" >> K Find_Theorems.Intro ||
  P.reserved "elim" >> K Find_Theorems.Elim ||
  P.reserved "dest" >> K Find_Theorems.Dest ||
  P.reserved "solves" >> K Find_Theorems.Solves ||
  P.reserved "simp" |-- P.!!! (P.$$$ ":" |-- P.term) >> Find_Theorems.Simp ||
  P.term >> Find_Theorems.Pattern;

val parse_query =
  Scan.repeat (((Scan.option P.minus >> is_none) -- criterion));

fun app_index f xs = fold_index (fn x => K (f x)) xs ();

fun find_theorems (req as ScgiReq.Req {request_method, query_string, ...},
                   content, send) =
  let
    val arg_data =
      (case request_method of
         ScgiReq.Get => query_string
       | ScgiReq.Post =>
          content
          |> Byte.bytesToString
          |> HttpUtil.parse_query_string
       | ScgiReq.Head => raise Fail "Cannot handle Head requests.");

    val args = Symtab.lookup arg_data;

    val query = the_default "" (args "query");
    fun get_query () =
      query
      |> (fn s => s ^ ";")
      |> OuterSyntax.scan Position.start
      |> filter OuterLex.is_proper
      |> Scan.error parse_query
      |> fst;

    val limit =
      args "limit"
      |> Option.mapPartial Int.fromString
      |> the_default default_limit;
    val thy_name =
      args "theory"
      |> the_default "Main";
    val with_dups = is_some (args "with_dups");

    fun do_find () =
      let
        val ctxt = ProofContext.init (theory thy_name);
        val query = get_query ();
        val (othmslen, thms) = apsnd rev
          (Find_Theorems.find_theorems ctxt NONE (SOME limit) with_dups query);
        val thmslen = length thms;
        fun thm_row args = Xhtml.write send (html_thm ctxt args);
      in
        Xhtml.write send
          (find_theorems_summary (othmslen, thmslen, query, arg_data));
        if null thms then ()
        else (Xhtml.write_open send find_theorems_table;
              HTML_Unicode.print_mode (app_index thm_row) thms;
              Xhtml.write_close send find_theorems_table)
      end;

    val header = (html_header thy_name (args "query", limit, with_dups));
  in
    send Xhtml.doctype_xhtml1_0_strict;
    Xhtml.write_open send header;
    if query = "" then ()
    else
      do_find ()
        handle
          ERROR msg => Xhtml.write send (html_error msg)
        | e => Xhtml.write send (html_error ("Server error: " ^ exnMessage e));
    Xhtml.write_close send header
  end;
in
val () = show_question_marks := false;
val () = ScgiServer.register (find_theorems_url, SOME Mime.html, find_theorems);
end;

