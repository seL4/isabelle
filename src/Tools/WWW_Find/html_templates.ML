(*  Title:      Tools/WWW_Find/html_templates.ML
    Author:     Timothy Bourke, NICTA

HTML Templates for find theorems server.
*)

signature HTML_TEMPLATES =
sig
  val find_theorems_form: string -> (string option * int * bool * string list) -> Xhtml.tag

  val header: string -> (string option * int * bool * string list) -> Xhtml.tag
  val error: string -> Xhtml.tag
  val find_theorems_table: Xhtml.tag

  val find_theorems_summary: int option * int * string Symtab.table -> Xhtml.tag
  val html_thm: Proof.context -> (int * (Facts.ref * thm)) -> Xhtml.tag
end


structure HTML_Templates: HTML_TEMPLATES =
struct

open Xhtml;

fun find_theorems_form thy_name (query, limit, withdups, all_thy_names) =
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
            itype = TextInput { value = SOME (string_of_int limit),
                                maxlength = NONE }})
      ];

    val theories = divele noid
      [
        label (noid, { for = "theory" }, "Search in:"),
        select (id "theory", { name = "theory", value = SOME thy_name })
               all_thy_names
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

fun header thy_name args =
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

fun error msg = p ((class "error"), msg);

val find_theorems_table =
  table (class "findtheorems")
    [
      thead noid [tr [th (noid, "name"), th (noid, "theorem")]],
      tbody noid []
    ];

fun show_criterion (b, c) =
  let
    fun prfx s =
      let
        val (c, v) = if b then ("criterion", s) else ("ncriterion", "-" ^ s);
      in span (class c, v) end;
  in
    (case c of
      Find_Theorems.Name name => prfx ("name: " ^ quote name)
    | Find_Theorems.Intro => prfx "intro"
    | Find_Theorems.Elim => prfx "elim"
    | Find_Theorems.Dest => prfx "dest"
    | Find_Theorems.Solves => prfx "solves"
    | Find_Theorems.Simp pat => prfx ("simp: \"" ^ pat ^ "\"")
    | Find_Theorems.Pattern pat => prfx ("\"" ^ pat ^ "\""))
  end;

fun find_theorems_summary (othmslen, thmslen, args) =
  let
    val args =
      (case othmslen of
         NONE => args
       | SOME l => Symtab.update ("limit", string_of_int l) args)
    val qargs = HttpUtil.make_query_string args;

    val num_found_text =
      (case othmslen of
         NONE => text (string_of_int thmslen)
       | SOME l =>
           a { href = "find_theorems" ^
               (if qargs = "" then "" else "?" ^ qargs),
           text = string_of_int l })
    val found = [text "found ", num_found_text, text " theorems"] : tag list;
    val displayed =
      if is_some othmslen
      then " (" ^ string_of_int thmslen ^ " displayed)"
      else "";
  in
    table (class "findtheoremsquery")
      [ tr [ th' noid (found @ [text (displayed ^ ":")]) ] ]
  end

(* FIXME!?! *)
fun is_sorry thm =
  Thm.proof_of thm
  |> Proofterm.approximate_proof_body
  |> Proofterm.all_oracles_of
  |> exists (fn (x, _) => x = "Pure.skip_proof");

fun sorry_class thm = if is_sorry thm then class "sorried" else noid;

fun html_thm ctxt (n, (thmref, thm)) =
  let
    val output_thm =
      Output.output o Pretty.string_of_margin 100 o
        Display.pretty_thm (Config.put show_question_marks false ctxt);
  in
    tag' "tr" (class ("row" ^ string_of_int (n mod 2)))
      [
        tag' "td" (class "name")
          [span' (sorry_class thm)
             [raw_text (Facts.string_of_ref thmref)]
          ],
        tag' "td" (class "thm") [pre noid (output_thm thm)]
      ]
  end;

end;


