(*  Title:      Pure/ProofGeneral/parsing.ML
    ID:         $Id$
    Author:     David Aspinall

Parsing theory files to add PGIP markup.
*)

signature PGIP_PARSER =
sig
    val xmls_of_str: string -> XML.content
end

structure PgipParser : PGIP_PARSER =
struct


(** Parsing proof scripts without execution **)

structure P = OuterParse;

(* Notes.
   This is quite tricky, because 1) we need to put back whitespace which
   was removed during parsing so we can provide markup around commands;
   2) parsing is intertwined with execution in Isar so we have to repeat
   the parsing to extract interesting parts of commands.  The trace of
   tokens parsed which is now recorded in each transition (added by
   Markus June '04) helps do this, but the mechanism is still a bad mess.

   If we had proper parse trees it would be easy, although having a
   fixed type of trees might be tricky with Isar's extensible parser.

   Probably the best solution is to produce the meta-information at
   the same time as the parse, for each command, e.g. by recording a
   list of (name,objtype) pairs which record the bindings created by
   a command.  This would require changing the interfaces in
   outer_syntax.ML (or providing new ones),

    datatype metainfo = Binding of string * string  (* name, objtype *)

    val command_withmetainfo: string -> string -> string ->
      (token list ->
       ((Toplevel.transition -> Toplevel.transition) * metainfo list) *
       token list) -> parser

   We'd also like to render terms as they appear in output, but this
   will be difficult because inner syntax is extensible and we don't
   have the correct syntax to hand when just doing outer parsing
   without execution.  A reasonable approximation could
   perhaps be obtained by using the syntax of the current context.
   However, this would mean more mess trying to pick out terms,
   so at this stage a more serious change to the Isar functions
   seems necessary.
*)

local
    fun markup_text str elt = [XML.Elem(elt, [], [XML.Text str])]
    fun markup_text_attrs str elt attrs = [XML.Elem(elt, attrs, [XML.Text str])]
    fun empty elt = [XML.Elem(elt, [], [])]

    fun whitespace str = XML.Elem("whitespace", [], [XML.Text str])

    (* an extra token is needed to terminate the command *)
    val sync = OuterSyntax.scan "\\<^sync>";

    fun named_item_elt_with nameattr toks str elt nameP objtyp =
        let
            val name = (fst (nameP (toks@sync)))
                        handle _ => (error ("Error occurred in name parser for " ^ elt ^
                                            "(objtype: " ^ objtyp ^ ")");
                                     "")

        in
            [XML.Elem(elt,
                     ((if name="" then [] else [(nameattr, name)])@
                      (if objtyp="" then [] else [("objtype", objtyp)])),
                     [XML.Text str])]
        end

    val named_item_elt = named_item_elt_with "name"
    val thmnamed_item_elt = named_item_elt_with "thmname"

    fun parse_warning msg = warning ("script->PGIP markup parser: " ^ msg)

    (* FIXME: allow dynamic extensions to language here: we need a hook in
       outer_syntax.ML to reset this table. *)

    val keywords_classification_table = ref (NONE: string Symtab.table option)

    fun get_keywords_classification_table () =
        case (!keywords_classification_table) of
          SOME t => t
        | NONE => (let
                     val tab = fold (fn (c, _, k, _) => Symtab.update (c, k))
                                    (OuterSyntax.dest_parsers ()) Symtab.empty;
                   in (keywords_classification_table := SOME tab; tab) end)



    fun xmls_of_thy_begin (name,toks,str) = (* see isar_syn.ML/theoryP *)
        let
            val ((thyname,imports,files),_) = ThyHeader.args (toks@sync)
        in
            markup_text_attrs str "opentheory"
                              ([("thyname",thyname)] @
                               (if imports=[] then [] else
                                [("parentnames", (space_implode ";" imports) ^ ";")]))
        end

    fun xmls_of_thy_decl (name,toks,str) = (* see isar_syn.ML/thy_decl cases  *)
        let
            (* NB: PGIP only deals with single name bindings at the moment;
               potentially we could markup grouped definitions several times but
               that might suggest the wrong structure to the editor?
               Better alternative would be to put naming closer around text,
               but to do that we'd be much better off modifying the real parser
               instead of reconstructing it here. *)

            val plain_items = (* no names, unimportant names, or too difficult *)
                ["defaultsort","arities","judgement","finalconsts",
                 "syntax", "nonterminals", "translations",
                 "global", "local", "hide",
                 "ML_setup", "setup", "method_setup",
                 "parse_ast_translation", "parse_translation", "print_translation",
                 "typed_print_translation", "print_ast_translation", "token_translation",
                 "oracle",
                 "declare"]

            val plain_item   = markup_text str "theoryitem"
            val comment_item = markup_text str "doccomment"
            val named_item   = named_item_elt toks str "theoryitem"

            val opt_overloaded = P.opt_keyword "overloaded";

            val thmnameP = (* see isar_syn.ML/theoremsP *)
                let
                    val name_facts = P.and_list1 ((P.opt_thm_name "=" --| P.xthms1) >> #1)
                    val theoremsP = P.opt_locale_target |-- name_facts >> (fn [] => "" | x::_ => x)
                in
                    theoremsP
                end
        in
            (* TODO: ideally we would like to render terms properly, just as they are
               in output. This implies using PGML for symbols and variables/atoms.
               BUT it's rather tricky without having the correct concrete syntax to hand,
               and even if we did, we'd have to mess around here a whole lot more first
               to pick out the terms from the syntax. *)

            if member (op =) plain_items name then plain_item
            else case name of
                     "text"      => comment_item
                   | "text_raw"  => comment_item
                   | "typedecl"  => named_item (P.type_args |-- P.name) "type"
                   | "types"     => named_item (P.type_args |-- P.name) "type"
                   | "classes"   => named_item P.name "class"
                   | "classrel"  => named_item P.name "class"
                   | "consts"    => named_item (P.const >> #1) "term"
                   | "axioms"    => named_item (P.spec_name >> (#1 o #1)) "theorem"
                   | "defs"      => named_item (opt_overloaded |-- P.spec_name >> (#1 o #1)) "theorem"
                   | "constdefs" => named_item P.name (* FIXME: heavily simplified/wrong *) "term"
                   | "theorems"  => named_item thmnameP "thmset"
                   | "lemmas"    => named_item thmnameP "thmset"
                   | "oracle"    => named_item P.name "oracle"
                   | "locale"    => named_item ((P.opt_keyword "open" >> not) |-- P.name) "locale"
                   | _ => (parse_warning ("Unrecognized thy-decl command: " ^ name); plain_item)
        end

    fun xmls_of_thy_goal (name,toks,str) =
        let
            (* see isar_syn.ML/gen_theorem *)
         val statement = P.and_list1 (P.opt_thm_name ":" -- Scan.repeat1 P.propp);
         val general_statement =
            statement >> pair [] || Scan.repeat P.locale_element -- (P.$$$ "shows" |-- statement);

            val gen_theoremP =
                P.opt_locale_target -- Scan.optional (P.opt_thm_name ":" --|
                 Scan.ahead (P.locale_keyword || P.$$$ "shows")) ("", []) --
                                 general_statement >> (fn ((locale, a), (elems, concl)) =>
                                                         fst a) (* a : (bstring * Args.src list) *)

            val nameP = P.opt_locale_target |-- (Scan.optional ((P.opt_thm_name ":") >> #1) "")
            (* TODO: add preference values for attributes
               val prefval = XML.element "prefval" [("name","thm-kind"),("value",name)]
            *)
        in
            (thmnamed_item_elt toks str "opengoal" nameP "") @
            (empty "openblock")
        end

    fun xmls_of_qed (name,markup) =
        let val qedmarkup  =
                (case name of
                     "sorry" => markup "postponegoal"
                   | "oops"  => markup "giveupgoal"
                   | "done"  => markup "closegoal"
                   | "by"    => markup "closegoal"  (* nested or toplevel *)
                   | "qed"   => markup "closegoal"  (* nested or toplevel *)
                   | "."     => markup "closegoal"  (* nested or toplevel *)
                   | ".."    => markup "closegoal"  (* nested or toplevel *)
                   | other => (* default to closegoal: may be wrong for extns *)
                                  (parse_warning
                                       ("Unrecognized qed command: " ^ quote other);
                                       markup "closegoal"))
        in qedmarkup @ (empty "closeblock") end

    fun xmls_of_kind kind (name,toks,str) =
    let val markup = markup_text str in
    case kind of
      "control"        => markup "badcmd"
    | "diag"           => markup "spuriouscmd"
    (* theory/files *)
    | "theory-begin"   => xmls_of_thy_begin (name,toks,str)
    | "theory-decl"    => xmls_of_thy_decl (name,toks,str)
    | "theory-heading" => markup "doccomment"
    | "theory-script"  => markup "theorystep"
    | "theory-end"     => markup "closetheory"
    (* proof control *)
    | "theory-goal"    => xmls_of_thy_goal (name,toks,str)
    | "proof-heading"  => markup "doccomment"
    | "proof-goal"     => (markup "opengoal") @ (empty "openblock")  (* nested proof: have, show, ... *)
    | "proof-block"    => markup "proofstep" (* context-shift: proof, next; really "newgoal" *)
    | "proof-open"     => (empty "openblock") @ (markup "proofstep")
    | "proof-close"    => (markup "proofstep") @ (empty "closeblock")
    | "proof-script"   => markup "proofstep"
    | "proof-chain"    => markup "proofstep"
    | "proof-decl"     => markup "proofstep"
    | "proof-asm"      => markup "proofstep"
    | "proof-asm-goal" => (markup "opengoal") @ (empty "openblock")  (* nested proof: obtain *)
    | "qed"            => xmls_of_qed (name,markup)
    | "qed-block"      => xmls_of_qed (name,markup)
    | "qed-global"     => xmls_of_qed (name,markup)
    | other => (* default for anything else is "spuriouscmd", ignored for undo *)
      (parse_warning ("Internal inconsistency, unrecognized keyword kind: " ^ quote other);
       markup "spuriouscmd")
    end
in

fun xmls_of_transition (name,str,toks) =
   let
     val classification = Symtab.lookup (get_keywords_classification_table ()) name
   in case classification of
          SOME k => (xmls_of_kind k (name,toks,str))
        | NONE => (* an uncategorized keyword ignored for undo (maybe wrong) *)
          (parse_warning ("Uncategorized command found: " ^ name ^ " -- using spuriouscmd");
           markup_text str "spuriouscmd")
   end

fun markup_toks [] _ = []
  | markup_toks toks x = markup_text (implode (map OuterLex.unparse toks)) x

fun markup_comment_whs [] = []
  | markup_comment_whs (toks as t::ts) = (* this would be a lot neater if we could match on toks! *)
    let
        val (prewhs,rest) = take_prefix (OuterLex.is_kind OuterLex.Space) toks
    in
        if (prewhs <> []) then
            whitespace (implode (map OuterLex.unparse prewhs))
            :: (markup_comment_whs rest)
        else
            (markup_text (OuterLex.unparse t) "comment") @
            (markup_comment_whs ts)
    end

fun xmls_pre_cmd [] = ([],[])
  | xmls_pre_cmd toks =
    let
        (* an extra token is needed to terminate the command *)
        val sync = OuterSyntax.scan "\\<^sync>";
        val spaceP = Scan.bulk (Scan.one (fn t =>not (OuterLex.is_proper t)) >> OuterLex.val_of) >> implode
        val text_with_whs =
            ((spaceP || Scan.succeed "") --
             (P.short_ident || P.long_ident || P.sym_ident || P.string || P.number || P.verbatim) >> op^)
             -- (spaceP || Scan.succeed "") >> op^
        val (prewhs,rest1) = take_prefix (not o OuterLex.is_proper) (toks@sync)
        (* NB: this collapses  litcomment,(litcomment|whitespace)* to a single litcomment *)
        val (_,rest2) = (Scan.bulk (P.$$$ "--" |-- text_with_whs) >> implode || Scan.succeed "") rest1
        val (postwhs,rest3) = take_prefix (not o OuterLex.is_proper) rest2
    in
        ((markup_comment_whs prewhs) @
         (if (length rest2 = length rest1)  then []
          else markup_text (implode
                                (map OuterLex.unparse (Library.take (length rest1 - length rest2, rest1))))
               "doccomment") @
         (markup_comment_whs postwhs),
         Library.take (length rest3 - 1,rest3))
    end

fun xmls_of_impropers toks =
    let
        val (xmls,rest) = xmls_pre_cmd toks
    in
        xmls @ (markup_toks rest "unparseable")
    end

fun markup_unparseable str = markup_text str "unparseable"

end


local
    (* we have to weave together the whitespace/comments with proper tokens
       to reconstruct the input. *)
    (* TODO: see if duplicating isar_output/parse_thy can help here *)

    fun match_tokens ([],us,vs) = (rev vs,us)  (* used, unused *)
      | match_tokens (t::ts,w::ws,vs) =
        if (t = w) then match_tokens (ts,ws,w::vs)
        else match_tokens (t::ts,ws,w::vs)
      | match_tokens _ = error ("match_tokens: mismatched input parse")
in
    fun xmls_of_str str =
    let
       (* parsing:   See outer_syntax.ML/toplevel_source *)
       fun parse_loop ([],[],xmls) = xmls
         | parse_loop ([],itoks,xmls) = xmls @ (xmls_of_impropers itoks)
         | parse_loop ((nm,toks,_)::trs,itoks,xmls) =
           let
               (* first proper token after whitespace/litcomment/whitespace is command *)
               val (xmls_pre_cmd,cmditoks') = xmls_pre_cmd itoks
               val (cmdtok,itoks') = case cmditoks' of x::xs => (x,xs)
                                                     | _ => error("proof_general/parse_loop impossible")
               val (utoks,itoks'') = match_tokens (toks,itoks',[])
               (* FIXME: should take trailing [w/s+] semicolon too in utoks *)

               val str = implode (map OuterLex.unparse (cmdtok::utoks))

               val xmls_tr  = xmls_of_transition (nm,str,toks)
           in
               parse_loop(trs,itoks'',xmls @ xmls_pre_cmd @ xmls_tr)
           end
    in
        (let val toks = OuterSyntax.scan str
         in
             parse_loop (OuterSyntax.read toks, toks, [])
         end)
           handle _ => markup_unparseable str
    end
end

end
