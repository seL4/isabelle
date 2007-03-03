(*  Title:      Pure/ProofGeneral/parsing.ML
    ID:         $Id$
    Author:     David Aspinall

Parsing Isabelle theory files to add PGIP markup.
*)

signature PGIP_PARSER =
sig
    val pgip_parser: PgipMarkup.pgip_parser
    val init : unit -> unit		     (* clear state *)
end

structure PgipParser : PGIP_PARSER =
struct


(** Parsing proof scripts without execution **)

structure P = OuterParse;

structure D = PgipMarkup;
structure I = PgipIsabelle;
structure T = PgipTypes;

(* Notes.
   This is quite tricky, because 1) we need to put back whitespace which
   was removed during parsing so we can provide markup around commands;
   2) parsing is intertwined with execution in Isar so we have to repeat
   the parsing to extract interesting parts of commands.  The trace of
   tokens parsed which is now recorded in each transition (added by
   Markus June '04) helps do this, but the mechanism is still a bad mess.

   If we had proper parse trees it would be easy, although having a
   fixed type of trees might be hard with Isar's extensible parser.

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
    val keywords_classification_table = ref (NONE: string Symtab.table option)

in
    fun get_keywords_classification_table () =
        case (!keywords_classification_table) of
          SOME t => t
        | NONE => (let
                     val tab = fold (fn (c, _, k, _) => Symtab.update (c, k))
                                    (OuterSyntax.dest_parsers ()) Symtab.empty;
                   in (keywords_classification_table := SOME tab; tab) end)
  
    (* To allow dynamic extensions to language during interactive use
       we need a hook in outer_syntax.ML to reset our table.  But this is
       pretty obscure; initialisation at startup should suffice. *)

    fun init () = (keywords_classification_table := NONE)
end


local

    fun whitespace str = D.Whitespace { text=str }

    (* an extra token is needed to terminate the command *)
    val sync = OuterSyntax.scan "\\<^sync>";

    fun nameparse elt objtyp nameP toks = 
        (fst (nameP (toks@sync)))
        handle _ => (error ("Error occurred in name parser for " ^ elt ^
                            "(objtype: " ^ (T.name_of_objtype objtyp) ^ ")");
                     "")

    fun parse_warning msg = warning ("script->PGIP markup parser: " ^ msg)

    fun xmls_of_thy_begin (name,toks,str) = (* see isar_syn.ML/theoryP *)
        let
            val ((thyname,imports,files),_) = ThyHeader.args (toks@sync)
        in
            [D.Opentheory { thyname=thyname, 
			    parentnames = imports,
			    text = str },
	     D.Openblock { metavarid=NONE,name=NONE,objtype=SOME I.ObjTheoryBody }]
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

            fun named_item nameP ty = 
		[D.Theoryitem {text=str,
			       name=SOME (nameparse "theoryitem" ty nameP toks),
			       objtype=SOME ty}]
	    val plain_item = 
		[D.Theoryitem {text=str,name=NONE,objtype=NONE}]
	    val doccomment = 
		[D.Doccomment {text=str}]

            val opt_overloaded = P.opt_keyword "overloaded";

            val thmnameP = (* see isar_syn.ML/theoremsP *)
                let
                    val name_facts = P.and_list1 ((SpecParse.opt_thm_name "=" --| SpecParse.xthms1) >> #1)
                    val theoremsP = P.opt_target |-- name_facts >> (fn [] => "" | x::_ => x)
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
                     "text"      => doccomment
                   | "text_raw"  => doccomment
                   | "typedecl"  => named_item (P.type_args |-- P.name) T.ObjType
                   | "types"     => named_item (P.type_args |-- P.name) T.ObjType
                   | "classes"   => named_item P.name I.ObjClass
                   | "classrel"  => named_item P.name I.ObjClass
                   | "consts"    => named_item (P.const >> #1) T.ObjTerm
                   | "axioms"    => named_item (SpecParse.spec_name >> (#1 o #1)) T.ObjTheorem
                   | "defs"      => named_item (opt_overloaded |-- SpecParse.spec_name >> (#1 o #1)) T.ObjTheorem
                   | "constdefs" => named_item P.name (* FIXME: heavily simplified/wrong *) T.ObjTerm
                   | "theorems"  => named_item thmnameP I.ObjTheoremSet
                   | "lemmas"    => named_item thmnameP I.ObjTheoremSet
                   | "oracle"    => named_item P.name I.ObjOracle
		   (* FIXME: locale needs to introduce a block *)
                   | "locale"    => named_item ((P.opt_keyword "open" >> not) |-- P.name) I.ObjLocale
                   | _ => (parse_warning ("Unrecognized thy-decl command: " ^ name); 
			   plain_item)
        end

    fun xmls_of_thy_goal (name,toks,str) =
        let
            (* see isar_syn.ML/gen_theorem *)
         val statement = P.and_list1 (SpecParse.opt_thm_name ":" -- Scan.repeat1 P.propp);
         val general_statement =
            statement >> pair [] || Scan.repeat SpecParse.locale_element -- (P.$$$ "shows" |-- statement);

            val gen_theoremP =
                P.opt_target -- Scan.optional (SpecParse.opt_thm_name ":" --|
                 Scan.ahead (SpecParse.locale_keyword || P.$$$ "shows")) ("", []) --
                                 general_statement >> (fn ((locale, a), (elems, concl)) =>
                                                         fst a) (* a : (bstring * Args.src list) *)

            val nameP = P.opt_target |-- (Scan.optional ((SpecParse.opt_thm_name ":") >> #1) "")
	    val thmname = nameparse "opengoal" T.ObjTheorem nameP toks
        in
            [D.Opengoal {thmname=SOME thmname, text=str},
             D.Openblock {metavarid=NONE,name=NONE,objtype=SOME I.ObjProofBody}]
        end

    fun xmls_of_qed (name,str) =
        let val qedmarkup  =
                (case name of
                     "sorry" => D.Postponegoal {text=str}
                   | "oops"  => D.Giveupgoal {text=str}
                   | "done"  => D.Closegoal {text=str}
                   | "by"    => D.Closegoal {text=str}  (* nested or toplevel *)
                   | "qed"   => D.Closegoal {text=str}  (* nested or toplevel *)
                   | "."     => D.Closegoal {text=str}  (* nested or toplevel *)
                   | ".."    => D.Closegoal {text=str}  (* nested or toplevel *)
                   | other => (* default to closegoal: may be wrong for extns *)
                                  (parse_warning
                                       ("Unrecognized qed command: " ^ quote other);
                                       D.Closegoal {text=str}))
        in qedmarkup :: [D.Closeblock {}] end

    fun xmls_of_kind kind (name,toks,str) =
    case kind of
      "control"        => [D.Badcmd {text=str}]
    | "diag"           => [D.Spuriouscmd {text=str}]
    (* theory/files *)
    | "theory-begin"   => xmls_of_thy_begin (name,toks,str)
    | "theory-decl"    => xmls_of_thy_decl (name,toks,str)
    | "theory-heading" => [D.Closeblock {},
			   D.Doccomment {text=str},
			   D.Openblock {metavarid=NONE,name=NONE,objtype=SOME I.ObjTheoryBody}]
    | "theory-script"  => [D.Theoryitem {name=NONE,objtype=SOME I.ObjTheoryDecl,text=str}]
    | "theory-end"     => [D.Closeblock {}, D.Closetheory {text=str}]
    (* proof control *)
    | "theory-goal"    => xmls_of_thy_goal (name,toks,str)
    | "proof-heading"  => [D.Doccomment {text=str}]
    | "proof-goal"     => [D.Opengoal {text=str,thmname=NONE}, 
			   D.Openblock {metavarid=NONE,name=NONE,objtype=SOME I.ObjProofBody}]
    | "proof-block"    => [D.Closeblock {}, 
			   D.Proofstep {text=str},
			   D.Openblock {metavarid=NONE,name=NONE,objtype=SOME I.ObjProofBody}]
    | "proof-open"     => [D.Openblock {metavarid=NONE,name=NONE,objtype=SOME I.ObjProofBody}, 
			   D.Proofstep {text=str} ]
    | "proof-close"    => [D.Proofstep {text=str}, D.Closeblock {}]
    | "proof-script"   => [D.Proofstep {text=str}]
    | "proof-chain"    => [D.Proofstep {text=str}]
    | "proof-decl"     => [D.Proofstep {text=str}]
    | "proof-asm"      => [D.Proofstep {text=str}]
    | "proof-asm-goal" => [D.Opengoal {text=str,thmname=NONE}, 
			   D.Openblock {metavarid=NONE,name=NONE,objtype=NONE}]
    | "qed"            => xmls_of_qed (name,str)
    | "qed-block"      => xmls_of_qed (name,str)
    | "qed-global"     => xmls_of_qed (name,str)
    | other => (* default for anything else is "spuriouscmd", ***ignored for undo*** *)
      (parse_warning ("Internal inconsistency, unrecognized keyword kind: " ^ quote other ^
		      "(treated as spuriouscmd)");
       [D.Spuriouscmd {text=str}])
in

fun xmls_of_transition (name,str,toks) =
   let
     val classification = Symtab.lookup (get_keywords_classification_table ()) name
   in case classification of
          SOME k => (xmls_of_kind k (name,toks,str))
        | NONE => (* an uncategorized keyword is treated as a theory item (maybe wrong) *)
          (parse_warning ("Uncategorized command found: " ^ name ^ " -- using theoryitem");
           [D.Theoryitem {name=NONE,objtype=NONE,text=str}])
   end


(* this would be a lot neater if we could match on toks! *)
fun markup_comment_whs [] = []
  | markup_comment_whs (toks as t::ts) = 
    let
        val (prewhs,rest) = take_prefix (OuterLex.is_kind OuterLex.Space) toks
    in
        if not (null prewhs) then
            D.Whitespace {text=implode (map OuterLex.unparse prewhs)}
            :: (markup_comment_whs rest)
        else
            D.Comment {text=OuterLex.unparse t} ::
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
        (* NB: this collapses  doccomment,(doccomment|whitespace)* to a single doccomment *)
        val (_,rest2) = (Scan.bulk (P.$$$ "--" |-- text_with_whs) >> implode || Scan.succeed "") rest1
        val (postwhs,rest3) = take_prefix (not o OuterLex.is_proper) rest2
    in
        ((markup_comment_whs prewhs) @
         (if (length rest2 = length rest1)  then []
          else 
	      [D.Doccomment 
		   {text= implode
                          (map OuterLex.unparse (Library.take (length rest1 - length rest2, rest1)))}]
              @
              (markup_comment_whs postwhs)),
              Library.take (length rest3 - 1,rest3))
    end

fun xmls_of_impropers toks =
    let
        val (xmls,rest) = xmls_pre_cmd toks
	val unparsed =  
	    case rest of [] => []
		       | _ => [D.Unparseable 
			      {text= implode (map OuterLex.unparse rest)}]
    in
        xmls @ unparsed
    end

end


local
    (* we have to weave together the whitespace/comments with proper tokens
       to reconstruct the input. *)
    (* TODO: see if duplicating isar_output/parse_thy can help here *)

    fun match_tokens ([],us,vs) = (rev vs,us)  (* used, unused *)
      | match_tokens (t::ts, w::ws, vs) =
        if (t: OuterLex.token) = w  (* FIXME !? *)
          then match_tokens (ts, ws, w::vs)
          else match_tokens (t::ts, ws, w::vs)
      | match_tokens _ = error ("match_tokens: mismatched input parse")
in
    fun pgip_parser str =
    let
       (* parsing:   See outer_syntax.ML/toplevel_source *)
       fun parse_loop ([],[],xmls) = xmls
         | parse_loop ([],itoks,xmls) = xmls @ (xmls_of_impropers itoks)
         | parse_loop ((nm,toks,_)::trs,itoks,xmls) =
           let
               (* first proper token after whitespace/litcomment/whitespace is command *)
               val (xmls_pre_cmd,cmditoks') = xmls_pre_cmd itoks
               val (cmdtok,itoks') = 
		   case cmditoks' of x::xs => (x,xs)
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
           handle _ => [D.Unparseable {text=str}]
    end
end

end
