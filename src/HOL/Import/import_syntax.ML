(*  Title:      HOL/Import/import_syntax.ML
    ID:         $Id$
    Author:     Sebastian Skalberg (TU Muenchen)
*)

signature HOL4_IMPORT_SYNTAX =
sig
    type token = OuterSyntax.token

    val import_segment: token list -> (theory -> theory) * token list
    val import_theory : token list -> (theory -> theory) * token list
    val end_import    : token list -> (theory -> theory) * token list

    val setup_theory  : token list -> (theory -> theory) * token list
    val end_setup     : token list -> (theory -> theory) * token list

    val thm_maps      : token list -> (theory -> theory) * token list
    val ignore_thms   : token list -> (theory -> theory) * token list
    val type_maps     : token list -> (theory -> theory) * token list
    val def_maps      : token list -> (theory -> theory) * token list
    val const_maps    : token list -> (theory -> theory) * token list
    val const_moves   : token list -> (theory -> theory) * token list
    val const_renames : token list -> (theory -> theory) * token list

    val setup        : unit -> unit
end

structure HOL4ImportSyntax :> HOL4_IMPORT_SYNTAX =
struct

type token = OuterSyntax.token

local structure P = OuterParse and K = OuterSyntax.Keyword in

(* Parsers *)

val import_segment = P.name >> set_import_segment

val import_theory = P.name >> (fn thyname =>
			       fn thy =>
				  thy |> set_generating_thy thyname
				      |> Theory.add_path thyname
				      |> add_dump (";setup_theory " ^ thyname))

fun end_import toks =
    Scan.succeed
	(fn thy =>
	    let
		val thyname = get_generating_thy thy
		val segname = get_import_segment thy
		val (int_thms,facts) = Replay.setup_int_thms thyname thy
		val thmnames = filter (not o should_ignore thyname thy) facts
	    in
		thy |> clear_import_thy
		    |> set_segment thyname segname
		    |> set_used_names facts
		    |> Replay.import_thms thyname int_thms thmnames
		    |> clear_used_names
		    |> export_hol4_pending
		    |> Theory.parent_path
		    |> dump_import_thy thyname
		    |> add_dump ";end_setup"
	    end) toks

val ignore_thms = Scan.repeat1 P.name
			       >> (fn ignored =>
				   fn thy =>
				      let
					  val thyname = get_import_thy thy
				      in
					  foldl (fn (thy,thmname) => ignore_hol4 thyname thmname thy) (thy,ignored)
				      end)

val thm_maps = Scan.repeat1 (P.name --| P.$$$ ">" -- P.xname)
			    >> (fn thmmaps =>
				fn thy =>
				   let
				       val thyname = get_import_thy thy
				   in
				       foldl (fn (thy,(hol,isa)) => add_hol4_mapping thyname hol isa thy) (thy,thmmaps)
				   end)

val type_maps = Scan.repeat1 (P.name --| P.$$$ ">" -- P.xname)
			     >> (fn typmaps =>
				 fn thy =>
				    let
					val thyname = get_import_thy thy
				    in
					foldl (fn (thy,(hol,isa)) => add_hol4_type_mapping thyname hol false isa thy) (thy,typmaps)
				    end)

val def_maps = Scan.repeat1 (P.name --| P.$$$ ">" -- P.xname)
			    >> (fn defmaps =>
				fn thy =>
				   let
				       val thyname = get_import_thy thy
				   in
				       foldl (fn (thy,(hol,isa)) => add_defmap thyname hol isa thy) (thy,defmaps)
				   end)

val const_renames = Scan.repeat1 (P.name --| P.$$$ ">" -- P.name)
				 >> (fn renames =>
				     fn thy =>
					let
					    val thyname = get_import_thy thy
					in
					    foldl (fn (thy,(hol,isa)) => add_hol4_const_renaming thyname hol isa thy) (thy,renames)
					end)
																      
val const_maps = Scan.repeat1 (P.name --| P.$$$ ">" -- P.xname -- Scan.option (P.$$$ "::" |-- P.typ))
			      >> (fn constmaps =>
				  fn thy =>
				     let
					 val thyname = get_import_thy thy
				     in
					 foldl (fn (thy,((hol,isa),None)) => add_hol4_const_mapping thyname hol false isa thy
						 | (thy,((hol,isa),Some ty)) => add_hol4_const_wt_mapping thyname hol false isa (typ_of (read_ctyp (sign_of thy) ty)) thy) (thy,constmaps)
				     end)

val const_moves = Scan.repeat1 (P.name --| P.$$$ ">" -- P.xname -- Scan.option (P.$$$ "::" |-- P.typ))
			       >> (fn constmaps =>
				   fn thy =>
				      let
					  val thyname = get_import_thy thy
				      in
					  foldl (fn (thy,((hol,isa),None)) => add_hol4_const_mapping thyname hol true isa thy
						  | (thy,((hol,isa),Some ty)) => add_hol4_const_wt_mapping thyname hol true isa (typ_of (read_ctyp (sign_of thy) ty)) thy) (thy,constmaps)
				      end)

fun import_thy s =
    let
	val is = TextIO.openIn(s ^ ".imp")
	val inp = TextIO.inputAll is
	val _ = TextIO.closeIn is
	val orig_source = Source.of_string inp
	val symb_source = Symbol.source false orig_source
	val lexes = ref (OuterLex.make_lexicon ["import_segment","ignore_thms","import","end",">","::","const_maps","const_moves","thm_maps","const_renames","type_maps","def_maps"],
			 Scan.empty_lexicon)
	val get_lexes = fn () => !lexes
	val token_source = OuterLex.source false get_lexes (Position.line 1) symb_source
	val token_list = filter (not o (OuterLex.is_kind OuterLex.Space)) (Source.exhaust token_source)
	val import_segmentP = OuterParse.$$$ "import_segment" |-- import_segment
	val type_mapsP = OuterParse.$$$ "type_maps" |-- type_maps
	val def_mapsP = OuterParse.$$$ "def_maps" |-- def_maps
	val const_mapsP = OuterParse.$$$ "const_maps" |-- const_maps
	val const_movesP = OuterParse.$$$ "const_moves" |-- const_moves
	val const_renamesP = OuterParse.$$$ "const_renames" |-- const_renames
	val ignore_thmsP = OuterParse.$$$ "ignore_thms" |-- ignore_thms
	val thm_mapsP = OuterParse.$$$ "thm_maps" |-- thm_maps
	val parser = type_mapsP || def_mapsP || const_mapsP || const_movesP || const_renamesP || thm_mapsP || ignore_thmsP || import_segmentP
	val importP = OuterParse.$$$ "import" |-- Scan.repeat parser --| OuterParse.$$$ "end"
	fun apply [] thy = thy
	  | apply (f::fs) thy = apply fs (f thy)
    in
	apply (set_replaying_thy s::Theory.add_path s::(fst (importP token_list)))
    end

fun create_int_thms thyname thy =
    if !SkipProof.quick_and_dirty
    then thy
    else
	case ImportData.get thy of
	    None => ImportData.put (Some (fst (Replay.setup_int_thms thyname thy))) thy
	  | Some _ => error "Import data not closed - forgotten an end_setup, mayhap?"

fun clear_int_thms thy =
    if !SkipProof.quick_and_dirty
    then thy
    else
	case ImportData.get thy of
	    None => error "Import data already cleared - forgotten a setup_theory?"
	  | Some _ => ImportData.put None thy

val setup_theory = P.name
		       >>
		       (fn thyname =>
			fn thy =>
			   (case HOL4DefThy.get thy of
				NoImport => thy
			      | Generating _ => error "Currently generating a theory!"
			      | Replaying _ => thy |> clear_import_thy)
			       |> import_thy thyname
			       |> create_int_thms thyname)

fun end_setup toks =
    Scan.succeed
	(fn thy =>
	    let
		val thyname = get_import_thy thy
		val segname = get_import_segment thy
	    in
		thy |> set_segment thyname segname
		    |> clear_import_thy
		    |> clear_int_thms
		    |> Theory.parent_path
	    end) toks

val set_dump  = P.string -- P.string   >> setup_dump
fun fl_dump toks  = Scan.succeed flush_dump toks
val append_dump = (P.verbatim || P.string) >> add_dump

val parsers = 
  [OuterSyntax.command "import_segment"
		       "Set import segment name"
		       K.thy_decl (import_segment >> Toplevel.theory),
   OuterSyntax.command "import_theory"
		       "Set default HOL4 theory name"
		       K.thy_decl (import_theory >> Toplevel.theory),
   OuterSyntax.command "end_import"
		       "End HOL4 import"
		       K.thy_decl (end_import >> Toplevel.theory),
   OuterSyntax.command "setup_theory"
		       "Setup HOL4 theory replaying"
		       K.thy_decl (setup_theory >> Toplevel.theory),
   OuterSyntax.command "end_setup"
		       "End HOL4 setup"
		       K.thy_decl (end_setup >> Toplevel.theory),
   OuterSyntax.command "setup_dump"
		       "Setup the dump file name"
		       K.thy_decl (set_dump >> Toplevel.theory),
   OuterSyntax.command "append_dump"
		       "Add text to dump file"
		       K.thy_decl (append_dump >> Toplevel.theory),
   OuterSyntax.command "flush_dump"
		       "Write the dump to file"
		       K.thy_decl (fl_dump >> Toplevel.theory),
   OuterSyntax.command "ignore_thms"
		       "Theorems to ignore in next HOL4 theory import"
		       K.thy_decl (ignore_thms >> Toplevel.theory),
   OuterSyntax.command "type_maps"
		       "Map HOL4 type names to existing Isabelle/HOL type names"
		       K.thy_decl (type_maps >> Toplevel.theory),
   OuterSyntax.command "def_maps"
		       "Map HOL4 constant names to their primitive definitions"
		       K.thy_decl (def_maps >> Toplevel.theory),
   OuterSyntax.command "thm_maps"
		       "Map HOL4 theorem names to existing Isabelle/HOL theorem names"
		       K.thy_decl (thm_maps >> Toplevel.theory),
   OuterSyntax.command "const_renames"
		       "Rename HOL4 const names"
		       K.thy_decl (const_renames >> Toplevel.theory),
   OuterSyntax.command "const_moves"
		       "Rename HOL4 const names to other HOL4 constants"
		       K.thy_decl (const_moves >> Toplevel.theory),
   OuterSyntax.command "const_maps"
		       "Map HOL4 const names to existing Isabelle/HOL const names"
		       K.thy_decl (const_maps >> Toplevel.theory)]

fun setup () = (OuterSyntax.add_keywords[">"];
		OuterSyntax.add_parsers parsers)

end

end
