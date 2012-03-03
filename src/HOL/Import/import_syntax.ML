(*  Title:      HOL/Import/import_syntax.ML
    Author:     Sebastian Skalberg (TU Muenchen)
*)

signature IMPORTER_IMPORT_SYNTAX =
sig
    val import_segment: (theory -> theory) parser
    val import_theory : (theory -> theory) parser
    val end_import    : (theory -> theory) parser
                        
    val setup_theory  : (theory -> theory) parser
    val end_setup     : (theory -> theory) parser
                        
    val thm_maps      : (theory -> theory) parser
    val ignore_thms   : (theory -> theory) parser
    val type_maps     : (theory -> theory) parser
    val def_maps      : (theory -> theory) parser
    val const_maps    : (theory -> theory) parser
    val const_moves   : (theory -> theory) parser
    val const_renames : (theory -> theory) parser

    val setup        : unit -> unit
end

structure Importer_Import_Syntax :> IMPORTER_IMPORT_SYNTAX =
struct

(* Parsers *)

val import_segment = Parse.name >> set_import_segment


val import_theory = (Parse.name -- Parse.name) >> (fn (location, thyname) =>
                               fn thy =>
                                  thy |> set_generating_thy thyname
                                      |> Sign.add_path thyname
                                      |> add_dump ("setup_theory " ^ quote location ^ " " ^ thyname))

fun end_import toks =
    Scan.succeed
        (fn thy =>
            let
                val thyname = get_generating_thy thy
                val segname = get_import_segment thy
                val (int_thms,facts) = Replay.setup_int_thms thyname thy
                val thmnames = filter_out (should_ignore thyname thy) facts
                fun replay thy = Replay.import_thms thyname int_thms thmnames thy
            in
                thy |> clear_import_thy
                    |> set_segment thyname segname
                    |> set_used_names facts
                    |> replay 
                    |> clear_used_names
                    |> export_importer_pending
                    |> Sign.parent_path
                    |> dump_import_thy thyname
                    |> add_dump ";end_setup"
            end) toks

val ignore_thms = Scan.repeat1 Parse.name
                               >> (fn ignored =>
                                   fn thy =>
                                      let
                                          val thyname = get_import_thy thy
                                      in
                                          Library.foldl (fn (thy,thmname) => ignore_importer thyname thmname thy) (thy,ignored)
                                      end)

val thm_maps = Scan.repeat1 (Parse.name --| Parse.$$$ ">" -- Parse.xname)
                            >> (fn thmmaps =>
                                fn thy =>
                                   let
                                       val thyname = get_import_thy thy
                                   in
                                       Library.foldl (fn (thy,(hol,isa)) => add_importer_mapping thyname hol isa thy) (thy,thmmaps)
                                   end)

val type_maps = Scan.repeat1 (Parse.name --| Parse.$$$ ">" -- Parse.xname)
                             >> (fn typmaps =>
                                 fn thy =>
                                    let
                                        val thyname = get_import_thy thy
                                    in
                                        Library.foldl (fn (thy,(hol,isa)) => add_importer_type_mapping thyname hol false isa thy) (thy,typmaps)
                                    end)

val def_maps = Scan.repeat1 (Parse.name --| Parse.$$$ ">" -- Parse.xname)
                            >> (fn defmaps =>
                                fn thy =>
                                   let
                                       val thyname = get_import_thy thy
                                   in
                                       Library.foldl (fn (thy,(hol,isa)) => add_defmap thyname hol isa thy) (thy,defmaps)
                                   end)

val const_renames = Scan.repeat1 (Parse.name --| Parse.$$$ ">" -- Parse.name)
                                 >> (fn renames =>
                                     fn thy =>
                                        let
                                            val thyname = get_import_thy thy
                                        in
                                            Library.foldl (fn (thy,(hol,isa)) => add_importer_const_renaming thyname hol isa thy) (thy,renames)
                                        end)
                                                                                                                                      
val const_maps = Scan.repeat1 (Parse.name --| Parse.$$$ ">" -- Parse.xname -- Scan.option (Parse.$$$ "::" |-- Parse.typ))
                              >> (fn constmaps =>
                                  fn thy =>
                                     let
                                         val thyname = get_import_thy thy
                                     in
                                         Library.foldl (fn (thy,((hol,isa),NONE)) => add_importer_const_mapping thyname hol false isa thy
                                                 | (thy,((hol,isa),SOME ty)) => add_importer_const_wt_mapping thyname hol false isa (Syntax.read_typ_global thy ty) thy) (thy,constmaps)
                                     end)

val const_moves = Scan.repeat1 (Parse.name --| Parse.$$$ ">" -- Parse.xname -- Scan.option (Parse.$$$ "::" |-- Parse.typ))
                               >> (fn constmaps =>
                                   fn thy =>
                                      let
                                          val thyname = get_import_thy thy
                                      in
                                          Library.foldl (fn (thy,((hol,isa),NONE)) => add_importer_const_mapping thyname hol true isa thy
                                                  | (thy,((hol,isa),SOME ty)) => add_importer_const_wt_mapping thyname hol true isa (Syntax.read_typ_global thy ty) thy) (thy,constmaps)
                                      end)

fun import_thy location s =
    let
        val src_location = Path.append (Path.explode location) (Path.basic (s ^ ".imp"))
        val is = TextIO.openIn (File.platform_path src_location)
        val inp = TextIO.inputAll is
        val _ = TextIO.closeIn is
        val orig_source = Source.of_string inp
        val symb_source = Symbol.source orig_source
        val lexes =
          (Scan.make_lexicon
            (map Symbol.explode ["import_segment","ignore_thms","import","end",">","::","const_maps","const_moves","thm_maps","const_renames","type_maps","def_maps"]),
                  Scan.empty_lexicon)
        val token_source = Token.source {do_recover = NONE} (K lexes) Position.start symb_source
        val token_list = filter_out (Token.is_kind Token.Space) (Source.exhaust token_source)
        val import_segmentP = Parse.$$$ "import_segment" |-- import_segment
        val type_mapsP = Parse.$$$ "type_maps" |-- type_maps
        val def_mapsP = Parse.$$$ "def_maps" |-- def_maps
        val const_mapsP = Parse.$$$ "const_maps" |-- const_maps
        val const_movesP = Parse.$$$ "const_moves" |-- const_moves
        val const_renamesP = Parse.$$$ "const_renames" |-- const_renames
        val ignore_thmsP = Parse.$$$ "ignore_thms" |-- ignore_thms
        val thm_mapsP = Parse.$$$ "thm_maps" |-- thm_maps
        val parser = type_mapsP || def_mapsP || const_mapsP || const_movesP || const_renamesP || thm_mapsP || ignore_thmsP || import_segmentP
        val importP = Parse.$$$ "import" |-- Scan.repeat parser --| Parse.$$$ "end"
        fun apply [] thy = thy
          | apply (f::fs) thy = apply fs (f thy)
    in
        apply (set_replaying_thy s :: Sign.add_path s :: fst (importP token_list))
    end

fun create_int_thms thyname thy =
    if ! quick_and_dirty
    then thy
    else
        case ImportData.get thy of
            NONE => ImportData.put (SOME (fst (Replay.setup_int_thms thyname thy))) thy
          | SOME _ => error "Import data not closed - forgotten an end_setup, mayhap?"

fun clear_int_thms thy =
    if ! quick_and_dirty
    then thy
    else
        case ImportData.get thy of
            NONE => error "Import data already cleared - forgotten a setup_theory?"
          | SOME _ => ImportData.put NONE thy

val setup_theory = (Parse.name -- Parse.name)
                       >>
                       (fn (location, thyname) =>
                        fn thy =>
                           (case Importer_DefThy.get thy of
                                NoImport => thy
                              | Generating _ => error "Currently generating a theory!"
                              | Replaying _ => thy |> clear_import_thy)
                               |> import_thy location thyname
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
                    |> Sign.parent_path
            end) toks

val set_dump  = Parse.string -- Parse.string   >> setup_dump
fun fl_dump toks  = Scan.succeed flush_dump toks
val append_dump = (Parse.verbatim || Parse.string) >> add_dump

fun setup () =
  (Keyword.keyword ">";
   Outer_Syntax.command "import_segment"
                       "Set import segment name"
                       Keyword.thy_decl (import_segment >> Toplevel.theory);
   Outer_Syntax.command "import_theory"
                       "Set default external theory name"
                       Keyword.thy_decl (import_theory >> Toplevel.theory);
   Outer_Syntax.command "end_import"
                       "End external import"
                       Keyword.thy_decl (end_import >> Toplevel.theory);
   Outer_Syntax.command "setup_theory"
                       "Setup external theory replaying"
                       Keyword.thy_decl (setup_theory >> Toplevel.theory);
   Outer_Syntax.command "end_setup"
                       "End external setup"
                       Keyword.thy_decl (end_setup >> Toplevel.theory);
   Outer_Syntax.command "setup_dump"
                       "Setup the dump file name"
                       Keyword.thy_decl (set_dump >> Toplevel.theory);
   Outer_Syntax.command "append_dump"
                       "Add text to dump file"
                       Keyword.thy_decl (append_dump >> Toplevel.theory);
   Outer_Syntax.command "flush_dump"
                       "Write the dump to file"
                       Keyword.thy_decl (fl_dump >> Toplevel.theory);
   Outer_Syntax.command "ignore_thms"
                       "Theorems to ignore in next external theory import"
                       Keyword.thy_decl (ignore_thms >> Toplevel.theory);
   Outer_Syntax.command "type_maps"
                       "Map external type names to existing Isabelle/HOL type names"
                       Keyword.thy_decl (type_maps >> Toplevel.theory);
   Outer_Syntax.command "def_maps"
                       "Map external constant names to their primitive definitions"
                       Keyword.thy_decl (def_maps >> Toplevel.theory);
   Outer_Syntax.command "thm_maps"
                       "Map external theorem names to existing Isabelle/HOL theorem names"
                       Keyword.thy_decl (thm_maps >> Toplevel.theory);
   Outer_Syntax.command "const_renames"
                       "Rename external const names"
                       Keyword.thy_decl (const_renames >> Toplevel.theory);
   Outer_Syntax.command "const_moves"
                       "Rename external const names to other external constants"
                       Keyword.thy_decl (const_moves >> Toplevel.theory);
   Outer_Syntax.command "const_maps"
                       "Map external const names to existing Isabelle/HOL const names"
                       Keyword.thy_decl (const_maps >> Toplevel.theory));

end
