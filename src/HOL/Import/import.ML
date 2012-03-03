(*  Title:      HOL/Import/import.ML
    Author:     Sebastian Skalberg (TU Muenchen)
*)

signature IMPORT =
sig
    val debug      : bool Unsynchronized.ref
    val import_tac : Proof.context -> string * string -> tactic
    val setup      : theory -> theory
end

structure ImportData = Theory_Data
(
  type T = ProofKernel.thm option array option  (* FIXME mutable array !??!!! *)
  val empty = NONE
  val extend = I
  fun merge _ = NONE
)

structure Import : IMPORT =
struct

val debug = Unsynchronized.ref false
fun message s = if !debug then writeln s else ()

fun import_tac ctxt (thyname, thmname) =
    if ! quick_and_dirty
    then Skip_Proof.cheat_tac (Proof_Context.theory_of ctxt)
    else
     fn th =>
        let
            val thy = Proof_Context.theory_of ctxt
            val prem = hd (prems_of th)
            val _ = message ("Import_tac: thyname=" ^ thyname ^ ", thmname=" ^ thmname)
            val _ = message ("Import trying to prove " ^ Syntax.string_of_term ctxt prem)
            val int_thms = case ImportData.get thy of
                               NONE => fst (Replay.setup_int_thms thyname thy)
                             | SOME a => a
            val proof = snd (ProofKernel.import_proof thyname thmname thy) thy
            val importerthm = snd (Replay.replay_proof int_thms thyname thmname proof thy)
            val thm = snd (ProofKernel.to_isa_thm importerthm)
            val rew = ProofKernel.rewrite_importer_term (concl_of thm) thy
            val thm = Thm.equal_elim rew thm
            val prew = ProofKernel.rewrite_importer_term prem thy
            val prem' = #2 (Logic.dest_equals (prop_of prew))
            val _ = message ("Import proved " ^ Display.string_of_thm ctxt thm)
            val thm = ProofKernel.disambiguate_frees thm
            val _ = message ("Disambiguate: " ^ Display.string_of_thm ctxt thm)
        in
            case Shuffler.set_prop thy prem' [("",thm)] of
                SOME (_,thm) =>
                let
                    val _ = if prem' aconv (prop_of thm)
                            then message "import: Terms match up"
                            else message "import: Terms DO NOT match up"
                    val thm' = Thm.equal_elim (Thm.symmetric prew) thm
                    val res = Thm.bicompose true (false,thm',0) 1 th
                in
                    res
                end
              | NONE => (message "import: set_prop didn't succeed"; no_tac th)
        end

val setup = Method.setup @{binding import}
  (Scan.lift (Args.name -- Args.name) >>
    (fn arg => fn ctxt => SIMPLE_METHOD (import_tac ctxt arg)))
  "import external theorem"

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

val _ =
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

