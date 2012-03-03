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

end

