(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_shrink.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Author:     Steffen Juilf Smolka, TU Muenchen

Preplaying of reconstructed isar proofs.
*)

signature SLEDGEHAMMER_PREPLAY =
sig
  type isar_step = Sledgehammer_Proof.isar_step
  val try_metis : bool -> string -> string -> Proof.context ->
    Time.time -> (isar_step option * isar_step) -> unit -> Time.time option
  val try_metis_quietly : bool -> string -> string -> Proof.context ->
    Time.time -> (isar_step option * isar_step) -> unit -> Time.time option
end

structure Sledgehammer_Preplay : SLEDGEHAMMER_PREPLAY =
struct

open Sledgehammer_Util
open Sledgehammer_Proof

(* timing *)
fun take_time timeout tac arg =
  let
    val timing = Timing.start ()
  in
    (TimeLimit.timeLimit timeout tac arg; Timing.result timing |> #cpu |> SOME)
    handle TimeLimit.TimeOut => NONE
  end

(* lookup facts in context *)
fun resolve_fact_names ctxt names =
  names
    |>> map string_for_label
    |> op @
    |> maps (thms_of_name ctxt)

exception ZEROTIME
fun try_metis debug type_enc lam_trans ctxt timeout (succedent, step) =
  let
    val (t, byline, obtain) =
      (case step of
        Prove (_, _, t, byline) => (t, byline, false)
      | Obtain (_, xs, _, t, byline) =>
        (* proof obligation: !!thesis. (!!x. A x ==> thesis) ==> thesis
           (see ~~/src/Pure/Isar/obtain.ML) *)
        let
          val thesis = Term.Free ("thesis", HOLogic.boolT)
          val thesis_prop = thesis |> HOLogic.mk_Trueprop
          val frees = map Term.Free xs

          (* !!x1..xn. t ==> thesis (xs = [x1, .., xn]) *)
          val inner_prop =
            fold_rev Logic.all frees (Logic.mk_implies (t, thesis_prop))

          (* !!thesis. (!!x1..xn. t ==> thesis) ==> thesis *)
          val prop =
            Logic.all thesis (Logic.mk_implies (inner_prop, thesis_prop))
        in
          (prop, byline, true)
        end
      | _ => raise ZEROTIME)
    val make_thm = Skip_Proof.make_thm (Proof_Context.theory_of ctxt)
    val facts =
      (case byline of
        By_Metis fact_names => resolve_fact_names ctxt fact_names
      | Case_Split (cases, fact_names) =>
        resolve_fact_names ctxt fact_names
          @ (case the succedent of
              Assume (_, t) => make_thm t
            | Obtain (_, _, _, t, _) => make_thm t
            | Prove (_, _, t, _) => make_thm t
            | _ => error "Preplay error: unexpected succedent of case split")
          :: map (hd #> (fn Assume (_, a) => Logic.mk_implies (a, t)
                          | _ => error "Preplay error: malformed case split")
                     #> make_thm)
               cases)
    val ctxt = ctxt |> Config.put Metis_Tactic.verbose debug
                    |> obtain ? Config.put Metis_Tactic.new_skolem true
    val goal =
      Goal.prove (Config.put Metis_Tactic.verbose debug ctxt) [] [] t
    fun tac {context = ctxt, prems = _} =
      Metis_Tactic.metis_tac [type_enc] lam_trans ctxt facts 1
  in
    take_time timeout (fn () => goal tac)
  end
  handle ZEROTIME => K (SOME Time.zeroTime)

(* this version does not throw exceptions but returns NONE instead *)
fun try_metis_quietly debug type_enc lam_trans ctxt =
   the_default NONE oo try oo try_metis debug type_enc lam_trans ctxt

end
