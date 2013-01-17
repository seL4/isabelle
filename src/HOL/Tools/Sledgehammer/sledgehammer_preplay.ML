(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_shrink.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Author:     Steffen Juilf Smolka, TU Muenchen

Preplaying of isar proofs.
*)

signature SLEDGEHAMMER_PREPLAY =
sig
  type isar_step = Sledgehammer_Proof.isar_step
  eqtype preplay_time
  val zero_preplay_time : preplay_time
  val some_preplay_time : preplay_time
  val add_preplay_time : preplay_time -> preplay_time -> preplay_time
  val string_of_preplay_time : preplay_time -> string
  val try_metis : bool -> string -> string -> Proof.context ->
    Time.time -> (isar_step option * isar_step) -> unit -> preplay_time
  val try_metis_quietly : bool -> string -> string -> Proof.context ->
    Time.time -> (isar_step option * isar_step) -> unit -> preplay_time
end

structure Sledgehammer_Preplay : SLEDGEHAMMER_PREPLAY =
struct

open Sledgehammer_Util
open Sledgehammer_Proof

(* The boolean flag encodes whether the time is exact (false) or an lower bound
     (true) *)
type preplay_time = bool * Time.time

val zero_preplay_time = (false, Time.zeroTime)
val some_preplay_time = (true, Time.zeroTime)

fun add_preplay_time (b1, t1) (b2, t2) = (b1 orelse b2, Time.+(t1,t2))

val string_of_preplay_time = ATP_Util.string_from_ext_time

(* timing *)
fun take_time timeout tac arg =
  let
    val timing = Timing.start ()
  in
    (TimeLimit.timeLimit timeout tac arg;
      Timing.result timing |> #cpu |> pair false)
    handle TimeLimit.TimeOut => (true, timeout)
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
            | _ => error "preplay error: unexpected succedent of case split")
          :: map (hd #> (fn Assume (_, a) => Logic.mk_implies (a, t)
                          | _ => error "preplay error: malformed case split")
                     #> make_thm)
               cases)
    val ctxt = ctxt |> Config.put Metis_Tactic.verbose debug
                    |> obtain ? Config.put Metis_Tactic.new_skolem true
    val goal =
      Goal.prove (Config.put Metis_Tactic.verbose debug ctxt) [] [] t
    fun tac {context = ctxt, prems = _} =
      Metis_Tactic.metis_tac [type_enc] lam_trans ctxt facts 1
  in
    take_time timeout
      (fn () => goal tac handle ERROR msg => error ("preplay error: " ^ msg))
  end
  handle ZEROTIME => K zero_preplay_time

(* this version treats exceptions like timeouts *)
fun try_metis_quietly debug type_enc lam_trans ctxt timeout =
   the_default (true, timeout) oo try o try_metis debug type_enc lam_trans ctxt timeout

end
