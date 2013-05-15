(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_preplay.ML
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
  val try_metis : bool -> bool -> string -> string -> Proof.context ->
    Time.time -> isar_step -> unit -> preplay_time
  val try_metis_quietly : bool -> bool -> string -> string -> Proof.context ->
    Time.time -> isar_step -> unit -> preplay_time
end

structure Sledgehammer_Preplay : SLEDGEHAMMER_PREPLAY =
struct

open Sledgehammer_Util
open Sledgehammer_Proof

(* The boolean flag encodes whether the time is exact (false) or an lower bound
   (true):
      (t, false) = "t ms"
      (t, true)  = "> t ms" *)
type preplay_time = bool * Time.time

val zero_preplay_time = (false, Time.zeroTime) (* 0 ms *)
val some_preplay_time = (true, Time.zeroTime)  (* > 0 ms *)

fun add_preplay_time (b1, t1) (b2, t2) = (b1 orelse b2, Time.+(t1,t2))

val string_of_preplay_time = ATP_Util.string_from_ext_time

(* preplay tracing *)
fun preplay_trace ctxt assms concl time =
  let
    val ctxt = ctxt |> Config.put show_markup true
    val time = "[" ^ (string_of_preplay_time time) ^ "]" |> Pretty.str
    val nr_of_assms = length assms
    val assms = assms |> map (Display.pretty_thm ctxt)
                      |> (fn [] => Pretty.str ""
                           | [a] => a
                           | assms => Pretty.enum ";" "⟦" "⟧" assms)
    val concl = concl |> Syntax.pretty_term ctxt
    val trace_list = [] |> cons concl
                        |> nr_of_assms>0 ? cons (Pretty.str "⟹")
                        |> cons assms
                        |> cons time
    val pretty_trace = Pretty.blk(2, Pretty.breaks trace_list)
  in tracing (Pretty.string_of pretty_trace) end

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
  (names
    |>> map string_of_label
    |> op @
    |> maps (thms_of_name ctxt))
  handle ERROR msg => error ("preplay error: " ^ msg)

(* turn terms/proofs into theorems *)
fun thm_of_term ctxt = Skip_Proof.make_thm (Proof_Context.theory_of ctxt)
fun thm_of_proof ctxt (Proof (Fix fixed_frees, Assume assms, steps)) =
  let
    val concl = (case try List.last steps of
                  SOME (Prove (_, _, t, _)) => t
                | _ => raise Fail "preplay error: malformed subproof")
    val var_idx = maxidx_of_term concl + 1
    fun var_of_free (x, T) = Var((x, var_idx), T)
    val substitutions =
      map (`var_of_free #> swap #> apfst Free) fixed_frees
  in
    Logic.list_implies (assms |> map snd, concl)
      |> subst_free substitutions
      |> thm_of_term ctxt
  end

exception ZEROTIME
fun try_metis debug trace type_enc lam_trans ctxt timeout step =
  let
    val (prop, subproofs, fact_names, obtain) =
      (case step of
        Prove (_, _, t, By_Metis (subproofs, fact_names)) =>
            (t, subproofs, fact_names, false)
      | Obtain (_, Fix xs, _, t, By_Metis (subproofs, fact_names)) =>
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
          (prop, subproofs, fact_names, true)
        end
      | _ => raise ZEROTIME)
    val facts =
      map (thm_of_proof ctxt) subproofs @ resolve_fact_names ctxt fact_names
    val ctxt = ctxt |> Config.put Metis_Tactic.verbose debug
                    |> obtain ? Config.put Metis_Tactic.new_skolem true
    val goal =
      Goal.prove (Config.put Metis_Tactic.verbose debug ctxt) [] [] prop
    fun tac {context = ctxt, prems = _} =
      Metis_Tactic.metis_tac [type_enc] lam_trans ctxt facts 1
    fun run_tac () = goal tac
      handle ERROR msg => error ("preplay error: " ^ msg)
  in
    fn () =>
      let
        val preplay_time = take_time timeout run_tac ()
        (* tracing *)
        val _ = if trace then preplay_trace ctxt facts prop preplay_time else ()
      in
        preplay_time
      end
  end
  handle ZEROTIME => K zero_preplay_time

(* this version treats exceptions like timeouts *)
fun try_metis_quietly debug trace type_enc lam_trans ctxt timeout =
  the_default (true, timeout) oo try
  o try_metis debug trace type_enc lam_trans ctxt timeout

end
