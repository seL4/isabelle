(*  Title:      HOL/Tools/Datatype/datatype_selectors.ML
    Author:     Sascha Boehme, TU Muenchen

Selector functions for datatype constructor arguments.
*)

signature DATATYPE_SELECTORS =
sig
  val add_selector: ((string * typ) * int) * (string * typ) ->
    Context.generic -> Context.generic
  val lookup_selector: Proof.context -> string * int -> string option
  val setup: theory -> theory
end

structure Datatype_Selectors: DATATYPE_SELECTORS =
struct

structure Stringinttab = Table
(
  type key = string * int
  val ord = prod_ord fast_string_ord int_ord
)

structure Data = Generic_Data
(
  type T = string Stringinttab.table
  val empty = Stringinttab.empty
  val extend = I
  val merge = Stringinttab.merge (K true)
)

fun pretty_term context = Syntax.pretty_term (Context.proof_of context)

fun sanity_check context (((con as (n, _), i), sel as (m, _))) =
  let
    val thy = Context.theory_of context
    val varify_const =
      Const #> Type.varify_global [] #> snd #> Term.dest_Const #>
      snd #> Term.strip_type

    val (Ts, T) = varify_const con
    val (Us, U) = varify_const sel
    val _ = (0 < i andalso i <= length Ts) orelse
      error (Pretty.string_of (Pretty.block [
        Pretty.str "The constructor ",
        Pretty.quote (pretty_term context (Const con)),
        Pretty.str " has no argument position ",
        Pretty.str (string_of_int i),
        Pretty.str "."]))
    val _ = length Us = 1 orelse
      error (Pretty.string_of (Pretty.block [
        Pretty.str "The term ", Pretty.quote (pretty_term context (Const sel)),
        Pretty.str " might not be a selector ",
        Pretty.str "(it accepts more than one argument)."]))
    val _ =
     (Sign.typ_equiv thy (T, hd Us) andalso
      Sign.typ_equiv thy (nth Ts (i-1), U)) orelse
      error (Pretty.string_of (Pretty.block [
        Pretty.str "The types of the constructor ",
        Pretty.quote (pretty_term context (Const con)),
        Pretty.str " and of the selector ",
        Pretty.quote (pretty_term context (Const sel)),
        Pretty.str " do not fit to each other."]))
  in ((n, i), m) end

fun add_selector (entry as ((con as (n, _), i), (_, T))) context =
  (case Stringinttab.lookup (Data.get context) (n, i) of
    NONE => Data.map (Stringinttab.update (sanity_check context entry)) context
  | SOME c => error (Pretty.string_of (Pretty.block [
      Pretty.str "There is already a selector assigned to constructor ",
      Pretty.quote (pretty_term context (Const con)), Pretty.str ", namely ",
      Pretty.quote (pretty_term context (Const (c, T))), Pretty.str "."])))

fun lookup_selector ctxt = Stringinttab.lookup (Data.get (Context.Proof ctxt))

val setup =
  Attrib.setup @{binding selector}
   ((Args.term >> Term.dest_Const) -- Scan.lift (Parse.nat) --|
    Scan.lift (Parse.$$$ "=") -- (Args.term >> Term.dest_Const) >>
    (Thm.declaration_attribute o K o add_selector))
  "assign a selector function to a datatype constructor argument"

end
