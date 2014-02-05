(*  Title:      Pure/Tools/simplifier_trace.ML
    Author:     Lars Hupel

Interactive Simplifier trace.
*)

signature SIMPLIFIER_TRACE =
sig
  val add_term_breakpoint: term -> Context.generic -> Context.generic
  val add_thm_breakpoint: thm -> Context.generic -> Context.generic
end

structure Simplifier_Trace: SIMPLIFIER_TRACE =
struct

(** background data **)

datatype mode = Disabled | Normal | Full

fun merge_modes Disabled m = m
  | merge_modes Normal Full = Full
  | merge_modes Normal _ = Normal
  | merge_modes Full _ = Full

val empty_breakpoints =
  (Item_Net.init (op =) single (* FIXME equality on terms? *),
   Item_Net.init eq_rrule (single o Thm.full_prop_of o #thm))

fun merge_breakpoints ((term_bs1, thm_bs1), (term_bs2, thm_bs2)) =
  (Item_Net.merge (term_bs1, term_bs2),
   Item_Net.merge (thm_bs1, thm_bs2))

structure Data = Generic_Data
(
  type T =
    {max_depth: int,
     depth: int,
     mode: mode,
     interactive: bool,
     parent: int,
     breakpoints: term Item_Net.T * rrule Item_Net.T}
  val empty =
    {max_depth = 10,
     depth = 0,
     mode = Disabled,
     interactive = false,
     parent = 0,
     breakpoints = empty_breakpoints}
  val extend = I
  fun merge ({max_depth = max_depth1, mode = mode1, interactive = interactive1,
              breakpoints = breakpoints1, ...}: T,
             {max_depth = max_depth2, mode = mode2, interactive = interactive2,
              breakpoints = breakpoints2, ...}: T) =
    {max_depth = Int.max (max_depth1, max_depth2),
     depth = 0,
     mode = merge_modes mode1 mode2,
     interactive = interactive1 orelse interactive2,
     parent = 0,
     breakpoints = merge_breakpoints (breakpoints1, breakpoints2)}: T
)

fun map_breakpoints f_term f_thm =
  Data.map (fn {max_depth, depth, mode, interactive, parent, breakpoints = (term_bs, thm_bs)} =>
    {max_depth = max_depth,
     depth = depth,
     mode = mode,
     interactive = interactive,
     parent = parent,
     breakpoints = (f_term term_bs, f_thm thm_bs)})

fun add_term_breakpoint term =
  map_breakpoints (Item_Net.update term) I

fun add_thm_breakpoint thm context =
  let
    val rrules = mk_rrules (Context.proof_of context) [thm]
  in
    map_breakpoints I (fold Item_Net.update rrules) context
  end

fun is_breakpoint (term, rrule) context =
  let
    val {breakpoints, ...} = Data.get context

    fun matches pattern = Pattern.matches (Context.theory_of context) (pattern, term)
    val term_matches = filter matches (Item_Net.retrieve_matching (fst breakpoints) term)

    val {thm = thm, ...} = rrule
    val thm_matches = exists (eq_rrule o pair rrule)
      (Item_Net.retrieve_matching (snd breakpoints) (Thm.full_prop_of thm))
  in
    (term_matches, thm_matches)
  end

(** config and attributes **)

fun config raw_mode interactive max_depth =
  let
    val mode = case raw_mode of
      "normal" => Normal
    | "full" => Full
    | _ => error ("Simplifier_Trace.config: unknown mode " ^ raw_mode)

    val update = Data.map (fn {depth, parent, breakpoints, ...} =>
      {max_depth = max_depth,
       depth = depth,
       mode = mode,
       interactive = interactive,
       parent = parent,
       breakpoints = breakpoints})
  in Thm.declaration_attribute (K update) end

fun term_breakpoint terms =
  Thm.declaration_attribute (K (fold add_term_breakpoint terms))

val thm_breakpoint =
  Thm.declaration_attribute add_thm_breakpoint

(** tracing state **)

val futures =
  Synchronized.var "Simplifier_Trace.futures" (Inttab.empty: string future Inttab.table)

(** markup **)

fun output_result (id, data) =
  Output.result (Markup.serial_properties id) data

val serialN = "serial"
val parentN = "parent"
val textN = "text"
val successN = "success"

val logN = "simp_trace_log"
val stepN = "simp_trace_step"
val recurseN = "simp_trace_recurse"
val hintN = "simp_trace_hint"
val ignoreN = "simp_trace_ignore"

val cancelN = "simp_trace_cancel"

type payload =
  {props: Properties.T,
   pretty: Pretty.T}

fun empty_payload () : payload =
  {props = [], pretty = Pretty.str ""}

fun mk_generic_result markup text triggered (payload : unit -> payload) ctxt =
  let
    val {max_depth, depth, mode, interactive, parent, ...} = Data.get (Context.Proof ctxt)

    val eligible =
      case mode of
        Disabled => false
      | Normal => triggered
      | Full => true

    val markup' = if markup = stepN andalso not interactive then logN else markup
  in
    if not eligible orelse depth > max_depth then
      NONE
    else
      let
        val {props = more_props, pretty} = payload ()
        val props =
          [(textN, text),
           (parentN, Markup.print_int parent)]
        val data =
          Pretty.string_of (Pretty.markup (markup', props @ more_props) [pretty])
      in
        SOME (serial (), data)
      end
  end

(** tracing output **)

fun send_request (result_id, content) =
  let
    fun break () =
      (Output.protocol_message
         [(Markup.functionN, cancelN),
          (serialN, Markup.print_int result_id)]
         "";
       Synchronized.change futures (Inttab.delete_safe result_id))
    val promise = Future.promise break : string future
  in
    Synchronized.change futures (Inttab.update_new (result_id, promise));
    output_result (result_id, content);
    promise
  end


type data = {term: term, thm: thm, unconditional: bool, ctxt: Proof.context, rrule: rrule}

fun step ({term, thm, unconditional, ctxt, rrule}: data) =
  let
    val (matching_terms, thm_triggered) = is_breakpoint (term, rrule) (Context.Proof ctxt)

    val {name, ...} = rrule
    val term_triggered = not (null matching_terms)

    val text =
      if unconditional then
        "Apply rewrite rule?"
      else
        "Apply conditional rewrite rule?"

    fun payload () =
      let
        (* FIXME pretty printing via Proof_Context.pretty_fact *)
        val pretty_thm = Pretty.block
          [Pretty.str ("Instance of " ^ name ^ ":"),
           Pretty.brk 1,
           Syntax.pretty_term ctxt (Thm.prop_of thm)]

        val pretty_term = Pretty.block
          [Pretty.str "Trying to rewrite:",
           Pretty.brk 1,
           Syntax.pretty_term ctxt term]

        val pretty_matchings =
          let
            val items = map (Pretty.item o single o Syntax.pretty_term ctxt) matching_terms
          in
            if not (null matching_terms) then
              [Pretty.block (Pretty.fbreaks (Pretty.str "Matching terms:" :: items))]
            else
              []
          end

        val pretty =
          Pretty.chunks ([pretty_thm, pretty_term] @ pretty_matchings)
      in
        {props = [], pretty = pretty}
      end

    val {max_depth, depth, mode, interactive, breakpoints, ...} =
      Data.get (Context.Proof ctxt)

    fun mk_promise result =
      let
        val result_id = #1 result

        fun put mode' interactive' = Data.put
          {max_depth = max_depth,
           depth = depth,
           mode = mode',
           interactive = interactive',
           parent = result_id,
           breakpoints = breakpoints} (Context.Proof ctxt) |>
          Context.the_proof

        fun to_response "skip" = NONE
          | to_response "continue" = SOME (put mode true)
          | to_response "continue_trace" = SOME (put Full true)
          | to_response "continue_passive" = SOME (put mode false)
          | to_response "continue_disable" = SOME (put Disabled false)
          | to_response _ = raise Fail "Simplifier_Trace.step: invalid message"
      in
        if not interactive then
          (output_result result; Future.value (SOME (put mode false)))
        else
          Future.map to_response (send_request result)
      end

  in
    case mk_generic_result stepN text (thm_triggered orelse term_triggered) payload ctxt of
      NONE => Future.value (SOME ctxt)
    | SOME res => mk_promise res
  end

fun recurse text term ctxt =
  let
    fun payload () =
      {props = [],
       pretty = Syntax.pretty_term ctxt term}

    val {max_depth, depth, mode, interactive, breakpoints, ...} = Data.get (Context.Proof ctxt)

    fun put result_id = Data.put
      {max_depth = max_depth,
       depth = depth + 1,
       mode = if depth >= max_depth then Disabled else mode,
       interactive = interactive,
       parent = result_id,
       breakpoints = breakpoints} (Context.Proof ctxt)

    val context' =
      case mk_generic_result recurseN text true payload ctxt of
        NONE =>
          put 0
      | SOME res =>
          (output_result res; put (#1 res))
  in Context.the_proof context' end

fun indicate_failure ({term, ctxt, thm, rrule, ...}: data) ctxt' =
  let
    fun payload () =
      let
        val {name, ...} = rrule
        val pretty_thm =
          (* FIXME pretty printing via Proof_Context.pretty_fact *)
          Pretty.block
            [Pretty.str ("In an instance of " ^ name ^ ":"),
             Pretty.brk 1,
             Syntax.pretty_term ctxt (Thm.prop_of thm)]

        val pretty_term =
          Pretty.block
            [Pretty.str "Was trying to rewrite:",
             Pretty.brk 1,
             Syntax.pretty_term ctxt term]

        val pretty =
          Pretty.chunks [pretty_thm, pretty_term]
      in
        {props = [(successN, "false")], pretty = pretty}
      end

    val {interactive, ...} = Data.get (Context.Proof ctxt)
    val {parent, ...} = Data.get (Context.Proof ctxt')

    fun mk_promise result =
      let
        val result_id = #1 result

        fun to_response "exit" =
              false
          | to_response "redo" =
              (Option.app output_result
                (mk_generic_result ignoreN "Ignore" true empty_payload ctxt');
               true)
          | to_response _ =
              raise Fail "Simplifier_Trace.indicate_failure: invalid message"
      in
        if not interactive then
          (output_result result; Future.value false)
        else
          Future.map to_response (send_request result)
      end
  in
    case mk_generic_result hintN "Step failed" true payload ctxt' of
      NONE => Future.value false
    | SOME res => mk_promise res
  end

fun indicate_success thm ctxt =
  let
    fun payload () =
      {props = [(successN, "true")],
       pretty = Syntax.pretty_term ctxt (Thm.prop_of thm)}
  in
    Option.app output_result (mk_generic_result hintN "Successfully rewrote" true payload ctxt)
  end

(** setup **)

fun simp_if_continue args ctxt cont =
  let
    val {unconditional: bool, term: term, thm: thm, rrule: rrule} = args
    val data =
      {term = term,
       unconditional = unconditional,
       ctxt = ctxt,
       thm = thm,
       rrule = rrule}
  in
    case Future.join (step data) of
      NONE =>
        NONE
    | SOME ctxt' =>
        let val res = cont ctxt' in
          case res of
            NONE =>
              if Future.join (indicate_failure data ctxt') then
                simp_if_continue args ctxt cont
              else
                NONE
          | SOME (thm, _) =>
              (indicate_success thm ctxt';
               res)
        end
  end

val _ = Session.protocol_handler "isabelle.Simplifier_Trace$Handler"

val _ = Theory.setup
  (Simplifier.set_trace_ops
    {trace_invoke = fn {depth, term} => recurse "Simplifier invoked" term,
     trace_apply = simp_if_continue})

val _ =
  Isabelle_Process.protocol_command "Document.simp_trace_reply"
    (fn [s, r] =>
      let
        val serial = Markup.parse_int s
        fun lookup_delete tab =
          (Inttab.lookup tab serial, Inttab.delete_safe serial tab)
        fun apply_result (SOME promise) = Future.fulfill promise r
          | apply_result NONE = () (* FIXME handle protocol failure, just like in active.ML? *)
      in
        (Synchronized.change_result futures lookup_delete |> apply_result)
          handle exn => if Exn.is_interrupt exn then () (*sic!*) else reraise exn
      end)

(** attributes **)

val pat_parser =
  Args.context -- Scan.lift Args.name_inner_syntax >> uncurry Proof_Context.read_term_schematic

val mode_parser: string parser =
  Scan.optional
    (Args.$$$ "mode" |-- Args.$$$ "=" |-- (Args.$$$ "normal" || Args.$$$ "full"))
    "normal"

val interactive_parser: bool parser =
  Scan.optional (Args.$$$ "interactive" >> K true) false

val depth_parser =
  Scan.optional (Args.$$$ "depth" |-- Args.$$$ "=" |-- Parse.nat) 10

val config_parser =
  (interactive_parser -- mode_parser -- depth_parser) >>
    (fn ((interactive, mode), depth) => config mode interactive depth)

val _ = Theory.setup
  (Attrib.setup @{binding break_term}
    ((Scan.repeat1 pat_parser) >> term_breakpoint)
    "declaration of a term breakpoint" #>
   Attrib.setup @{binding break_thm}
    (Scan.succeed thm_breakpoint)
    "declaration of a theorem breakpoint" #>
   Attrib.setup @{binding simplifier_trace} (Scan.lift config_parser)
    "simplifier trace configuration")

end
