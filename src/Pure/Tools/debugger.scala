/*  Title:      Pure/Tools/debugger.scala
    Author:     Makarius

Interactive debugger for Isabelle/ML.
*/

package isabelle


object Debugger
{
  /* global state */

  sealed case class Debug_State(
    pos: Position.T,
    function: String)

  sealed case class State(
    session: Session = new Session(Resources.empty),
    active: Int = 0,
    active_breakpoints: Set[Long] = Set.empty,
    focus: Option[Position.T] = None,  // position of active GUI component
    threads: Map[String, List[Debug_State]] = Map.empty,  // thread name ~> stack of debug states
    output: Map[String, Command.Results] = Map.empty)  // thread name ~> output messages
  {
    def set_session(new_session: Session): State =
      copy(session = new_session)

    def is_active: Boolean = active > 0
    def inc_active: State = copy(active = active + 1)
    def dec_active: State = copy(active = active - 1)

    def toggle_breakpoint(breakpoint: Long): (Boolean, State) =
    {
      val active_breakpoints1 =
        if (active_breakpoints(breakpoint)) active_breakpoints - breakpoint
      else active_breakpoints + breakpoint
      (active_breakpoints1(breakpoint), copy(active_breakpoints = active_breakpoints1))
    }

    def set_focus(new_focus: Option[Position.T]): State =
      copy(focus = new_focus)

    def get_thread(thread_name: String): List[Debug_State] =
      threads.getOrElse(thread_name, Nil)

    def update_thread(thread_name: String, debug_states: List[Debug_State]): State =
      copy(threads = threads + (thread_name -> debug_states))

    def get_output(thread_name: String): Command.Results =
      output.getOrElse(thread_name, Command.Results.empty)

    def add_output(thread_name: String, entry: Command.Results.Entry): State =
      copy(output = output + (thread_name -> (get_output(thread_name) + entry)))

    def clear_output(thread_name: String): State =
      copy(output = output - thread_name)

    def purge(thread_name: String): State =
      if (get_thread(thread_name).isEmpty)
        copy(threads = threads - thread_name, output = output - thread_name)
      else this
  }

  private val global_state = Synchronized(State())


  /* protocol handler */

  sealed case class Update(thread_names: Set[String])

  class Handler extends Session.Protocol_Handler
  {
    private var updated = Set.empty[String]
    private val delay_update =
      Simple_Thread.delay_first(global_state.value.session.output_delay) {
        global_state.value.session.debugger_updates.post(Update(updated))
        updated = Set.empty
      }
    private def update(name: String)
    {
      updated += name
      delay_update.invoke()
    }

    private def debugger_state(prover: Prover, msg: Prover.Protocol_Output): Boolean =
    {
      msg.properties match {
        case Markup.Debugger_State(thread_name) =>
          val msg_body =
            YXML.parse_body_failsafe(Symbol.decode(UTF8.decode_permissive(msg.bytes)))
          val debug_states =
          {
            import XML.Decode._
            list(pair(properties, Symbol.decode_string))(msg_body).map({
              case (pos, function) => Debug_State(pos, function)
            })
          }
          global_state.change(_.update_thread(thread_name, debug_states))
          update(thread_name)
          true
        case _ => false
      }
    }

    private def debugger_output(prover: Prover, msg: Prover.Protocol_Output): Boolean =
    {
      msg.properties match {
        case Markup.Debugger_Output(thread_name) =>
          val msg_body =
            prover.xml_cache.body(
              YXML.parse_body_failsafe(Symbol.decode(UTF8.decode_permissive(msg.bytes))))
          msg_body match {
            case List(XML.Elem(Markup(name, props @ Markup.Serial(i)), body)) =>
              val message = XML.Elem(Markup(Markup.message(name), props), body)
              global_state.change(_.add_output(thread_name, i -> message))
              update(thread_name)
              true
            case _ => false
          }
        case _ => false
      }
    }

    val functions =
      Map(
        Markup.DEBUGGER_STATE -> debugger_state _,
        Markup.DEBUGGER_OUTPUT -> debugger_output _)
  }


  /* protocol commands */

  def set_session(session: Session): Unit =
    global_state.change(_.set_session(session))

  def is_active(): Boolean = global_state.value.is_active

  def inc_active(): Unit =
    global_state.change(state =>
    {
      val state1 = state.inc_active
      if (!state.is_active && state1.is_active)
        state1.session.protocol_command("Debugger.init")
      state1
    })

  def dec_active(): Unit =
    global_state.change(state =>
    {
      val state1 = state.dec_active
      if (state.is_active && !state1.is_active)
        state1.session.protocol_command("Debugger.exit")
      state1
    })

  def active_breakpoint_state(breakpoint: Long): Option[Boolean] =
  {
    val state = global_state.value
    if (state.active > 0) Some(state.active_breakpoints(breakpoint)) else None
  }

  def breakpoint_state(breakpoint: Long): Boolean =
    global_state.value.active_breakpoints(breakpoint)

  def toggle_breakpoint(command: Command, breakpoint: Long)
  {
    global_state.change(state =>
    {
      val (breakpoint_state, state1) = state.toggle_breakpoint(breakpoint)
      state1.session.protocol_command(
        "Debugger.breakpoint",
        Symbol.encode(command.node_name.node),
        Document_ID(command.id),
        Properties.Value.Long(breakpoint),
        Properties.Value.Boolean(breakpoint_state))
      state1
    })
  }

  def focus(new_focus: Option[Position.T]): Boolean =
    global_state.change_result(state => (state.focus != new_focus, state.set_focus(new_focus)))

  def threads(): Map[String, List[Debug_State]] = global_state.value.threads

  def output(): Map[String, Command.Results] = global_state.value.output

  def input(thread_name: String, msg: String*): Unit =
    global_state.value.session.protocol_command("Debugger.input", (thread_name :: msg.toList):_*)

  def step(thread_name: String): Unit = input(thread_name, "step")
  def step_over(thread_name: String): Unit = input(thread_name, "step_over")
  def step_out(thread_name: String): Unit = input(thread_name, "step_out")
  def continue(thread_name: String): Unit = input(thread_name, "continue")

  def eval(thread_name: String, index: Int, SML: Boolean, context: String, expression: String)
  {
    global_state.change(state => {
      input(thread_name, "eval",
        index.toString, SML.toString, Symbol.encode(context), Symbol.encode(expression))
      state.clear_output(thread_name)
    })
  }

  def print_vals(thread_name: String, index: Int, SML: Boolean, context: String)
  {
    global_state.change(state => {
      input(thread_name, "print_vals", index.toString, SML.toString, Symbol.encode(context))
      state.clear_output(thread_name)
    })
  }
}
