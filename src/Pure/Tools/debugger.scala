/*  Title:      Pure/Tools/debugger.scala
    Author:     Makarius

Interactive debugger for Isabelle/ML.
*/

package isabelle


import scala.collection.immutable.SortedMap


object Debugger
{
  /* thread context */

  case object Update

  sealed case class Debug_State(pos: Position.T, function: String)
  type Threads = SortedMap[String, List[Debug_State]]

  sealed case class Context(thread_name: String, debug_states: List[Debug_State], index: Int = 0)
  {
    def size: Int = debug_states.length + 1
    def reset: Context = copy(index = 0)
    def select(i: Int) = copy(index = i + 1)

    def thread_state: Option[Debug_State] = debug_states.headOption

    def stack_state: Option[Debug_State] =
      if (1 <= index && index <= debug_states.length)
        Some(debug_states(index - 1))
      else None

    def debug_index: Option[Int] =
      if (stack_state.isDefined) Some(index - 1)
      else if (debug_states.nonEmpty) Some(0)
      else None

    def debug_state: Option[Debug_State] = stack_state orElse thread_state
    def debug_position: Option[Position.T] = debug_state.map(_.pos)

    override def toString: String =
      stack_state match {
        case None => thread_name
        case Some(d) => d.function
      }
  }


  /* debugger state */

  sealed case class State(
    session: Session,
    active: Int = 0,  // active views
    break: Boolean = false,  // break at next possible breakpoint
    active_breakpoints: Set[Long] = Set.empty,  // explicit breakpoint state
    threads: Threads = SortedMap.empty,  // thread name ~> stack of debug states
    focus: Map[String, Context] = Map.empty,  // thread name ~> focus
    output: Map[String, Command.Results] = Map.empty)  // thread name ~> output messages
  {
    def set_break(b: Boolean): State = copy(break = b)

    def is_active: Boolean = active > 0 && session.is_ready
    def inc_active: State = copy(active = active + 1)
    def dec_active: State = copy(active = active - 1)

    def toggle_breakpoint(breakpoint: Long): (Boolean, State) =
    {
      val active_breakpoints1 =
        if (active_breakpoints(breakpoint)) active_breakpoints - breakpoint
      else active_breakpoints + breakpoint
      (active_breakpoints1(breakpoint), copy(active_breakpoints = active_breakpoints1))
    }

    def get_thread(thread_name: String): List[Debug_State] =
      threads.getOrElse(thread_name, Nil)

    def update_thread(thread_name: String, debug_states: List[Debug_State]): State =
    {
      val threads1 =
        if (debug_states.nonEmpty) threads + (thread_name -> debug_states)
        else threads - thread_name
      val focus1 =
        focus.get(thread_name) match {
          case Some(c) if debug_states.nonEmpty =>
            focus + (thread_name -> Context(thread_name, debug_states))
          case _ => focus - thread_name
        }
      copy(threads = threads1, focus = focus1)
    }

    def set_focus(c: Context): State = copy(focus = focus + (c.thread_name -> c))

    def get_output(thread_name: String): Command.Results =
      output.getOrElse(thread_name, Command.Results.empty)

    def add_output(thread_name: String, entry: Command.Results.Entry): State =
      copy(output = output + (thread_name -> (get_output(thread_name) + entry)))

    def clear_output(thread_name: String): State =
      copy(output = output - thread_name)
  }


  /* protocol handler */

  def get(session: Session): Option[Debugger] =
    session.get_protocol_handler("isabelle.Debugger$Handler") match {
      case Some(handler: Handler) => handler.get_debugger
      case _ => None
    }

  def apply(session: Session): Debugger =
    get(session) getOrElse error("Debugger not initialized")

  class Handler extends Session.Protocol_Handler
  {
    private val _debugger_ = Synchronized[Option[Debugger]](None)
    def get_debugger: Option[Debugger] = _debugger_.value
    def the_debugger: Debugger = get_debugger getOrElse error("Debugger not initialized")

    override def start(session: Session, prover: Prover)
    {
      _debugger_.change(
        {
          case None => Some(new Debugger(session))
          case Some(_) => error("Debugger already initialized")
        })
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
          the_debugger.update_thread(thread_name, debug_states)
          true
        case _ => false
      }
    }

    private def debugger_output(prover: Prover, msg: Prover.Protocol_Output): Boolean =
    {
      msg.properties match {
        case Markup.Debugger_Output(thread_name) =>
          YXML.parse_body_failsafe(Symbol.decode(UTF8.decode_permissive(msg.bytes))) match {
            case List(XML.Elem(Markup(name, props @ Markup.Serial(i)), body)) =>
              val message =
                prover.xml_cache.elem(XML.Elem(Markup(Markup.message(name), props), body))
              the_debugger.add_output(thread_name, i -> message)
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
}

class Debugger private(session: Session)
{
  /* debugger state */

  private val state = Synchronized(Debugger.State(session))

  private val delay_update =
    Standard_Thread.delay_first(session.output_delay) {
      session.debugger_updates.post(Debugger.Update)
    }


  /* protocol commands */

  def update_thread(thread_name: String, debug_states: List[Debugger.Debug_State])
  {
    state.change(_.update_thread(thread_name, debug_states))
    delay_update.invoke()
  }

  def add_output(thread_name: String, entry: Command.Results.Entry)
  {
    state.change(_.add_output(thread_name, entry))
    delay_update.invoke()
  }

  def is_active(): Boolean = state.value.is_active

  def init(): Unit =
    state.change(st =>
    {
      val st1 = st.inc_active
      if (!st.is_active && st1.is_active)
        session.protocol_command("Debugger.init")
      st1
    })

  def exit(): Unit =
    state.change(st =>
    {
      val st1 = st.dec_active
      if (st.is_active && !st1.is_active)
        session.protocol_command("Debugger.exit")
      st1
    })

  def is_break(): Boolean = state.value.break
  def set_break(b: Boolean)
  {
    state.change(st => {
      val st1 = st.set_break(b)
      session.protocol_command("Debugger.break", b.toString)
      st1
    })
    delay_update.invoke()
  }

  def active_breakpoint_state(breakpoint: Long): Option[Boolean] =
  {
    val st = state.value
    if (st.is_active) Some(st.active_breakpoints(breakpoint)) else None
  }

  def breakpoint_state(breakpoint: Long): Boolean =
    state.value.active_breakpoints(breakpoint)

  def toggle_breakpoint(command: Command, breakpoint: Long)
  {
    state.change(st =>
      {
        val (breakpoint_state, st1) = st.toggle_breakpoint(breakpoint)
        session.protocol_command(
          "Debugger.breakpoint",
          Symbol.encode(command.node_name.node),
          Document_ID(command.id),
          Value.Long(breakpoint),
          Value.Boolean(breakpoint_state))
        st1
      })
  }

  def status(focus: Option[Debugger.Context]): (Debugger.Threads, List[XML.Tree]) =
  {
    val st = state.value
    val output =
      focus match {
        case None => Nil
        case Some(c) =>
          (for {
            (thread_name, results) <- st.output
            if thread_name == c.thread_name
            (_, tree) <- results.iterator
          } yield tree).toList
      }
    (st.threads, output)
  }

  def focus(): List[Debugger.Context] = state.value.focus.toList.map(_._2)
  def set_focus(c: Debugger.Context)
  {
    state.change(_.set_focus(c))
    delay_update.invoke()
  }

  def input(thread_name: String, msg: String*): Unit =
    session.protocol_command("Debugger.input", (thread_name :: msg.toList):_*)

  def continue(thread_name: String): Unit = input(thread_name, "continue")
  def step(thread_name: String): Unit = input(thread_name, "step")
  def step_over(thread_name: String): Unit = input(thread_name, "step_over")
  def step_out(thread_name: String): Unit = input(thread_name, "step_out")

  def clear_output(thread_name: String)
  {
    state.change(_.clear_output(thread_name))
    delay_update.invoke()
  }

  def eval(c: Debugger.Context, SML: Boolean, context: String, expression: String)
  {
    state.change(st => {
      input(c.thread_name, "eval", c.debug_index.getOrElse(0).toString,
        SML.toString, Symbol.encode(context), Symbol.encode(expression))
      st.clear_output(c.thread_name)
    })
    delay_update.invoke()
  }

  def print_vals(c: Debugger.Context, SML: Boolean, context: String)
  {
    require(c.debug_index.isDefined)

    state.change(st => {
      input(c.thread_name, "print_vals", c.debug_index.getOrElse(0).toString,
        SML.toString, Symbol.encode(context))
      st.clear_output(c.thread_name)
    })
    delay_update.invoke()
  }
}
