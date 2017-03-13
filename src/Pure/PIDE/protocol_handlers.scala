/*  Title:      Pure/PIDE/protocol_handlers.scala
    Author:     Makarius

Management of add-on protocol handlers for PIDE session.
*/

package isabelle


object Protocol_Handlers
{
  private def bad_handler(exn: Throwable, name: String): Unit =
    Output.error_message(
      "Failed to initialize protocol handler: " + quote(name) + "\n" + Exn.message(exn))

  sealed case class State(
    session: Session,
    handlers: Map[String, Session.Protocol_Handler] = Map.empty,
    functions: Map[String, Prover.Protocol_Output => Boolean] = Map.empty)
  {
    def get(name: String): Option[Session.Protocol_Handler] = handlers.get(name)

    def add(prover: Prover, handler: Session.Protocol_Handler): State =
    {
      val name = handler.getClass.getName

      val (handlers1, functions1) =
        handlers.get(name) match {
          case Some(old_handler) =>
            Output.warning("Redefining protocol handler: " + name)
            old_handler.stop(prover)
            (handlers - name, functions -- old_handler.functions.keys)
          case None => (handlers, functions)
        }

      val (handlers2, functions2) =
        try {
          handler.start(session, prover)

          val new_functions =
            for ((a, f) <- handler.functions.toList) yield
              (a, (msg: Prover.Protocol_Output) => f(prover, msg))

          val dups = for ((a, _) <- new_functions if functions1.isDefinedAt(a)) yield a
          if (dups.nonEmpty) error("Duplicate protocol functions: " + commas_quote(dups))

          (handlers1 + (name -> handler), functions1 ++ new_functions)
        }
        catch {
          case exn: Throwable => bad_handler(exn, name); (handlers1, functions1)
        }
      copy(handlers = handlers2, functions = functions2)
    }

    def add(prover: Prover, name: String): State =
    {
      val new_handler =
        try { Some(Class.forName(name).newInstance.asInstanceOf[Session.Protocol_Handler]) }
        catch { case exn: Throwable => bad_handler(exn, name); None }
      new_handler match {
        case Some(handler) => add(prover, handler)
        case None => this
      }
    }

    def invoke(msg: Prover.Protocol_Output): Boolean =
      msg.properties match {
        case Markup.Function(a) if functions.isDefinedAt(a) =>
          try { functions(a)(msg) }
          catch {
            case exn: Throwable =>
              Output.error_message(
                "Failed invocation of protocol function: " + quote(a) + "\n" + Exn.message(exn))
            false
          }
        case _ => false
      }

    def stop(prover: Prover): State =
    {
      for ((_, handler) <- handlers) handler.stop(prover)
      copy(handlers = Map.empty, functions = Map.empty)
    }
  }

  def init(session: Session): Protocol_Handlers =
    new Protocol_Handlers(session)
}

class Protocol_Handlers private(session: Session)
{
  private val state = Synchronized(Protocol_Handlers.State(session))

  def get(name: String): Option[Session.Protocol_Handler] =
    state.value.get(name)

  def add(prover: Prover, handler: Session.Protocol_Handler): Unit =
    state.change(_.add(prover, handler))

  def add(prover: Prover, name: String): Unit =
    state.change(_.add(prover, name))

  def invoke(msg: Prover.Protocol_Output): Boolean =
    state.value.invoke(msg)

  def stop(prover: Prover): Unit =
    state.change(_.stop(prover))
}
