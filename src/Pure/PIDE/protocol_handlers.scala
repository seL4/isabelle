/*  Title:      Pure/PIDE/protocol_handlers.scala
    Author:     Makarius

Management of add-on protocol handlers for PIDE session.
*/

package isabelle


object Protocol_Handlers
{
  private def err_handler(exn: Throwable, name: String): Nothing =
    error("Failed to initialize protocol handler: " + quote(name) + "\n" + Exn.message(exn))

  sealed case class State(
    session: Session,
    handlers: Map[String, Session.Protocol_Handler] = Map.empty,
    functions: Map[String, Session.Protocol_Function] = Map.empty)
  {
    def get(name: String): Option[Session.Protocol_Handler] = handlers.get(name)

    def init(handler: Session.Protocol_Handler): State =
    {
      val name = handler.getClass.getName
      try {
        if (handlers.isDefinedAt(name)) error("Duplicate protocol handler: " + name)
        else {
          handler.init(session)
          val dups = for ((a, _) <- handler.functions if functions.isDefinedAt(a)) yield a
          if (dups.nonEmpty) error("Duplicate protocol functions: " + commas_quote(dups))
          copy(handlers = handlers + (name -> handler), functions = functions ++ handler.functions)
        }
      }
      catch { case exn: Throwable => err_handler(exn, name) }
    }

    def init(name: String): State =
    {
      val handler =
        try {
          Class.forName(name).getDeclaredConstructor().newInstance()
            .asInstanceOf[Session.Protocol_Handler]
        }
        catch { case exn: Throwable => err_handler(exn, name) }
      init(handler)
    }

    def invoke(msg: Prover.Protocol_Output): Boolean =
      msg.properties match {
        case (Markup.FUNCTION, a) :: _ if functions.isDefinedAt(a) =>
          try { functions(a)(msg) }
          catch {
            case exn: Throwable =>
              Output.error_message(
                "Failed invocation of protocol function: " + quote(a) + "\n" + Exn.message(exn))
            false
          }
        case _ => false
      }

    def exit(): State =
    {
      for ((_, handler) <- handlers) handler.exit()
      copy(handlers = Map.empty, functions = Map.empty)
    }
  }

  def init(session: Session): Protocol_Handlers =
    new Protocol_Handlers(session)
}

class Protocol_Handlers private(session: Session)
{
  private val state = Synchronized(Protocol_Handlers.State(session))

  def prover_options(options: Options): Options =
    state.value.handlers.foldLeft(options) {
      case (opts, (_, handler)) => handler.prover_options(opts)
    }

  def get(name: String): Option[Session.Protocol_Handler] = state.value.get(name)
  def init(handler: Session.Protocol_Handler): Unit = state.change(_.init(handler))
  def init(name: String): Unit = state.change(_.init(name))
  def invoke(msg: Prover.Protocol_Output): Boolean = state.value.invoke(msg)
  def exit(): Unit = state.change(_.exit())
}
