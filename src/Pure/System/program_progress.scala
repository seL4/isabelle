/*  Title:      Pure/System/program_progress.scala
    Author:     Makarius

Structured program progress.
*/

package isabelle


object Program_Progress {
  class Program private[Program_Progress](heading: String, title: String) {
    private val output_buffer = new StringBuffer(256)  // synchronized

    def output(message: Progress.Message): Unit = synchronized {
      if (output_buffer.length() > 0) output_buffer.append('\n')
      output_buffer.append(message.output_text)
    }

    val start_time: Time = Time.now()
    private var stop_time: Option[Time] = None
    def stop_now(): Unit = synchronized { stop_time = Some(Time.now()) }

    def output(): (Command.Results, XML.Elem) = synchronized {
      val output_text = output_buffer.toString
      val elapsed_time = stop_time.map(t => t - start_time)

      val message_prefix = heading + " "
      val message_suffix =
        elapsed_time match {
          case None => " ..."
          case Some(t) => " ... (" + t.message + " elapsed time)"
        }

      val (results, message) =
        if (output_text.isEmpty) {
          (Command.Results.empty, XML.string(message_prefix + title + message_suffix))
        }
        else {
          val i = Document_ID.make()
          val results = Command.Results.make(List(i -> Protocol.writeln_message(output_text)))
          val message =
            XML.string(message_prefix) :::
            List(XML.Elem(Markup(Markup.WRITELN, Markup.Serial(i)), XML.string(title))) :::
            XML.string(message_suffix)
          (results, message)
        }

      (results, XML.elem(Markup.TRACING_MESSAGE, message))
    }
  }
}

abstract class Program_Progress(
  default_heading: String = "Running",
  default_title: String = "program",
  override val verbose: Boolean = false
) extends Progress {
  private var _finished_programs: List[Program_Progress.Program] = Nil
  private var _running_program: Option[Program_Progress.Program] = None

  def output(): (Command.Results, List[XML.Elem]) = synchronized {
    val programs = (_running_program.toList ::: _finished_programs).reverse
    val programs_output = programs.map(_.output())
    val results = Command.Results.merge(programs_output.map(_._1))
    (results, programs_output.map(_._2))
  }

  private def start_program(heading: String, title: String): Unit = synchronized {
    _running_program = Some(new Program_Progress.Program(heading, title))
  }

  def stop_program(): Unit = synchronized {
    _running_program match {
      case Some(program) =>
        program.stop_now()
        _finished_programs ::= program
        _running_program = None
      case None =>
    }
  }

  def detect_program(s: String): Option[String]

  override def output(message: Progress.Message): Unit = synchronized {
    val writeln_msg = if (message.kind == Progress.Kind.writeln) message.text else ""
    detect_program(writeln_msg).map(Word.explode) match {
      case Some(a :: bs) =>
        stop_program()
        start_program(a, Word.implode(bs))
      case _ =>
        if (_running_program.isEmpty) start_program(default_heading, default_title)
        if (do_output(message)) _running_program.get.output(message)
    }
  }
}
