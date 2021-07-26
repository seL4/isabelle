/*  Title:      Pure/System/process_result.scala
    Author:     Makarius

Result of system process.
*/

package isabelle

object Process_Result
{
  def print_return_code(rc: Int): String = "Return code: " + rc + rc_text(rc)
  def print_rc(rc: Int): String = "return code " + rc + rc_text(rc)

  def rc_text(rc: Int): String =
    return_code_text.get(rc) match {
      case None => ""
      case Some(text) => " (" + text + ")"
    }

  val interrupt_rc = 130
  val timeout_rc = 142

  private val return_code_text =
    Map(0 -> "OK",
      1 -> "ERROR",
      2 -> "FAILURE",
      127 -> "COMMAND NOT FOUND",
      interrupt_rc -> "INTERRUPT",
      131 -> "QUIT SIGNAL",
      137 -> "KILL SIGNAL",
      138 -> "BUS ERROR",
      139 -> "SEGMENTATION VIOLATION",
      timeout_rc -> "TIMEOUT",
      143 -> "TERMINATION SIGNAL")
}

final case class Process_Result(
  rc: Int,
  out_lines: List[String] = Nil,
  err_lines: List[String] = Nil,
  timing: Timing = Timing.zero)
{
  def out: String = Library.trim_line(cat_lines(out_lines))
  def err: String = Library.trim_line(cat_lines(err_lines))

  def output(outs: List[String]): Process_Result =
    copy(out_lines = out_lines ::: outs.flatMap(split_lines))
  def errors(errs: List[String]): Process_Result =
    copy(err_lines = err_lines ::: errs.flatMap(split_lines))
  def error(err: String): Process_Result =
    if (err.isEmpty) this else errors(List(err))

  def ok: Boolean = rc == 0
  def interrupted: Boolean = rc == Process_Result.interrupt_rc

  def timeout_rc: Process_Result = copy(rc = Process_Result.timeout_rc)
  def timeout: Boolean = rc == Process_Result.timeout_rc

  def error_rc: Process_Result = if (interrupted) this else copy(rc = rc max 1)

  def errors_rc(errs: List[String]): Process_Result =
    if (errs.isEmpty) this else errors(errs).error_rc

  def check_rc(pred: Int => Boolean): Process_Result =
    if (pred(rc)) this
    else if (interrupted) throw Exn.Interrupt()
    else Exn.error(err)

  def check: Process_Result = check_rc(_ == 0)

  def print_return_code: String = Process_Result.print_return_code(rc)
  def print_rc: String = Process_Result.print_rc(rc)

  def print: Process_Result =
  {
    Output.warning(err)
    Output.writeln(out)
    copy(out_lines = Nil, err_lines = Nil)
  }

  def print_stdout: Process_Result =
  {
    Output.warning(err, stdout = true)
    Output.writeln(out, stdout = true)
    copy(out_lines = Nil, err_lines = Nil)
  }
}
