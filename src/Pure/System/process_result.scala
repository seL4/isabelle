/*  Title:      Pure/System/process_result.scala
    Author:     Makarius

Result of system process.
*/

package isabelle

object Process_Result
{
  val return_code_text: Map[Int, String] =
    Map(0 -> "OK",
      1 -> "ERROR",
      2 -> "FAILURE",
      130 -> "INTERRUPT",
      131 -> "QUIT SIGNAL",
      137 -> "KILL SIGNAL",
      138 -> "BUS ERROR",
      139 -> "SEGMENTATION VIOLATION",
      143 -> "TERMINATION SIGNAL")

  def print_return_code(rc: Int): String =
  {
    val text = return_code_text.get(rc)
    "Return code: " + rc + (if (text.isEmpty) "" else " (" + text.get + ")")
  }

  def print_rc(rc: Int): String = "return code " + rc
}

final case class Process_Result(
  rc: Int,
  out_lines: List[String] = Nil,
  err_lines: List[String] = Nil,
  timeout: Boolean = false,
  timing: Timing = Timing.zero)
{
  def out: String = cat_lines(out_lines)
  def err: String = cat_lines(err_lines)

  def output(outs: List[String]): Process_Result =
    copy(out_lines = out_lines ::: outs.flatMap(split_lines))
  def errors(errs: List[String]): Process_Result =
    copy(err_lines = err_lines ::: errs.flatMap(split_lines))
  def error(err: String): Process_Result = errors(List(err))

  def was_timeout: Process_Result = copy(rc = 1, timeout = true)

  def ok: Boolean = rc == 0
  def interrupted: Boolean = rc == Exn.Interrupt.return_code

  def error_rc: Process_Result = if (interrupted) this else copy(rc = rc max 1)

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

  def print_if(b: Boolean): Process_Result = if (b) print else this
  def print_stdout_if(b: Boolean): Process_Result = if (b) print_stdout else this
}
