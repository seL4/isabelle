/*  Title:      Pure/System/process_result.scala
    Author:     Makarius

Result of system process.
*/

package isabelle

final case class Process_Result(
  rc: Int,
  out_lines: List[String] = Nil,
  err_lines: List[String] = Nil,
  timeout: Option[Time] = None)
{
  def out: String = cat_lines(out_lines)
  def err: String = cat_lines(err_lines)
  def error(s: String): Process_Result = copy(err_lines = err_lines ::: List(s))

  def set_timeout(t: Time): Process_Result = copy(rc = 1, timeout = Some(t))

  def ok: Boolean = rc == 0
  def interrupted: Boolean = rc == Exn.Interrupt.return_code

  def check: Process_Result =
    if (ok) this
    else if (interrupted) throw Exn.Interrupt()
    else Exn.error(err)

  def print: Process_Result =
  {
    Output.warning(Library.trim_line(err))
    Output.writeln(Library.trim_line(out))
    copy(out_lines = Nil, err_lines = Nil)
  }

  def print_stdout: Process_Result =
  {
    Output.warning(Library.trim_line(err), stdout = true)
    Output.writeln(Library.trim_line(out), stdout = true)
    copy(out_lines = Nil, err_lines = Nil)
  }
}
