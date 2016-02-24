/*  Title:      Pure/System/process_result.scala
    Author:     Makarius

Result of system process.
*/

package isabelle

final case class Process_Result(out_lines: List[String], err_lines: List[String], rc: Int)
{
  def out: String = cat_lines(out_lines)
  def err: String = cat_lines(err_lines)

  def error(s: String, err_rc: Int = 0): Process_Result =
    copy(err_lines = err_lines ::: List(s), rc = rc max err_rc)

  def ok: Boolean = rc == 0
  def interrupted: Boolean = rc == Exn.Interrupt.return_code

  def check: Process_Result =
    if (ok) this
    else if (interrupted) throw Exn.Interrupt()
    else Library.error(err)

  def print: Process_Result =
  {
    Output.warning(Library.trim_line(err))
    Output.writeln(Library.trim_line(out))
    Process_Result(Nil, Nil, rc)
  }
}
