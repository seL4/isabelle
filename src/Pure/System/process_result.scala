/*  Title:      Pure/System/process_result.scala
    Author:     Makarius

Result of system process.
*/

package isabelle

object Process_Result {
  /* return code */

  object RC {
    val undefined = -1
    val ok = 0
    val error = 1
    val failure = 2
    val startup_failure = 127
    val interrupt = 130
    val timeout = 142

    val regular: Set[Int] = Set(ok, error)

    private def text(rc: Int): String = {
      val txt =
        rc match {
          case `undefined` => "UNDEFINED"
          case `ok` => "OK"
          case `error` => "ERROR"
          case `failure` => "FAILURE"
          case `startup_failure` => "COMMAND NOT FOUND"
          case `interrupt` => "INTERRUPT"
          case 131 => "QUIT SIGNAL"
          case 137 => "KILL SIGNAL"
          case 138 => "BUS ERROR"
          case 139 => "SEGMENTATION VIOLATION"
          case `timeout` => "TIMEOUT"
          case 143 => "TERMINATION SIGNAL"
          case _ => ""
        }
      if (txt.isEmpty) txt else " (" + txt + ")"
    }

    def print_long(rc: Int): String = "Return code: " + rc + text(rc)
    def print(rc: Int): String = "return code " + rc + text(rc)

    def merge(rc1: Int, rc2: Int): Int =
      if (rc1 == interrupt || rc2 == interrupt) interrupt
      else rc1 max rc2

    def merge(rcs: IterableOnce[Int]): Int = rcs.iterator.foldLeft(ok)(merge)

    def apply(ok: Boolean): Int = if (ok) RC.ok else RC.error
    def apply(exn: Throwable): Int = if (Exn.is_interrupt(exn)) interrupt else error
    def apply(result: Exn.Result[Process_Result]): Int =
      result match {
        case Exn.Res(res) => res.rc
        case Exn.Exn(exn) => apply(exn)
      }
  }

  val undefined: Process_Result = Process_Result(RC.undefined)
  val ok: Process_Result = Process_Result(RC.ok)
  val error: Process_Result = Process_Result(RC.error)
  val startup_failure: Process_Result = Process_Result(RC.startup_failure)
}

final case class Process_Result(
  rc: Int,
  out_lines: List[String] = Nil,
  err_lines: List[String] = Nil,
  timing: Timing = Timing.zero
) {
  def out: String = Library.trim_line(cat_lines(out_lines))
  def err: String = Library.trim_line(cat_lines(err_lines))

  def output(outs: List[String]): Process_Result =
    copy(out_lines = out_lines ::: outs.flatMap(split_lines))
  def errors(errs: List[String]): Process_Result =
    copy(err_lines = err_lines ::: errs.flatMap(split_lines))
  def error(err: String): Process_Result =
    if (err.isEmpty) this else errors(List(err))

  def ok: Boolean = rc == Process_Result.RC.ok
  def interrupted: Boolean = rc == Process_Result.RC.interrupt

  def defined: Boolean = rc > Process_Result.RC.undefined
  def strict: Process_Result = if (defined) this else copy(rc = Process_Result.RC.error)

  def timeout_rc: Process_Result = copy(rc = Process_Result.RC.timeout)
  def timeout: Boolean = rc == Process_Result.RC.timeout

  def error_rc: Process_Result =
    if (interrupted) this else copy(rc = rc max Process_Result.RC.error)

  def errors_rc(errs: List[String]): Process_Result =
    if (errs.isEmpty) this else errors(errs).error_rc

  def check_rc(pred: Int => Boolean): Process_Result =
    if (pred(rc)) this
    else if (interrupted) throw Exn.Interrupt()
    else Exn.error(err)

  def check: Process_Result = check_rc(_ == Process_Result.RC.ok)

  def print_return_code: String = Process_Result.RC.print_long(rc)
  def print_rc: String = Process_Result.RC.print(rc)

  def print: Process_Result = {
    Output.warning(err)
    Output.writeln(out)
    copy(out_lines = Nil, err_lines = Nil)
  }

  def print_stdout: Process_Result = {
    Output.warning(err, stdout = true)
    Output.writeln(out, stdout = true)
    copy(out_lines = Nil, err_lines = Nil)
  }
}
