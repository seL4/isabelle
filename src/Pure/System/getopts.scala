/*  Title:      Pure/System/getopts.scala
    Author:     Makarius

Support for command-line options as in GNU bash.
*/

package isabelle


import scala.annotation.tailrec


object Getopts {
  def apply(usage_text: => String, option_specs: (String, String => Unit)*): Getopts = {
    val options =
      option_specs.foldLeft(Map.empty[Char, (Boolean, String => Unit)]) {
        case (m, (s, f)) =>
          val (a, entry) =
            if (s.length == 1) (s(0), (false, f))
            else if (s.length == 2 && s.endsWith(":")) (s(0), (true, f))
            else error("Bad option specification: " + quote(s))
          if (m.isDefinedAt(a)) error("Duplicate option specification: " + quote(a.toString))
          else m + (a -> entry)
      }
    new Getopts(usage_text, options)
  }
}

class Getopts private(usage_text: => String, options: Map[Char, (Boolean, String => Unit)]) {
  def usage(internal: Boolean = false): Nothing = {
    if (internal) error(usage_text)
    else {
      Output.writeln(usage_text, stdout = true)
      sys.exit(Process_Result.RC.error)
    }
  }

  private def is_option(opt: Char): Boolean = options.isDefinedAt(opt)
  private def is_option0(opt: Char): Boolean = is_option(opt) && !options(opt)._1
  private def is_option1(opt: Char): Boolean = is_option(opt) && options(opt)._1
  private def print_option(opt: Char): String = quote("-" + opt.toString)
  private def option(opt: Char, opt_arg: List[Char]): Unit =
    try { options(opt)._2.apply(opt_arg.mkString) }
    catch {
      case ERROR(msg) =>
        cat_error(msg, "The error(s) above occurred in command-line option " + print_option(opt))
    }

  private def err(msg: String, internal: Boolean): Nothing =
    if (internal) cat_error(msg, usage_text)
    else { Output.error_message(msg); usage() }

  @tailrec private def getopts(args: List[List[Char]], internal: Boolean): List[List[Char]] =
    args match {
      case List('-', '-') :: rest_args => rest_args
      case ('-' :: opt :: rest_opts) :: rest_args if is_option0(opt) && rest_opts.nonEmpty =>
        option(opt, Nil); getopts(('-' :: rest_opts) :: rest_args, internal)
      case List('-', opt) :: rest_args if is_option0(opt) =>
        option(opt, Nil); getopts(rest_args, internal)
      case ('-' :: opt :: opt_arg) :: rest_args if is_option1(opt) && opt_arg.nonEmpty =>
        option(opt, opt_arg); getopts(rest_args, internal)
      case List('-', opt) :: opt_arg :: rest_args if is_option1(opt) =>
        option(opt, opt_arg); getopts(rest_args, internal)
      case List(List('-', opt)) if is_option1(opt) =>
        err("Command-line option " + print_option(opt) + " requires an argument", internal)
      case ('-' :: opt :: _) :: _ if !is_option(opt) =>
        err(if (opt != '?') "Illegal command-line option " + print_option(opt) else "", internal)
      case _ => args
  }

  def apply(args: List[String], internal: Boolean): List[String] =
    getopts(args.map(_.toList), internal).map(_.mkString)
  def apply(args: List[String]): List[String] = apply(args, false)
  def apply(args: Array[String]): List[String] = apply(args.toList)
}
