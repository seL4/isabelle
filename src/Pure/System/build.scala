/*  Title:      Pure/System/build.scala
    Author:     Makarius

Build and manage Isabelle sessions.
*/

package isabelle


object Build
{
  /* command line entry point */

  private object Bool
  {
    def unapply(s: String): Option[Boolean] =
      s match {
        case "true" => Some(true)
        case "false" => Some(false)
        case _ => None
      }
  }

  def main(args: Array[String])
  {
    def bad_args()
    {
      java.lang.System.err.println("Bad arguments: " + args.toString)
      sys.exit(2)
    }

    args.toList match {
      case Bool(all_sessions) :: Bool(build_images) :: Bool(list_only) :: rest =>
        rest.indexWhere(_ == "\n") match {
          case -1 => bad_args()
          case i =>
            val (options, rest1) = rest.splitAt(i)
            val sessions = rest1.tail
            val rc = build(all_sessions, build_images, list_only, options, sessions)
            sys.exit(rc)
        }
      case _ => bad_args()
    }
  }


  /* build */

  def build(all_sessions: Boolean, build_images: Boolean, list_only: Boolean,
    options: List[String], sessions: List[String]): Int =
  {
    val rc = 1

    println("options = " + options.toString)
    println("sessions = " + sessions.toString)

    rc
  }
}

