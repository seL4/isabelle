/*  Title:      Pure/General/date.scala
    Author:     Makarius

Date and time, with time zone.
*/

package isabelle


import java.time.{ZonedDateTime, ZoneId}
import java.time.format.{DateTimeFormatter, DateTimeParseException}


object Date
{
  def timezone(): ZoneId = ZoneId.systemDefault

  def now(zone: ZoneId = timezone()): Date = new Date(ZonedDateTime.now(zone))

  def apply(t: Time, zone: ZoneId = timezone()): Date =
    new Date(ZonedDateTime.ofInstant(t.instant, zone))


  /* format */

  object Format
  {
    def apply(fmt: DateTimeFormatter): Format =
      new Format {
        def apply(date: Date): String = fmt.format(date.rep)
        def parse(str: String): Date = new Date(ZonedDateTime.from(fmt.parse(str)))
      }

    def apply(pattern: String): Format =
      apply(DateTimeFormatter.ofPattern(pattern))

    val default: Format = apply("dd-MMM-uuuu HH:mm:ss xx")
    val default_date: Format = apply("dd-MMM-uuuu")
    val default_time: Format = apply("HH:mm:ss")
  }

  abstract class Format private
  {
    def apply(date: Date): String
    def parse(str: String): Date
    def unapply(str: String): Option[Date] =
      try { Some(parse(str)) }
      catch { case _: DateTimeParseException => None }
  }
}

sealed case class Date private(private[Date] rep: ZonedDateTime)
{
  override def toString: String = Date.Format.default(this)
}
