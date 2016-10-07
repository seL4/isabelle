/*  Title:      Pure/General/date.scala
    Author:     Makarius

Date and time, with time zone.
*/

package isabelle


import java.util.Locale
import java.time.{Instant, ZonedDateTime, ZoneId}
import java.time.format.{DateTimeFormatter, DateTimeParseException}
import java.time.temporal.TemporalAccessor

import scala.annotation.tailrec


object Date
{
  /* format */

  object Format
  {
    def make(fmts: List[DateTimeFormatter], filter: String => String = s => s): Format =
    {
      require(fmts.nonEmpty)

      @tailrec def parse_first(
        last_exn: Option[Throwable], fs: List[DateTimeFormatter], str: String): TemporalAccessor =
      {
        fs match {
          case Nil => throw last_exn.get
          case f :: rest =>
            try { ZonedDateTime.from(f.parse(str)) }
            catch { case exn: DateTimeParseException => parse_first(Some(exn), rest, str) }
        }
      }
      new Format {
        def apply(date: Date): String = fmts.head.format(date.rep)
        def parse(str: String): Date =
          new Date(ZonedDateTime.from(parse_first(None, fmts, filter(str))))
      }
    }

    def make_variants(patterns: List[String],
      locales: List[Locale] = List(Locale.ROOT),
      filter: String => String = s => s): Format =
    {
      val fmts =
        patterns.flatMap(pat =>
          {
            val fmt = DateTimeFormatter.ofPattern(pat)
            locales.map(fmt.withLocale(_))
          })
      make(fmts, filter)
    }

    def apply(patterns: String*): Format =
      make(patterns.toList.map(DateTimeFormatter.ofPattern(_)))

    val default: Format = apply("dd-MMM-uuuu HH:mm:ss xx")
    val date: Format = apply("dd-MMM-uuuu")
    val time: Format = apply("HH:mm:ss")
  }

  abstract class Format private
  {
    def apply(date: Date): String
    def parse(str: String): Date
    def unapply(str: String): Option[Date] =
      try { Some(parse(str)) }
      catch { case _: DateTimeParseException => None }
    object Strict
    {
      def unapply(s: String): Some[Date] = Some(parse(s))
    }
  }


  /* date operations */

  def timezone(): ZoneId = ZoneId.systemDefault

  def now(zone: ZoneId = timezone()): Date = new Date(ZonedDateTime.now(zone))

  def apply(t: Time, zone: ZoneId = timezone()): Date =
    new Date(ZonedDateTime.ofInstant(t.instant, zone))
}

sealed case class Date(rep: ZonedDateTime)
{
  def time: Time = Time.instant(Instant.from(rep))
  def timezone: ZoneId = rep.getZone

  def format(fmt: Date.Format = Date.Format.default): String = fmt(this)
  override def toString: String = format()
}
