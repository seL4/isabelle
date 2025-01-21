/*  Title:      Pure/General/date.scala
    Author:     Makarius

Date and time, with timezone.
*/

package isabelle


import java.util.Locale
import java.time.{Instant, ZonedDateTime, LocalTime, ZoneId}
import java.time.format.{DateTimeFormatter, DateTimeParseException}
import java.time.temporal.{ChronoUnit, TemporalAccessor}

import scala.annotation.tailrec


object Date {
  /* format */

  object Format {
    def make(fmts: List[DateTimeFormatter], tune: String => String = s => s): Format = {
      require(fmts.nonEmpty, "no date formats")

      new Format {
        def apply(date: Date): String = fmts.head.format(date.rep)
        def parse(str: String): Date =
          new Date(ZonedDateTime.from(Formatter.try_variants(fmts, tune(str))))
      }
    }

    def apply(pats: String*): Format =
      make(pats.toList.map(Date.Formatter.pattern))

    val default: Format = Format("dd-MMM-uuuu HH:mm:ss xx")
    val date: Format = Format("dd-MMM-uuuu")
    val time: Format = Format("HH:mm:ss")
    val alt_date: Format = Format("uuuuMMdd")
  }

  abstract class Format private {
    def apply(date: Date): String
    def parse(str: String): Date

    def unapply(str: String): Option[Date] =
      try { Some(parse(str)) } catch { case _: DateTimeParseException => None }
  }

  object Formatter {
    def pattern(pat: String): DateTimeFormatter = DateTimeFormatter.ofPattern(pat)

    def variants(pats: List[String], locs: List[Locale] = Nil): List[DateTimeFormatter] =
      pats.flatMap { pat =>
        val fmt = pattern(pat)
        if (locs.isEmpty) List(fmt) else locs.map(fmt.withLocale)
      }

    @tailrec def try_variants(
      fmts: List[DateTimeFormatter],
      str: String,
      last_exn: Option[DateTimeParseException] = None
    ): TemporalAccessor = {
      fmts match {
        case Nil =>
          throw last_exn.getOrElse(new DateTimeParseException("Failed to parse date", str, 0))
        case fmt :: rest =>
          try { ZonedDateTime.from(fmt.parse(str)) }
          catch { case exn: DateTimeParseException => try_variants(rest, str, Some(exn)) }
      }
    }
  }


  /* ordering */

  object Ordering extends scala.math.Ordering[Date] {
    def compare(date1: Date, date2: Date): Int =
      date1.instant.compareTo(date2.instant)
  }

  object Rev_Ordering extends scala.math.Ordering[Date] {
    def compare(date1: Date, date2: Date): Int =
      date2.instant.compareTo(date1.instant)
  }


  /* date operations */

  def timezone_utc: ZoneId = ZoneId.of("UTC")
  def timezone_berlin: ZoneId = ZoneId.of("Europe/Berlin")

  def timezone(): ZoneId = ZoneId.systemDefault

  def now(timezone: ZoneId = Date.timezone()): Date =
    new Date(ZonedDateTime.now(timezone))

  def instant(t: Instant, timezone: ZoneId = Date.timezone()): Date =
    new Date(ZonedDateTime.ofInstant(t, timezone))

  def apply(t: Time, timezone: ZoneId = Date.timezone()): Date =
    instant(t.instant, timezone)


  /* varying-length calendar cycles */

  enum Day { case mon, tue, wed, thu, fri, sat, sun }
  enum Month { case jan, feb, mar, apr, may, jun, jul, aug, sep, okt, nov, dec }

  sealed trait Cycle {
    def zero(date: Date): Date
    def next(date: Date): Date
  }

  case class Daily(at: Time = Time.zero) extends Cycle {
    require(at >= Time.zero && at < Time.hms(24, 0, 0))

    def zero(date: Date): Date = date.midnight
    def next(date: Date): Date = {
      val start = zero(date) + at
      if (date.time < start.time) start else start.shift(1)
    }

    override def toString: String = "Daily(" + Format.time(Date(at, timezone_utc)) + ")"
  }

  case class Weekly(on: Day = Day.mon, step: Daily = Daily()) extends Cycle {
    def zero(date: Date): Date = date.shift(1 - date.rep.getDayOfWeek.getValue).midnight
    def next(date: Date): Date = {
      val next = step.next(zero(date).shift(on.ordinal) - Time.ms(1))
      if (date.time < next.time) next else Date(next.rep.plus(1, ChronoUnit.WEEKS))
    }
  }

  case class Monthly(nth: Int = 1, step: Daily = Daily()) extends Cycle {
    require(nth > 0 && nth <= 31)

    def zero(date: Date): Date = date.shift(1 - date.rep.getDayOfMonth).midnight
    def next(date: Date): Date = {
      @tailrec def find_next(zero: Date): Date = {
        val next = step.next(zero.shift(nth - 1) - Time.ms(1))
        if (next.rep.getDayOfMonth == nth && date.time < next.time) next
        else find_next(Date(zero.rep.plus(1, ChronoUnit.MONTHS)))
      }
      find_next(zero(date))
    }
  }

  case class Yearly(in: Month = Month.jan, step: Monthly = Monthly()) extends Cycle {
    def zero(date: Date): Date = date.shift(1 - date.rep.getDayOfYear).midnight
    def next(date: Date): Date = {
      @tailrec def find_next(zero: Date): Date = {
        val next = step.next(Date(zero.rep.plus(in.ordinal, ChronoUnit.MONTHS)) - Time.ms(1))
        if (next.rep.getMonthValue - 1 == in.ordinal && date.time < next.time) next
        else find_next(Date(zero.rep.plus(1, ChronoUnit.YEARS)))
      }
      find_next(zero(date))
    }
  }
}

sealed case class Date(rep: ZonedDateTime) {
  def shift(days: Int): Date = Date(rep.plus(days, ChronoUnit.DAYS))
  def midnight: Date =
    new Date(ZonedDateTime.of(rep.toLocalDate, LocalTime.MIDNIGHT, rep.getZone))

  def to(other: ZoneId): Date = new Date(rep.withZoneSameInstant(other))

  def unix_epoch: Long = rep.toEpochSecond
  def unix_epoch_day: Long = rep.toLocalDate.toEpochDay
  def instant: Instant = Instant.from(rep)
  def time: Time = Time.instant(instant)
  def timezone: ZoneId = rep.getZone

  def + (t: Time): Date = Date(time + t, timezone = timezone)
  def - (t: Time): Date = Date(time - t, timezone = timezone)
  def - (d: Date): Time = time - d.time

  def format(fmt: Date.Format = Date.Format.default): String = fmt(this)
  override def toString: String = format()
}
