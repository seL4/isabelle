/*  Title:      Pure/General/json.scala
    Author:     Makarius

Support for JSON parsing.
*/

package isabelle


import scala.util.parsing.json.{JSONObject, JSONArray}

object JSON
{
  type T = Any
  type S = String


  /* standard format */

  def parse(s: S): T = Format.unapply(s) getOrElse error("Malformed JSON")

  object Format
  {
    def unapply(s: S): Option[T] =
      try { scala.util.parsing.json.JSON.parseFull(s) }
      catch { case ERROR(_) => None }

    def apply(json: T): S =
    {
      val result = new StringBuilder

      def string(s: String)
      {
        result += '"'
        result ++=
          s.iterator.map {
            case '"'  => "\\\""
            case '\\' => "\\\\"
            case '\b' => "\\b"
            case '\f' => "\\f"
            case '\n' => "\\n"
            case '\r' => "\\r"
            case '\t' => "\\t"
            case c =>
              if (c <= '\u001f' || c >= '\u007f' && c <= '\u009f') "\\u%04x".format(c.toInt)
              else c
          }.mkString
        result += '"'
      }

      def array(list: List[T])
      {
        result += '['
        Library.separate(None, list.map(Some(_))).foreach({
          case None => result += ','
          case Some(x) => json_format(x)
        })
        result += ']'
      }

      def object_(obj: Map[String, T])
      {
        result += '{'
        Library.separate(None, obj.toList.map(Some(_))).foreach({
          case None => result += ','
          case Some((x, y)) =>
            string(x)
            result += ':'
            json_format(y)
        })
        result += '}'
      }

      def json_format(x: T)
      {
        x match {
          case null => result ++= "null"
          case _: Int | _: Long | _: Boolean => result ++= x.toString
          case n: Double =>
            val i = n.toLong
            result ++= (if (i.toDouble == n) i.toString else n.toString)
          case s: String => string(s)
          case JSONObject(obj) => object_(obj)
          case obj: Map[_, _] if obj.keySet.forall(_.isInstanceOf[String]) =>
            object_(obj.asInstanceOf[Map[String, T]])
          case JSONArray(list) => array(list)
          case list: List[T] => array(list)
          case _ => error("Bad JSON value: " + x.toString)
        }
      }

      json_format(json)
      result.toString
    }
  }


  /* numbers */

  object Number
  {
    object Double {
      def unapply(json: T): Option[scala.Double] =
        json match {
          case x: scala.Double => Some(x)
          case x: scala.Long => Some(x.toDouble)
          case x: scala.Int => Some(x.toDouble)
          case _ => None
        }
    }

    object Long {
      def unapply(json: T): Option[scala.Long] =
        json match {
          case x: scala.Double if x.toLong.toDouble == x => Some(x.toLong)
          case x: scala.Long => Some(x)
          case x: scala.Int => Some(x.toLong)
          case _ => None
        }
    }

    object Int {
      def unapply(json: T): Option[scala.Int] =
        json match {
          case x: scala.Double if x.toInt.toDouble == x => Some(x.toInt)
          case x: scala.Long if x.toInt.toLong == x => Some(x.toInt)
          case x: scala.Int => Some(x)
          case _ => None
        }
    }
  }


  /* object values */

  def value(obj: T, name: String): Option[T] =
    obj match {
      case m: Map[_, _] if m.keySet.forall(_.isInstanceOf[String]) =>
        m.asInstanceOf[Map[String, T]].get(name)
      case _ => None
    }

  def value[A](obj: T, name: String, unapply: T => Option[A]): Option[A] =
    for {
      json <- value(obj, name)
      x <- unapply(json)
    } yield x

  def array(obj: T, name: String): Option[List[T]] =
    value(obj, name) match {
      case Some(a: List[T]) => Some(a)
      case _ => None
    }

  def array[A](obj: T, name: String, unapply: T => Option[A]): Option[List[A]] =
    for {
      a0 <- array(obj, name)
      a = a0.map(unapply(_))
      if a.forall(_.isDefined)
    } yield a.map(_.get)

  def string(obj: T, name: String): Option[String] =
    value(obj, name) match {
      case Some(x: String) => Some(x)
      case _ => None
    }

  def double(obj: T, name: String): Option[Double] =
    value(obj, name, Number.Double.unapply)

  def long(obj: T, name: String): Option[Long] =
    value(obj, name, Number.Long.unapply)

  def int(obj: T, name: String): Option[Int] =
    value(obj, name, Number.Int.unapply)

  def bool(obj: T, name: String): Option[Boolean] =
    value(obj, name) match {
      case Some(x: Boolean) => Some(x)
      case _ => None
    }
}
