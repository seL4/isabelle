/*  Title:      Pure/update.scala
    Author:     Makarius

Update data (with formal name).
*/

package isabelle


object Update {
  sealed abstract class Op[A]
  case class Delete[A](name: String) extends Op[A]
  case class Insert[A](item: A) extends Op[A]

  def data[A <: Name.T](old_data: Name.Data[A], updates: List[Op[A]]): Name.Data[A] =
    updates.foldLeft(old_data) {
      case (map, Delete(name)) => map - name
      case (map, Insert(item)) => map + (item.name -> item)
    }

  val empty: Update = Update()

  def make[A](a: Name.Data[A], b: Name.Data[A], kind: Int = 0): Update =
    if (a eq b) empty
    else {
      val delete = List.from(for ((x, y) <- a.iterator if !b.get(x).contains(y)) yield x)
      val insert = List.from(for ((x, y) <- b.iterator if !a.get(x).contains(y)) yield x)
      Update(delete = delete, insert = insert, kind = kind)
    }
}

sealed case class Update(
  delete: List[String] = Nil,
  insert: List[String] = Nil,
  kind: Int = 0
) {
  def deletes: Boolean = delete.nonEmpty
  def inserts: Boolean = insert.nonEmpty
  def defined: Boolean = deletes || inserts
  lazy val domain: Set[String] = delete.toSet ++ insert
}
