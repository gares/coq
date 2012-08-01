/*  Title:      Pure/General/position.scala
    Author:     Makarius

Position properties.
*/

package pide


object Position
{
  type T = Properties.T

  val Line = new Properties.Int(Slave_Markup.LINE)
  val Offset = new Properties.Int(Slave_Markup.OFFSET)
  val End_Offset = new Properties.Int(Slave_Markup.END_OFFSET)
  val File = new Properties.String(Slave_Markup.FILE)
  val Id = new Properties.Long(Slave_Markup.ID)

  object Range
  {
    def apply(range: Text.Range): T = Offset(range.start) ++ Offset(range.stop)
    def unapply(pos: T): Option[Text.Range] =
      (Offset.unapply(pos), End_Offset.unapply(pos)) match {
        case (Some(start), Some(stop)) if start <= stop => Some(Text.Range(start, stop))
        case (Some(start), None) => Some(Text.Range(start, start + 1))
        case _ => None
      }
  }

  object Id_Range
  {
    def unapply(pos: T): Option[(Long, Text.Range)] =
      (pos, pos) match {
        case (Id(id), Range(range)) => Some((id, range))
        case _ => None
      }
  }

  private val purge_pos = Map(
    Slave_Markup.DEF_LINE -> Slave_Markup.LINE,
    Slave_Markup.DEF_OFFSET -> Slave_Markup.OFFSET,
    Slave_Markup.DEF_END_OFFSET -> Slave_Markup.END_OFFSET,
    Slave_Markup.DEF_FILE -> Slave_Markup.FILE,
    Slave_Markup.DEF_ID -> Slave_Markup.ID)

  def purge(props: T): T =
    for ((x, y) <- props if !Slave_Markup.POSITION_PROPERTIES(x))
      yield (if (purge_pos.isDefinedAt(x)) (purge_pos(x), y) else (x, y))
}
