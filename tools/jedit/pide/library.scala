/*  Title:      Pure/library.scala
    Module:     PIDE
    Author:     Makarius

Basic library.
*/

package pide

import java.lang.System
import scala.collection.mutable


object Library
{
  /* user errors */

  object ERROR
  {
    def apply(message: String): Throwable = new RuntimeException(message)
    def unapply(exn: Throwable): Option[String] =
      exn match {
        case e: RuntimeException => Some(Exn.message(e))
        case _ => None
      }
  }

  def error(message: String): Nothing = throw ERROR(message)

  def cat_error(msg1: String, msg2: String): Nothing =
    if (msg1 == "") error(msg1)
    else error(msg1 + "\n" + msg2)


  /* lists */

  def separate[A](s: A, list: List[A]): List[A] =
    list match {
      case x :: xs if !xs.isEmpty => x :: s :: separate(s, xs)
      case _ => list
    }

  def space_explode(sep: Char, str: String): List[String] =
    if (str.isEmpty) Nil
    else {
      val result = new mutable.ListBuffer[String]
      var start = 0
      var finished = false
      while (!finished) {
        val i = str.indexOf(sep, start)
        if (i == -1) { result += str.substring(start); finished = true }
        else { result += str.substring(start, i); start = i + 1 }
      }
      result.toList
    }

  def split_lines(str: String): List[String] = space_explode('\n', str)


  /* iterate over chunks (cf. space_explode) */

  def chunks(source: CharSequence, sep: Char = '\n') = new Iterator[CharSequence]
  {
    private val end = source.length
    private def next_chunk(i: Int): Option[(CharSequence, Int)] =
    {
      if (i < end) {
        var j = i; do j += 1 while (j < end && source.charAt(j) != sep)
        Some((source.subSequence(i + 1, j), j))
      }
      else None
    }
    private var state: Option[(CharSequence, Int)] = if (end == 0) None else next_chunk(-1)

    def hasNext(): Boolean = state.isDefined
    def next(): CharSequence =
      state match {
        case Some((s, i)) => { state = next_chunk(i); s }
        case None => Iterator.empty.next()
      }
  }

  def first_line(source: CharSequence): String =
  {
    val lines = chunks(source)
    if (lines.hasNext) lines.next.toString
    else ""
  }


  /* strings */

  def cat_lines(lines: TraversableOnce[String]): String = lines.mkString("\n")

  def quote(s: String): String = "\"" + s + "\""
  def commas(ss: Iterable[String]): String = ss.iterator.mkString(", ")
  def commas_quote(ss: Iterable[String]): String = ss.iterator.mkString("\"", ", ", "\"")


  /* reverse CharSequence */

  class Reverse(text: CharSequence, start: Int, end: Int) extends CharSequence
  {
    require(0 <= start && start <= end && end <= text.length)

    def this(text: CharSequence) = this(text, 0, text.length)

    def length: Int = end - start
    def charAt(i: Int): Char = text.charAt(end - i - 1)

    def subSequence(i: Int, j: Int): CharSequence =
      if (0 <= i && i <= j && j <= length) new Reverse(text, end - j, end - i)
      else throw new IndexOutOfBoundsException

    override def toString: String =
    {
      val buf = new StringBuilder(length)
      for (i <- 0 until length)
        buf.append(charAt(i))
      buf.toString
    }
  }


}


class Basic_Library
{
  val ERROR = Library.ERROR
  val error = Library.error _
  val cat_error = Library.cat_error _

  val space_explode = Library.space_explode _
  val split_lines = Library.split_lines _
  val cat_lines = Library.cat_lines _
  val quote = Library.quote _
  val commas = Library.commas _
  val commas_quote = Library.commas_quote _
}
