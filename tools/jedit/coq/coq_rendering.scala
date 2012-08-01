/*  Title:      Tools/jEdit/src/coq_rendering.scala
    Author:     Makarius

Coq specific physical rendering and markup selection.
*/

package coq
import pide._
import pide.jedit._

import java.awt.Color
import javax.swing.Icon

import org.lobobrowser.util.gui.ColorFactory
import org.gjt.sp.jedit.syntax.{Token => JEditToken}

import scala.collection.immutable.SortedMap


object Coq_Rendering extends JEdit_Prover.Rendering
{
  /* physical rendering */

  def get_color(s: String): Color = ColorFactory.getInstance.getColor(s)

  val quoted_color = new Color(139, 139, 139, 25)
  val unprocessed1_color = new Color(139, 139, 139, 25)
  val running_color = new Color(139, 139, 139, 25)
  val warning_color = new Color(139, 139, 139, 25)
  val error_color =  new Color(139, 139, 139, 25)


  /* command overview */

  def overview_color(snapshot: Document.Snapshot, range: Text.Range): Option[Color] = None


  /* markup selectors */

  def subexp(snapshot: Document.Snapshot, range: Text.Range): Option[Text.Info[Color]] = None

  def tooltip_message(snapshot: Document.Snapshot, range: Text.Range): Option[String] = None

  def gutter_message(snapshot: Document.Snapshot, range: Text.Range): Option[Icon] = None

  def squiggly_underline(snapshot: Document.Snapshot, range: Text.Range): Stream[Text.Info[Color]] =
    Stream.empty

  def background1(snapshot: Document.Snapshot, range: Text.Range): Stream[Text.Info[Color]] =
    Stream.empty

  def background2(snapshot: Document.Snapshot, range: Text.Range): Stream[Text.Info[Color]] =
    Stream.empty

  def foreground(snapshot: Document.Snapshot, range: Text.Range): Stream[Text.Info[Color]] =
    snapshot.select_markup(range,
      Some(Set(Coq_Markup.STRING)),
      {
        case Text.Info(_, XML.Elem(Markup(Coq_Markup.STRING, _), _)) => quoted_color
      })


  private val text_colors: Map[String, Color] =
    Map(
      Coq_Markup.COMMENT -> get_color("#A52A2A"),
      Coq_Markup.KEYWORD -> get_color("#0000FF"),
      Coq_Markup.DECLARATION -> get_color("#FF4500"),
      Coq_Markup.PROOF_DECLARATION -> get_color("#FF4500"),
      Coq_Markup.QED -> get_color("#0000FF"),
      Coq_Markup.STRING -> get_color("black"),
      Coq_Markup.DELIMITER -> get_color("red"))

  private val text_color_elements = Set.empty[String] ++ text_colors.keys

  def text_color(snapshot: Document.Snapshot, range: Text.Range, color: Color)
      : Stream[Text.Info[Color]] =
    snapshot.cumulate_markup(range, color, Some(text_color_elements),
      {
        case (_, Text.Info(_, XML.Elem(Markup(m, _), _)))
        if text_colors.isDefinedAt(m) => text_colors(m)
      })

  def tooltip(snapshot: Document.Snapshot, range: Text.Range): Option[String] =
  { None }

  private val token_style: Map[Token.Kind.Value, Byte] =
  {
    import JEditToken._
    Map[Token.Kind.Value, Byte](
      Token.Kind.KEYWORD -> KEYWORD2,
      Token.Kind.IDENT -> NULL,
      Token.Kind.LONG_IDENT -> NULL,
      Token.Kind.SYM_IDENT -> NULL,
      Token.Kind.VAR -> NULL,
      Token.Kind.TYPE_IDENT -> NULL,
      Token.Kind.TYPE_VAR -> NULL,
      Token.Kind.NAT -> NULL,
      Token.Kind.FLOAT -> NULL,
      Token.Kind.STRING -> LITERAL1,
      Token.Kind.ALT_STRING -> LITERAL2,
      Token.Kind.VERBATIM -> COMMENT3,
      Token.Kind.SPACE -> NULL,
      Token.Kind.COMMENT -> COMMENT1,
      Token.Kind.UNPARSED -> INVALID
    ).withDefaultValue(NULL)
  }


  def token_markup(syntax: Outer_Syntax, token: Token): Byte = 
    token_style(token.kind)
}
