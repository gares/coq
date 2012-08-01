package pide.jedit
import  pide._

import java.lang.System
import java.awt.{Font, Color}
import javax.swing.{JOptionPane, Icon}

import scala.collection.mutable
import scala.swing.{ComboBox, ListView, ScrollPane}

import org.gjt.sp.jedit.{jEdit, GUIUtilities, EBMessage, EBPlugin,
  Buffer, EditPane, ServiceManager, View}
import org.gjt.sp.jedit.buffer.JEditBuffer
import org.gjt.sp.jedit.textarea.{JEditTextArea, TextArea}
import org.gjt.sp.jedit.syntax.{Token => JEditToken, ModeProvider}
import org.gjt.sp.jedit.msg.{EditorStarted, BufferUpdate, EditPaneUpdate, PropertiesChanged}
import org.gjt.sp.jedit.gui.DockableWindowManager

import org.gjt.sp.util.SyntaxUtilities
import org.gjt.sp.util.Log
import org.gjt.sp.jedit.EBPlugin

import scala.actors.Actor._

object JEdit_Prover
{
  abstract class Rendering {
    import Document._
    import Text._
  
    def get_color(s: String): Color
    val quoted_color : Color
    val unprocessed1_color : Color
    val running_color : Color
    val warning_color : Color
    val error_color : Color
    def overview_color(snapshot: Snapshot, range: Range): Option[Color]
    def subexp(snapshot: Snapshot, range: Range): Option[Info[Color]]
    def tooltip_message(snapshot: Snapshot, range: Range): Option[String]
    def gutter_message(snapshot: Snapshot, range: Range): Option[Icon]
    def squiggly_underline(snapshot: Snapshot, range: Range): Stream[Info[Color]]
    def background1(snapshot: Snapshot, range: Range): Stream[Info[Color]]
    def background2(snapshot: Snapshot, range: Range): Stream[Info[Color]]
    def foreground(snapshot: Snapshot, range: Range): Stream[Info[Color]]
    def text_color(snapshot: Snapshot, range: Range, color: Color): Stream[Info[Color]]
    def tooltip(snapshot: Snapshot, range: Range): Option[String]
    def token_markup(syntax: Outer_Syntax, token: Token): Byte
  }

  /* plugin instance */

  var plugin: EBPlugin = null
  var rendering: Rendering = null

  /* properties */

  val OPTION_PREFIX = "options.pide."

  object Property
  {
    def apply(name: String): String =
      jEdit.getProperty(OPTION_PREFIX + name)
    def apply(name: String, default: String): String =
      jEdit.getProperty(OPTION_PREFIX + name, default)
    def update(name: String, value: String) =
      jEdit.setProperty(OPTION_PREFIX + name, value)
  }

  object Boolean_Property
  {
    def apply(name: String): Boolean =
      jEdit.getBooleanProperty(OPTION_PREFIX + name)
    def apply(name: String, default: Boolean): Boolean =
      jEdit.getBooleanProperty(OPTION_PREFIX + name, default)
    def update(name: String, value: Boolean) =
      jEdit.setBooleanProperty(OPTION_PREFIX + name, value)
  }

  object Int_Property
  {
    def apply(name: String): Int =
      jEdit.getIntegerProperty(OPTION_PREFIX + name)
    def apply(name: String, default: Int): Int =
      jEdit.getIntegerProperty(OPTION_PREFIX + name, default)
    def update(name: String, value: Int) =
      jEdit.setIntegerProperty(OPTION_PREFIX + name, value)
  }

  object Double_Property
  {
    def apply(name: String): Double =
      jEdit.getDoubleProperty(OPTION_PREFIX + name, 0.0)
    def apply(name: String, default: Double): Double =
      jEdit.getDoubleProperty(OPTION_PREFIX + name, default)
    def update(name: String, value: Double) =
      jEdit.setDoubleProperty(OPTION_PREFIX + name, value)
  }

  object Time_Property
  {
    def apply(name: String): Time =
      Time.seconds(Double_Property(name))
    def apply(name: String, default: Time): Time =
      Time.seconds(Double_Property(name, default.seconds))
    def update(name: String, value: Time) =
      Double_Property.update(name, value.seconds)
  }


  /* font */

  def font_family(): String = jEdit.getProperty("view.font") /* TODO: default*/

  def font_size(): Float =
    (jEdit.getIntegerProperty("view.fontsize", 16) *
      Int_Property("relative-font-size", 100)).toFloat / 100


  /* tooltip markup */

  def tooltip(text: String): String =
    "<html><pre style=\"font-family: " + font_family() + "; font-size: " +
        Int_Property("tooltip-font-size", 10).toString + "px; \">" +  // FIXME proper scaling (!?)
      HTML.encode(text) + "</pre></html>"

  private val tooltip_lb = Time.seconds(0.5)
  private val tooltip_ub = Time.seconds(60.0)
  def tooltip_dismiss_delay(): Time =
    Time_Property("tooltip-dismiss-delay", Time.seconds(8.0)) max tooltip_lb min tooltip_ub

  def setup_tooltips()
  {
    Swing_Thread.now {
      val manager = javax.swing.ToolTipManager.sharedInstance
      manager.setDismissDelay(tooltip_dismiss_delay().ms.toInt)
    }
  }


  /* icons */

  def load_icon(name: String): javax.swing.Icon =
  {
    val icon = GUIUtilities.loadIcon(name)
    if (icon.getIconWidth < 0 || icon.getIconHeight < 0)
      Log.log(Log.ERROR, icon, "Bad icon: " + name)
    icon
  }


  /* buffers */

  def swing_buffer_lock[A](buffer: JEditBuffer)(body: => A): A =
    Swing_Thread.now { buffer_lock(buffer) { body } }

  def buffer_text(buffer: JEditBuffer): String =
    buffer_lock(buffer) { buffer.getText(0, buffer.getLength) }

  def buffer_name(buffer: Buffer): String = buffer.getSymlinkPath


  /* main jEdit components */

  def jedit_buffers(): Iterator[Buffer] = jEdit.getBuffers().iterator

  def jedit_buffer(name: String): Option[Buffer] =
    jedit_buffers().find(buffer => buffer_name(buffer) == name)

  def jedit_views(): Iterator[View] = jEdit.getViews().iterator

  def jedit_text_areas(view: View): Iterator[JEditTextArea] =
    view.getEditPanes().iterator.map(_.getTextArea)

  def jedit_text_areas(): Iterator[JEditTextArea] =
    jedit_views().flatMap(jedit_text_areas(_))

  def jedit_text_areas(buffer: JEditBuffer): Iterator[JEditTextArea] =
    jedit_text_areas().filter(_.getBuffer == buffer)

  def buffer_lock[A](buffer: JEditBuffer)(body: => A): A =
  {
    try { buffer.readLock(); body }
    finally { buffer.readUnlock() }
  }


  /* document model and view */

  def document_model(buffer: Buffer): Option[Document_Model] = Document_Model(buffer)

  def document_view(text_area: JEditTextArea): Option[Document_View] = Document_View(text_area)

  def document_views(buffer: Buffer): List[Document_View] =
    for {
      text_area <- jedit_text_areas(buffer).toList
      doc_view = document_view(text_area)
      if doc_view.isDefined
    } yield doc_view.get

  def exit_model(buffer: Buffer)
  {
    swing_buffer_lock(buffer) {
      jedit_text_areas(buffer).foreach(Document_View.exit)
      Document_Model.exit(buffer)
    }
  }

  def init_model(buffer: Buffer)
  {
    swing_buffer_lock(buffer) {
      val opt_model =
      {
        val name = buffer_name(buffer)
        if (name.endsWith(Prover.extension)) {
          val node_name = Document.Node.Name(name, buffer.getDirectory, name)
          document_model(buffer) match {
            case Some(model) if model.name == node_name => Some(model)
            case _ => Some(Document_Model.init(Prover.session, buffer, node_name))
          }
        }
        else None
      }
      if (opt_model.isDefined) {
        for (text_area <- jedit_text_areas(buffer)) {
          if (document_view(text_area).map(_.model) != opt_model)
            Document_View.init(opt_model.get, text_area)
        }
      }
    }
  }

  def init_view(buffer: Buffer, text_area: JEditTextArea)
  {
    swing_buffer_lock(buffer) {
      document_model(buffer) match {
        case Some(model) => Document_View.init(model, text_area)
        case None =>
      }
    }
  }

  def exit_view(buffer: Buffer, text_area: JEditTextArea)
  {
    swing_buffer_lock(buffer) {
      Document_View.exit(text_area)
    }
  }


  /* dockable windows */

  private def wm(view: View): DockableWindowManager = view.getDockableWindowManager

  def docked_session(view: View): Option[Session_Dockable] =
    wm(view).getDockableWindow("isabelle-session") match {
      case dockable: Session_Dockable => Some(dockable)
      case _ => None
    }

  def docked_output(view: View): Option[Output_Dockable] =
    wm(view).getDockableWindow("isabelle-output") match {
      case dockable: Output_Dockable => Some(dockable)
      case _ => None
    }

  def docked_raw_output(view: View): Option[Raw_Output_Dockable] =
    wm(view).getDockableWindow("isabelle-raw-output") match {
      case dockable: Raw_Output_Dockable => Some(dockable)
      case _ => None
    }

  def docked_protocol(view: View): Option[Protocol_Dockable] =
    wm(view).getDockableWindow("isabelle-protocol") match {
      case dockable: Protocol_Dockable => Some(dockable)
      case _ => None
    }


  /* logic image */

  def default_logic(): String = "CIC"

  class Logic_Entry(val name: String, val description: String)
  {
    override def toString = description
  }

  def logic_selector(logic: String): ComboBox[Logic_Entry] =
  {
    val entries = new Logic_Entry("", "default (" + default_logic() + ")") :: Nil
    val component = new ComboBox(entries)
    entries.find(_.name == logic) match {
      case None =>
      case Some(entry) => component.selection.item = entry
    }
    component.tooltip = "Isabelle logic image"
    component
  }

  /* convenience actions */

  private def user_input(text_area: JEditTextArea, s1: String, s2: String = "")
  {
    s1.foreach(text_area.userInput(_))
    s2.foreach(text_area.userInput(_))
    s2.foreach(_ => text_area.goToPrevCharacter(false))
  }

  def input_sub(text_area: JEditTextArea): Unit = user_input(text_area, Symbol.sub_decoded)
  def input_sup(text_area: JEditTextArea): Unit = user_input(text_area, Symbol.sup_decoded)
  def input_isub(text_area: JEditTextArea): Unit = user_input(text_area, Symbol.isub_decoded)
  def input_isup(text_area: JEditTextArea): Unit = user_input(text_area, Symbol.isup_decoded)
  def input_bsub(text_area: JEditTextArea): Unit = user_input(text_area, Symbol.bsub_decoded, Symbol.esub_decoded)
  def input_bsup(text_area: JEditTextArea): Unit = user_input(text_area, Symbol.bsup_decoded, Symbol.esup_decoded)
  def input_bold(text_area: JEditTextArea): Unit = user_input(text_area, Symbol.bold_decoded)

  def check_buffer(buffer: Buffer)
  {
    document_model(buffer) match {
      case None =>
      case Some(model) => model.full_perspective()
    }
  }

}

