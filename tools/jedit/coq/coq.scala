/*  Title:      Tools/jEdit/src/plugin.scala
    Author:     Makarius

Main Isabelle/jEdit plugin setup.
*/

/* The main class must be there! */
package pide.jedit
import pide._
import coq._

import java.lang.System
import java.awt.Font
import javax.swing.JOptionPane

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

import scala.actors.Actor._



class Plugin extends EBPlugin
{
  /* theory files */

  private lazy val delay_load =
    Swing_Thread.delay_last(Prover.session.load_delay)
    {
      val view = jEdit.getActiveView()

      val buffers = JEdit_Prover.jedit_buffers().toList
      if (buffers.forall(_.isLoaded)) {
        def loaded_buffer(name: String): Boolean =
          buffers.exists(buffer => JEdit_Prover.buffer_name(buffer) == name)

        val thys =
          for (buffer <- buffers; model <- JEdit_Prover.document_model(buffer))
            yield model.name

        // FIXME avoid I/O in Swing thread!?!
        val files = (Nil : List[String]) /*Prover.thy_info.dependencies(thys).map(_._1.node).
          filter(file => !loaded_buffer(file) && Prover.thy_load.check_file(view, file))*/

        if (!files.isEmpty) {
          val files_list = new ListView(files.sorted)
          for (i <- 0 until files.length)
            files_list.selection.indices += i

          val answer =
            JEdit_Library.confirm_dialog(view,
              "Auto loading of required files",
              JOptionPane.YES_NO_OPTION,
              "The following files are required to resolve theory imports.",
              "Reload selected files now?",
              new ScrollPane(files_list))
          if (answer == 0) {
            files.foreach(file =>
              if (files_list.selection.items.contains(file))
                jEdit.openFile(null: View, file))
          }
        }
      }
    }


  /* session manager */

  private val session_manager = actor {
    loop {
      react {
        case phase: Session.Phase =>
          phase match {
            case Session.Failed =>
              Swing_Thread.later {
                JEdit_Library.error_dialog(jEdit.getActiveView,
                  "Failed to start Isabelle process",
                    JEdit_Library.scrollable_text(Prover.session.current_syslog()))
              }

            case Session.Ready =>
              JEdit_Prover.jedit_buffers.foreach(JEdit_Prover.init_model)
              delay_load(true)

            case Session.Shutdown =>
              JEdit_Prover.jedit_buffers.foreach(JEdit_Prover.exit_model)
              delay_load(false)

            case _ =>
          }
        case bad => System.err.println("session_manager: ignoring bad message " + bad)
      }
    }
  }


  /* main plugin plumbing */

  override def handleMessage(message: EBMessage)
  {
    Swing_Thread.assert()
    message match {
      case msg: EditorStarted =>
        if (JEdit_Prover.Boolean_Property("auto-start"))
          Prover.start_session()

      case msg: BufferUpdate
      if msg.getWhat == BufferUpdate.LOADED || msg.getWhat == BufferUpdate.PROPERTIES_CHANGED =>
        if (Prover.session.is_ready) {
          val buffer = msg.getBuffer
          if (buffer != null && !buffer.isLoading) JEdit_Prover.init_model(buffer)
          delay_load(true)
        }

      case msg: EditPaneUpdate
      if (msg.getWhat == EditPaneUpdate.BUFFER_CHANGING ||
          msg.getWhat == EditPaneUpdate.BUFFER_CHANGED ||
          msg.getWhat == EditPaneUpdate.CREATED ||
          msg.getWhat == EditPaneUpdate.DESTROYED) =>
        val edit_pane = msg.getEditPane
        val buffer = edit_pane.getBuffer
        val text_area = edit_pane.getTextArea

        if (buffer != null && text_area != null) {
          if (msg.getWhat == EditPaneUpdate.BUFFER_CHANGED ||
              msg.getWhat == EditPaneUpdate.CREATED) {
            if (Prover.session.is_ready)
              JEdit_Prover.init_view(buffer, text_area)
          }
          else JEdit_Prover.exit_view(buffer, text_area)
        }

      case msg: PropertiesChanged =>
        JEdit_Prover.setup_tooltips()
        Prover.session.global_settings.event(Session.Global_Settings)

      case _ =>
    }
  }

  override def start()
  {
    org.gjt.sp.util.Log.log(org.gjt.sp.util.Log.ERROR,this,"starting...")
    Prover.extension = ".v"
    Prover.syntax = Coq_Syntax
    Prover.thy_load = new JEdit_Thy_Load(".v")
    //Isabelle_System.init()
    //Isabelle_System.install_fonts()
    Prover.session = new Session(
      program = "bin/pide", env = null, use_socket = true, 
      Prover.thy_load)
    JEdit_Prover.plugin = this
    JEdit_Prover.rendering = Coq_Rendering
    JEdit_Prover.setup_tooltips()
    // SyntaxUtilities.setStyleExtender(new Token_Markup.Style_Extender)
    if (ModeProvider.instance.isInstanceOf[ModeProvider]) {
      ModeProvider.instance =
        new Token_Markup.Mode_Provider(ModeProvider.instance)
    }
    Prover.session.phase_changed += session_manager
  }

  override def stop()
  {
    Prover.session.phase_changed -= session_manager
    JEdit_Prover.jedit_buffers.foreach(JEdit_Prover.exit_model)
    Prover.session.stop()
  }
}
