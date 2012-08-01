package pide

import java.lang.System

import scala.collection.mutable

import scala.actors.Actor._

object Prover
{
  abstract class Syntax {
    def text_edits(
      base_syntax: Outer_Syntax,
      previous: Document.Version,
      edits: List[Document.Edit_Text])
    : (List[Document.Edit_Command], Document.Version)
  }

  /* plugin instance */

  var session: Session = null
  var extension: String = null
  var syntax : Syntax = null

  var thy_load : Thy_Load = null
  //val thy_info = new Thy_Info(thy_load)


  def start_session()
  {
    val timeout = Time.seconds(5)
    session.start(timeout, Nil)
  }

  def cancel_execution() { session.cancel_execution() }
}

