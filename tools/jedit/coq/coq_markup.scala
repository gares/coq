/*  Title:      Pure/PIDE/coq_markup.scala
    Author:     Makarius

Coq markup elements.
*/

package coq


object Coq_Markup
{
  /* position */

  val OFFSET = "offset"
  val END_OFFSET = "end_offset"
  val ID = "id"

  val POSITION_PROPERTIES = Set(OFFSET, END_OFFSET, ID)
  val POSITION = "position"


  /* outer syntax */

  val COMMENT = "comment"
  val KEYWORD = "keyword"
  val DECLARATION = "declaration"
  val PROOF_DECLARATION = "proof_declaration"
  val QED = "qed"
  val STRING = "string"
  val DELIMITER = "delimiter"
  val UNTERMINATED = "unterminated"
}

