/*  Title:      Pure/PIDE/isabelle_markup.scala
    Author:     Makarius

Isabelle markup elements.
*/

package isabelle


object Isabelle_Markup
{
  /* formal entities */

  val BINDING = "binding"
  val ENTITY = "entity"
  val DEF = "def"
  val REF = "ref"

  object Entity
  {
    def unapply(markup: Markup): Option[(String, String)] =
      markup match {
        case Markup(ENTITY, props @ Markup.Kind(kind)) =>
          props match {
            case Markup.Name(name) => Some(kind, name)
            case _ => None
          }
        case _ => None
      }
  }

  /* logical entities */

  val CLASS = "class"
  val TYPE_NAME = "type name"
  val FIXED = "fixed"
  val CONSTANT = "constant"

  val DYNAMIC_FACT = "dynamic_fact"

  /* inner syntax */

  val TFREE = "tfree"
  val TVAR = "tvar"
  val FREE = "free"
  val SKOLEM = "skolem"
  val BOUND = "bound"
  val VAR = "var"
  val NUMERAL = "numeral"
  val LITERAL = "literal"
  val DELIMITER = "delimiter"
  val INNER_STRING = "inner_string"
  val INNER_COMMENT = "inner_comment"

  val TOKEN_RANGE = "token_range"

  val SORT = "sort"
  val TYP = "typ"
  val TERM = "term"
  val PROP = "prop"

  val TYPING = "typing"

  val ATTRIBUTE = "attribute"
  val METHOD = "method"


  /* embedded source text */

  val ML_SOURCE = "ML_source"
  val DOC_SOURCE = "doc_source"

  val ANTIQ = "antiq"
  val ML_ANTIQUOTATION = "ML antiquotation"
  val DOCUMENT_ANTIQUOTATION = "document antiquotation"
  val DOCUMENT_ANTIQUOTATION_OPTION = "document antiquotation option"


  /* ML syntax */

  val ML_KEYWORD = "ML_keyword"
  val ML_DELIMITER = "ML_delimiter"
  val ML_TVAR = "ML_tvar"
  val ML_NUMERAL = "ML_numeral"
  val ML_CHAR = "ML_char"
  val ML_STRING = "ML_string"
  val ML_COMMENT = "ML_comment"
  val ML_MALFORMED = "ML_malformed"

  val ML_DEF = "ML_def"
  val ML_OPEN = "ML_open"
  val ML_STRUCT = "ML_struct"
  val ML_TYPING = "ML_typing"


  /* outer syntax */

  val KEYWORD = "keyword"
  val OPERATOR = "operator"
  val COMMAND = "command"
  val STRING = "string"
  val ALTSTRING = "altstring"
  val VERBATIM = "verbatim"
  val COMMENT = "comment"
  val CONTROL = "control"
  val MALFORMED = "malformed"

  val COMMAND_SPAN = "command_span"
  val IGNORED_SPAN = "ignored_span"
  val MALFORMED_SPAN = "malformed_span"


  /* timing */

  val TIMING = "timing"
  val ELAPSED = "elapsed"
  val CPU = "cpu"
  val GC = "gc"

  object Timing
  {
    def apply(timing: isabelle.Timing): Markup =
      Markup(TIMING, List(
        (ELAPSED, Properties.Value.Double(timing.elapsed.seconds)),
        (CPU, Properties.Value.Double(timing.cpu.seconds)),
        (GC, Properties.Value.Double(timing.gc.seconds))))
    def unapply(markup: Markup): Option[isabelle.Timing] =
      markup match {
        case Markup(TIMING, List(
          (ELAPSED, Properties.Value.Double(elapsed)),
          (CPU, Properties.Value.Double(cpu)),
          (GC, Properties.Value.Double(gc)))) =>
            Some(new isabelle.Timing(Time.seconds(elapsed), Time.seconds(cpu), Time.seconds(gc)))
        case _ => None
      }
  }


  /* toplevel */

  val SUBGOALS = "subgoals"
  val PROOF_STATE = "proof_state"

  val STATE = "state"
  val SUBGOAL = "subgoal"
  val SENDBACK = "sendback"
  val HILITE = "hilite"

}

