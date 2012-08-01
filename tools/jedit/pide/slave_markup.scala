/*  Title:      message_markup
    Author:     Enrico

Message specific markup, with short version
*/

package pide

object Slave_Markup {

  val ID = "id"

  /* protocol messages */

  val INIT = "init"
  val STATUS = "status"
  val REPORT = "report"
  val WRITELN = "writeln"
  val TRACING = "tracing"
  val WARNING = "warning"
  val ERROR = "error"
  val PROTOCOL = "protocol"

  val inflate = Map(
    ('A' : Int) -> INIT,
    ('B' : Int) -> STATUS,
    ('C' : Int) -> REPORT,
    ('D' : Int) -> WRITELN,
    ('E' : Int) -> TRACING,
    ('F' : Int) -> WARNING,
    ('G' : Int) -> ERROR,
    ('H' : Int) -> PROTOCOL)

  /* other protocol messages */

  val Serial = new Properties.Long("serial")

  val MESSAGE = "message"

  val SYSTEM = "system"
  val STDOUT = "stdout"
  val STDERR = "stderr"
  val EXIT = "exit"

  val LEGACY = "legacy"

  val NO_REPORT = "no_report"

  val BAD = "bad"

  /* interactive documents */

  val VERSION = "version"
  val ASSIGN = "assign"


  /* prover process */

  val PROVER_COMMAND = "prover_command"
  val PROVER_ARG = "prover_arg"
  
  /* command status */

  val TASK = "task"

  val ACCEPTED = "accepted"
  val FORKED = "forked"
  val JOINED = "joined"
  val FAILED = "failed"
  val FINISHED = "finished"
  
  /* position */

  val LINE = "line"
  val OFFSET = "offset"
  val END_OFFSET = "end_offset"
  val FILE = "file"

  val DEF_LINE = "def_line"
  val DEF_OFFSET = "def_offset"
  val DEF_END_OFFSET = "def_end_offset"
  val DEF_FILE = "def_file"
  val DEF_ID = "def_id"

  val POSITION_PROPERTIES = Set(LINE, OFFSET, END_OFFSET, FILE, ID)
  val POSITION = "position"

  /* protocol message functions */

  val FUNCTION = "function"
  val Function = new Properties.String(FUNCTION)

  val Ready: Properties.T = List((FUNCTION, "ready"))

  object Loaded_Theory
  {
    def unapply(props: Properties.T): Option[String] =
      props match {
        case List((FUNCTION, "loaded_theory"), (Markup.NAME, name)) => Some(name)
        case _ => None
      }
  }

  object Keyword_Decl
  {
    def unapply(props: Properties.T): Option[String] =
      props match {
        case List((FUNCTION, "keyword_decl"), (Markup.NAME, name)) => Some(name)
        case _ => None
      }
  }
  object Command_Decl
  {
    def unapply(props: Properties.T): Option[(String, String)] =
      props match {
        case List((FUNCTION, "command_decl"), (Markup.NAME, name), (Markup.KIND, kind)) =>
          Some((name, kind))
        case _ => None
      }
  }

  val Assign_Execs: Properties.T = List((FUNCTION, "assign_execs"))
  val Removed_Versions: Properties.T = List((FUNCTION, "removed_versions"))

  object Invoke_Scala
  {
    def unapply(props: Properties.T): Option[(String, String)] =
      props match {
        case List((FUNCTION, "invoke_scala"), (Markup.NAME, name), (ID, id)) => Some((name, id))
        case _ => None
      }
  }
  object Cancel_Scala
  {
    def unapply(props: Properties.T): Option[String] =
      props match {
        case List((FUNCTION, "cancel_scala"), (ID, id)) => Some(id)
        case _ => None
      }
  }

  /* path */

  val PATH = "path"

  object Path
  {
    def unapply(markup: Markup): Option[String] =
      markup match {
        case Markup(PATH, Markup.Name(name)) => Some(name)
        case _ => None
      }
  }

  /* pretty printing */

  val Indent = new Properties.Int("indent")
  val BLOCK = "block"
  val Width = new Properties.Int("width")
  val BREAK = "break"


}
