/*  Title:      Pure/Thy/thy_syntax.scala
    Author:     Makarius

Superficial theory syntax: tokens and spans.
*/

package pide


import scala.collection.mutable
import scala.annotation.tailrec


object Coq_Syntax extends Prover.Syntax
{
  /** parse spans **/  // FIXME

  def parse_spans(toks: List[Token]): List[List[Token]] = List(toks)


  /** perspective **/

  def command_perspective(node: Document.Node, perspective: Text.Perspective): Command.Perspective =
  {
    if (perspective.is_empty) Command.Perspective.empty
    else {
      val result = new mutable.ListBuffer[Command]
      @tailrec
      def check_ranges(ranges: List[Text.Range], commands: Stream[(Command, Text.Offset)])
      {
        (ranges, commands) match {
          case (range :: more_ranges, (command, offset) #:: more_commands) =>
            val command_range = command.range + offset
            range compare command_range match {
              case -1 => check_ranges(more_ranges, commands)
              case 0 =>
                result += command
                check_ranges(ranges, more_commands)
              case 1 => check_ranges(ranges, more_commands)
            }
          case _ =>
        }
      }
      check_ranges(perspective.ranges, node.command_range(perspective.range).toStream)
      Command.Perspective(result.toList)
    }
  }



  /** text edits **/

  /* edit individual command source */

  @tailrec private def edit_text(eds: List[Text.Edit], commands: Linear_Set[Command])
      : Linear_Set[Command] =
  {
    eds match {
      case e :: es =>
        Document.Node.command_starts(commands.iterator).find {
          case (cmd, cmd_start) =>
            e.can_edit(cmd.source, cmd_start) ||
              e.is_insert && e.start == cmd_start + cmd.length
        } match {
          case Some((cmd, cmd_start)) if e.can_edit(cmd.source, cmd_start) =>
            val (rest, text) = e.edit(cmd.source, cmd_start)
            val new_commands = commands.insert_after(Some(cmd), Command.unparsed(text)) - cmd
            edit_text(rest.toList ::: es, new_commands)

          case Some((cmd, cmd_start)) =>
            edit_text(es, commands.insert_after(Some(cmd), Command.unparsed(e.text)))

          case None =>
            require(e.is_insert && e.start == 0)
            edit_text(es, commands.insert_after(None, Command.unparsed(e.text)))
        }
      case Nil => commands
    }
  }


  /* reparse range of command spans */

  @tailrec private def chop_common(
      cmds: List[Command], spans: List[List[Token]]): (List[Command], List[List[Token]]) =
    (cmds, spans) match {
      case (c :: cs, s :: ss) if c.span == s => chop_common(cs, ss)
      case _ => (cmds, spans)
    }

  private def reparse_spans(
    syntax: Outer_Syntax,
    name: Document.Node.Name,
    commands: Linear_Set[Command],
    first: Command, last: Command): Linear_Set[Command] =
  {
    val cmds0 = commands.iterator(first, last).toList
    val spans0 = parse_spans(syntax.scan(cmds0.iterator.map(_.source).mkString))

    val (cmds1, spans1) = chop_common(cmds0, spans0)

    val (rev_cmds2, rev_spans2) = chop_common(cmds1.reverse, spans1.reverse)
    val cmds2 = rev_cmds2.reverse
    val spans2 = rev_spans2.reverse

    cmds2 match {
      case Nil =>
        assert(spans2.isEmpty)
        commands
      case cmd :: _ =>
        val hook = commands.prev(cmd)
        val inserted = spans2.map(span => Command(Document.new_id(), name, span))
        (commands /: cmds2)(_ - _).append_after(hook, inserted)
    }
  }


  /* recover command spans after edits */

  // FIXME somewhat slow
  private def recover_spans(
    syntax: Outer_Syntax,
    name: Document.Node.Name,
    perspective: Command.Perspective,
    commands: Linear_Set[Command]): Linear_Set[Command] =
  {
    val visible = perspective.commands.toSet

    def next_invisible_command(cmds: Linear_Set[Command], from: Command): Command =
      cmds.iterator(from).dropWhile(cmd => !cmd.is_command || visible(cmd))
        .find(_.is_command) getOrElse cmds.last

    @tailrec def recover(cmds: Linear_Set[Command]): Linear_Set[Command] =
      cmds.find(_.span.exists(_.is_unparsed)) match {
        case Some(first_unparsed) =>
          val first = next_invisible_command(cmds.reverse, first_unparsed)
          val last = next_invisible_command(cmds, first_unparsed)
          recover(reparse_spans(syntax, name, cmds, first, last))
        case None => cmds
      }
    recover(commands)
  }


  /* main */

  private def diff_commands(old_cmds: Linear_Set[Command], new_cmds: Linear_Set[Command])
    : List[(Option[Command], Option[Command])] =
  {
    val removed = old_cmds.iterator.filter(!new_cmds.contains(_)).toList
    val inserted = new_cmds.iterator.filter(!old_cmds.contains(_)).toList

    removed.reverse.map(cmd => (old_cmds.prev(cmd), None)) :::
    inserted.map(cmd => (new_cmds.prev(cmd), Some(cmd)))
  }

  private def text_edit(syntax: Outer_Syntax, node: Document.Node, edit: Document.Edit_Text)
    : Document.Node =
  {
    edit match {
      case (_, Document.Node.Clear()) => node.clear

      case (name, Document.Node.Edits(text_edits)) =>
        val commands0 = node.commands
        val commands1 = edit_text(text_edits, commands0)
        val commands2 = recover_spans(syntax, name, node.perspective, commands1)
        node.update_commands(commands2)

      case (_, Document.Node.Header(_)) => node

      case (name, Document.Node.Perspective(text_perspective)) =>
        val perspective = command_perspective(node, text_perspective)
        if (node.perspective same perspective) node
        else node.update_perspective(perspective)
    }
  }

  def text_edits(
      syntax: Outer_Syntax,
      previous: Document.Version,
      edits: List[Document.Edit_Text])
    : (List[Document.Edit_Command], Document.Version) =
  {
    var nodes = previous.nodes
    val doc_edits = new mutable.ListBuffer[Document.Edit_Command]

    val node_edits =
      edits.groupBy(_._1)
        .asInstanceOf[Map[Document.Node.Name, List[Document.Edit_Text]]]  // FIXME ???

    node_edits foreach {
      case (name, edits) =>
        val node = nodes(name)
        val commands = node.commands
        val node1 = (node /: edits)(text_edit(syntax, _, _))

        if (!(node.perspective same node1.perspective))
          doc_edits += (name -> Document.Node.Perspective(node1.perspective))

        doc_edits += (name -> Document.Node.Edits(diff_commands(commands, node1.commands)))

        nodes += (name -> node1)
    }

    (doc_edits.toList, Document.Version.make(syntax, nodes))
  }
}
