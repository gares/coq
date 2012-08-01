/*  Title:      Tools/jEdit/src/jedit_thy_load.scala
    Author:     Makarius

Primitives for loading theory files, based on jEdit buffer content.
*/

package pide.jedit
import  pide._

import java.io.{File, IOException}
import javax.swing.text.Segment

import org.gjt.sp.jedit.io.{VFS, FileVFS, VFSFile, VFSManager}
import org.gjt.sp.jedit.MiscUtilities
import org.gjt.sp.jedit.View


class JEdit_Thy_Load(extension : String) extends Thy_Load(extension)
{
  override def append(dir: String, source_path: Path): String =
  {
    val path = source_path.expand
    if (path.is_absolute) Standard_System.platform_path(path)
    else {
      val vfs = VFSManager.getVFSForPath(dir)
      if (vfs.isInstanceOf[FileVFS])
        MiscUtilities.resolveSymlinks(
          vfs.constructPath(dir, Standard_System.platform_path(path)))
      else vfs.constructPath(dir, Standard_System.standard_path(path))
    }
  }

  def check_file(view: View, path: String): Boolean =
  {
    val vfs = VFSManager.getVFSForPath(path)
    val session = vfs.createVFSSession(path, view)

    try {
      session != null && {
        try {
          val file = vfs._getFile(session, path, view)
          file != null && file.isReadable && file.getType == VFSFile.FILE
        }
        catch { case _: IOException => false }
      }
    }
    finally {
      try { vfs._endVFSSession(session, view) }
      catch { case _: IOException => }
    }
  }

  override def read_header(name: Document.Node.Name): Thy_Header =
  {
    Swing_Thread.now {
      JEdit_Prover.jedit_buffer(name.node) match {
        case Some(buffer) =>
          JEdit_Prover.buffer_lock(buffer) {
            val text = new Segment
            buffer.getText(0, buffer.getLength, text)
            Some(Thy_Header.read(text))
          }
        case None => None
      }
    } getOrElse {
      val file = new File(name.node)  // FIXME load URL via jEdit VFS (!?)
      if (!file.exists || !file.isFile) error("No such file: " + quote(file.toString))
      Thy_Header.read(file)
    }
  }
}

