/*  Title:      Pure/System/system_channel.scala
    Author:     Makarius, Enrico

Portable system channel for inter-process communication, based on
named pipes or sockets. 
Interface with the slave process is given by slave_args, that can be one 
of the following:

  -channel-fifo fifo_m2s fifo_s2m
  -channel-socket master_host master_port

*/

package pide


import java.io.{InputStream, OutputStream, File, FileInputStream, FileOutputStream, IOException}
import java.net.{ServerSocket, InetAddress}


object System_Channel {
  def apply(use_socket: Boolean): System_Channel =
    if (Platform.is_windows || use_socket) new Socket_Channel
    else new Fifo_Channel
}

abstract class System_Channel {
  def slave_args: List[String]
  def rendezvous(): (OutputStream, InputStream)
  def accepted(): Unit
}


/** named pipes **/

private object Fifo_Channel {
  private val next_fifo = Counter()

  def mk_fifo(): String = {
    val i = next_fifo()
    val fifo = "/tmp/pide-fifo" + i
    val proc = new ProcessBuilder("mkfifo", "-m", "600", fifo)
    val rc = proc.start().waitFor()
    if (rc == 0) fifo
    else error("Unable to make fifo " + fifo)
  }

  def rm_fifo(fifo: String): Boolean = new File(fifo).delete
}

private class Fifo_Channel extends System_Channel {
  private val fifo1 = Fifo_Channel.mk_fifo()
  private val fifo2 = Fifo_Channel.mk_fifo()

  val slave_args: List[String] = List("-channel-fifo", fifo1, fifo2)

  def rendezvous(): (OutputStream, InputStream) =
    (new FileOutputStream(fifo1), new FileInputStream(fifo2))

  def accepted() = { Fifo_Channel.rm_fifo(fifo1); Fifo_Channel.rm_fifo(fifo2) }
}


/** sockets **/
// TODO: do not hardcode localhost, use the server name

private class Socket_Channel extends System_Channel {
  private val server =
    new ServerSocket(0, 2, InetAddress.getByName("127.0.0.1"))

  def slave_args: List[String] =
    List("-channel-socket", "127.0.0.1", server.getLocalPort().toString)

  def rendezvous(): (OutputStream, InputStream) = {
    val socket = server.accept
    (socket.getOutputStream, socket.getInputStream)
  }

  def accepted() { server.close }
}
