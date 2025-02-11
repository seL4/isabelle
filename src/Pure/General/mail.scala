/*  Title:      Pure/General/mail.scala
    Author:     Fabian Huch, TU Muenchen

Support for sending text mails via SMTP.
*/

package isabelle


import java.util.{Properties => JProperties}
import jakarta.mail.internet.{InternetAddress, MimeMessage}
import jakarta.mail.{Authenticator, Message, PasswordAuthentication, Transport => JTransport,
  Session => JSession}


object Mail {
  /* validated addresses */

  final class Address private[Mail](rep: String) {
    override def toString: String = rep
  }

  val default_address: Address = address("user@localhost")
  def address(s: String): Address =
    Exn.capture(new InternetAddress(s).validate()) match {
      case Exn.Res(_) => new Address(s)
      case _ => error("Invalid mail address: " + quote(s))
    }


  /* smtp server */

  enum Transport {
    case Plaintext extends Transport
    case SSL(protocol: String = "TLSv1.2") extends Transport
    case STARTTLS extends Transport
  }

  class Server (
    sender: Address,
    smtp_host: String,
    smtp_port: Int = 587,
    user: String = "",
    password: String = "",
    transport: Transport = Transport.SSL()
  ) {
    def use_auth: Boolean = user.nonEmpty && password.nonEmpty

    private def mail_session: JSession = {
      val props = new JProperties
      props.setProperty("mail.smtp.from", sender.toString)
      props.setProperty("mail.smtp.host", smtp_host)
      props.setProperty("mail.smtp.port", smtp_port.toString)
      props.setProperty("mail.smtp.auth", use_auth.toString)

      transport match {
        case Transport.SSL(protocol) =>
          props.setProperty("mail.smtp.ssl.enable", "true")
          props.setProperty("mail.smtp.ssl.protocols", protocol)
        case Transport.STARTTLS =>
          props.setProperty("mail.smtp.starttls.enable", "true")
        case Transport.Plaintext =>
      }

      val authenticator = new Authenticator() {
        override def getPasswordAuthentication = new PasswordAuthentication(user, password)
      }
      JSession.getInstance(props, authenticator)
    }

    def defined: Boolean = smtp_host.nonEmpty
    def check(): Unit = {
      val transport = mail_session.getTransport("smtp")
      try {
        transport.connect(smtp_host, smtp_port,
          if (user.nonEmpty) user else null, if (password.nonEmpty) password else null)
        transport.close()
      }
      catch {
        case exn: Throwable => error("Could not connect to SMTP server: " + exn.getMessage)
      }
    }

    def send(mail: Mail): Unit = {
      val from_address = mail.from_address.getOrElse(sender)
      val from =
        if (mail.from_name.isEmpty) new InternetAddress(from_address.toString)
        else new InternetAddress(from_address.toString, mail.from_name)

      val message = new MimeMessage(mail_session)
      message.setFrom(from)
      message.setSender(new InternetAddress(sender.toString))
      message.setSubject(mail.subject)
      message.setText(mail.content, "UTF-8")
      message.setSentDate(new java.util.Date())

      for (recipient <- mail.recipients) {
        message.addRecipient(Message.RecipientType.TO, new InternetAddress(recipient.toString))
      }

      try { JTransport.send(message) }
      catch { case exn: Throwable => error("Sending mail failed: " + exn.getMessage) }
    }
  }
}

case class Mail(
  subject: String,
  recipients: List[Mail.Address],
  content: String,
  from_address: Option[Mail.Address] = None,
  from_name: String = "")
