/*  Title:      Pure/Tools/remote_dmg.scala
    Author:     Makarius

Build dmg on remote Mac OS X system.
*/

package isabelle


object Remote_DMG
{
  def remote_dmg(session: SSH.Session, tar_gz_file: Path, dmg_file: Path, volume_name: String = "")
  {
    session.with_tmp_dir(remote_dir =>
      using(session.sftp())(sftp =>
        {
          val cd = "cd " + File.bash_string(remote_dir) + "; "

          sftp.write_file(remote_dir + "/dmg.tar.gz", tar_gz_file)
          session.execute(cd + "mkdir root && tar -C root -xzf dmg.tar.gz").check
          session.execute(
            cd + "hdiutil create -srcfolder root" +
              (if (volume_name == "") "" else " -volname " + File.bash_string(volume_name)) +
              " dmg.dmg").check
          sftp.read_file(remote_dir + "/dmg.dmg", dmg_file)
        }))
  }


  /* Isabelle tool wrapper */

  val isabelle_tool = Isabelle_Tool("remote_dmg", "build dmg on remote Mac OS X system", args =>
  {
    Command_Line.tool0 {
      var port = SSH.default_port
      var volume_name = ""

      val getopts = Getopts("""
Usage: isabelle remote_dmg [OPTIONS] USER@HOST TAR_GZ_FILE DMG_FILE

  Options are:
    -p PORT      alternative SSH port (default: """ + SSH.default_port + """)
    -V NAME      specify volume name

  Turn the contents of a tar.gz file into a dmg file -- produced on a remote
  Mac OS X system.
""",
        "p:" -> (arg => port = Value.Int.parse(arg)),
        "V:" -> (arg => volume_name = arg))

      val more_args = getopts(args)
      val (user, host, tar_gz_file, dmg_file) =
        more_args match {
          case List(SSH.User_Host(user, host), tar_gz_file, dmg_file) =>
            (user, host, Path.explode(tar_gz_file), Path.explode(dmg_file))
          case _ => getopts.usage()
        }

      val ssh = SSH.init(Options.init)
      using(ssh.open_session(user = user, host = host, port = port))(
        remote_dmg(_, tar_gz_file, dmg_file, volume_name))
    }
  })
}
