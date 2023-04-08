/*  Title:      Pure/General/rsync.scala
    Author:     Makarius

Support for rsync: see also https://rsync.samba.org
*/

package isabelle


object Rsync {
  object Context {
    def apply(
      progress: Progress = new Progress,
      ssh: SSH.System = SSH.Local,
      archive: Boolean = true,
      protect_args: Boolean = true  // requires rsync 3.0.0, or later
    ): Context = {
      val directory = Components.provide(Component_Rsync.home, ssh = ssh, progress = progress)
      val remote_program = Component_Rsync.remote_program(directory)
      val rsync_path = quote(File.standard_path(remote_program))
      new Context(progress, ssh, rsync_path, archive, protect_args)
    }
  }

  final class Context private(
    val progress: Progress,
    val ssh: SSH.System,
    rsync_path: String,
    archive: Boolean,
    protect_args: Boolean,
  ) {
    def no_progress: Context = new Context(new Progress, ssh, rsync_path, archive, protect_args)
    def no_archive: Context = new Context(progress, ssh, rsync_path, false, protect_args)

    def command: String = {
      val ssh_command = ssh.client_command
      File.bash_path(Component_Rsync.local_program) +
        if_proper(ssh_command, " --rsh=" + Bash.string(ssh_command)) +
        " --rsync-path=" + Bash.string(rsync_path) +
        (if (archive) " --archive" else "") +
        (if (protect_args) " --protect-args" else "")
    }

    def target(path: Path, direct: Boolean = false): String = {
      val s = ssh.rsync_path(path)
      if (direct) Url.direct_path(s) else s
    }
  }

  def exec(
    context: Context,
    thorough: Boolean = false,
    prune_empty_dirs: Boolean = false,
    dry_run: Boolean = false,
    clean: Boolean = false,
    filter: List[String] = Nil,
    args: List[String] = Nil
  ): Process_Result = {
    val progress = context.progress
    val script =
      context.command +
        (if (progress.verbose) " --verbose" else "") +
        (if (thorough) " --ignore-times" else " --omit-dir-times") +
        (if (prune_empty_dirs) " --prune-empty-dirs" else "") +
        (if (dry_run) " --dry-run" else "") +
        (if (clean) " --delete-excluded" else "") +
        filter.map(s => " --filter=" + Bash.string(s)).mkString +
        if_proper(args, " " + Bash.strings(args))
    progress.bash(script, echo = true)
  }

  def init(context: Context, target: Path,
    contents: List[File.Content] = Nil
  ): Unit =
    Isabelle_System.with_tmp_dir("sync") { tmp_dir =>
      val init_dir = Isabelle_System.make_directory(tmp_dir + Path.explode("init"))
      contents.foreach(_.write(init_dir))
      exec(context.no_archive,
        thorough = true,
        args =
          List(if (contents.nonEmpty) "--archive" else "--dirs",
            File.bash_path(init_dir) + "/.", context.target(target))).check
    }
}
