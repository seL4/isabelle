/*  Title:      Pure/General/rsync.scala
    Author:     Makarius

Support for rsync, based on Isabelle component.
*/

package isabelle


object Rsync {
  def command_line(
    local_rsync: String = File.standard_path(Component_Rsync.program()),
    ssh_command: String = "",
    remote_rsync: String = "",
    verbose: Boolean = false,
    chmod: String = "",
    chown: String = "",
    archive: Boolean = true,
    thorough: Boolean = false,
    prune_empty_dirs: Boolean = false,
    dry_run: Boolean = false,
    clean: Boolean = false,
    filter: List[String] = Nil,
    args: List[String] = Nil
  ): String = {
    Bash.string(local_rsync) + " --secluded-args" +
      if_proper(ssh_command, " --rsh=" + Bash.string(ssh_command)) +
      if_proper(remote_rsync, " --rsync-path=" + Bash.string(Bash.string(remote_rsync))) +
      if_proper(chmod, " --chmod=" + Bash.string(chmod)) +
      if_proper(chown, " --chown=" + Bash.string(chown)) +
      if_proper(archive, " --archive") +
      if_proper(verbose, " --verbose --stats") +
      (if (thorough) " --ignore-times" else " --omit-dir-times") +
      if_proper(prune_empty_dirs, " --prune-empty-dirs") +
      if_proper(dry_run, " --dry-run") +
      if_proper(clean, " --delete-excluded") +
      filter.map(s => " --filter=" + Bash.string(s)).mkString +
      if_proper(args, " " + Bash.strings(args))
  }

  object Context {
    def apply(progress: Progress = new Progress, ssh: SSH.System = SSH.Local): Context = {
      val directory = Components.provide(Component_Rsync.home, ssh = ssh, progress = progress)
      new Context(directory.path, ssh, progress)
    }
  }

  final class Context private(base: Path, val ssh: SSH.System, val progress: Progress) {
    override def toString: String = base.toString + ssh.print

    def target(path: Path, direct: Boolean = false): String =
      Url.dir_path(ssh.rsync_path(path), direct = direct)

    def remote_rsync: String =
      ssh.standard_path(Component_Rsync.program(base = base, platform = ssh.isabelle_platform))

    def exec(
      chmod: String = "",
      chown: String = "",
      archive: Boolean = true,
      thorough: Boolean = false,
      prune_empty_dirs: Boolean = false,
      dry_run: Boolean = false,
      clean: Boolean = false,
      filter: List[String] = Nil,
      args: List[String] = Nil
    ): Process_Result = {
      val script =
        Rsync.command_line(
          ssh_command = ssh.client_command,
          remote_rsync = remote_rsync,
          verbose = progress.verbose,
          chmod = chmod,
          chown = chown,
          archive = archive,
          thorough = thorough,
          prune_empty_dirs = prune_empty_dirs,
          dry_run = dry_run,
          clean = clean,
          filter = filter,
          args = args)
      progress.bash(script, echo = true)
    }
  }
}
