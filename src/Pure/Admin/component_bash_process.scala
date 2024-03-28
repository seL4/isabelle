/*  Title:      Pure/Admin/component_bash_process.scala
    Author:     Makarius

Build bash_process component from C source.
*/

package isabelle


object Component_Bash_Process {
  /* build bash_process */

  def build_bash_process(
    progress: Progress = new Progress,
    target_dir: Path = Path.current,
  ): Unit = {
    Isabelle_System.require_command("cc")


    /* component */

    val component_date = Date.Format.alt_date(Date.now())
    val component_name = "bash_process-" + component_date
    val component_dir =
      Components.Directory(target_dir + Path.basic(component_name)).create(progress = progress)

    component_dir.write_platforms()


    /* platform */

    val platform_name =
      proper_string(Isabelle_System.getenv("ISABELLE_APPLE_PLATFORM64")) orElse
      proper_string(Isabelle_System.getenv("ISABELLE_PLATFORM64")) getOrElse
      error("Missing ISABELLE_PLATFORM64")

    val platform_dir =
      Isabelle_System.make_directory(component_dir.path + Path.basic(platform_name))


    /* source */

    val source_file = Path.explode("bash_process.c")
    File.write(component_dir.path + source_file,
"""/*  Author:     Makarius
    License:    Isabelle BSD-3

Bash process with separate process group id.
*/

#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/resource.h>
#include <sys/time.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

static void fail(const char *msg)
{
  fprintf(stderr, "%s\n", msg);
  fflush(stderr);
  exit(2);
}

static time_t now()
{
  struct timeval tv;
  if (gettimeofday(&tv, NULL) == 0) {
    return tv.tv_sec * 1000 + tv.tv_usec / 1000;
  }
  else {
    return time(NULL) * 1000;
  }
}


int main(int argc, char *argv[])
{
  /* args */

  if (argc < 2) {
    fprintf(stderr, "Bad arguments: missing TIMING_FILE\n");
    fflush(stderr);
    exit(1);
  }
  char *timing_name = argv[1];


  /* potential fork */

  time_t time_start = now();

  if (strlen(timing_name) > 0 || setsid() == -1) {
    pid_t pid = fork();

    if (pid == -1) fail("Cannot set session id (failed to fork)");
    else if (pid != 0) {
      int status;

      // ingore SIGINT
      struct sigaction sa;
      memset(&sa, 0, sizeof(sa));
      sa.sa_handler = SIG_IGN;
      sigaction(SIGINT, &sa, 0);

      if (waitpid(pid, &status, 0) == -1) {
        fail("Cannot join forked process");
      }

      /* report timing */

      if (strlen(timing_name) > 0) {
        long long timing_elapsed = now() - time_start;

        struct rusage ru;
        getrusage(RUSAGE_CHILDREN, &ru);

        long long timing_cpu =
          ru.ru_utime.tv_sec * 1000 + ru.ru_utime.tv_usec / 1000 +
          ru.ru_stime.tv_sec * 1000 + ru.ru_stime.tv_usec / 1000;

        FILE *timing_file = fopen(timing_name, "w");
        if (timing_file == NULL) fail("Cannot open timing file");
        fprintf(timing_file, "%lld %lld", timing_elapsed, timing_cpu);
        fclose(timing_file);
      }

      if (WIFEXITED(status)) {
        exit(WEXITSTATUS(status));
      }
      else if (WIFSIGNALED(status)) {
        exit(128 + WTERMSIG(status));
      }
      else {
        fail("Unknown status of forked process");
      }
    }
    else if (setsid() == -1) fail("Cannot set session id (after fork)");
  }


  /* report pid */

  fprintf(stdout, "%d\n", getpid());
  fflush(stdout);


  /* shift command line */

  int i;
  for (i = 2; i < argc; i++) {
    argv[i - 2] = argv[i];
  }
  argv[argc - 2] = NULL;
  argv[argc - 1] = NULL;


  /* exec */

  execvp("bash", argv);
  fail("Cannot exec process");
}
""")


    /* build */

    progress.echo("Building bash_process for " + platform_name + " ...")
    progress.bash("cc ../bash_process.c -o bash_process", cwd = platform_dir.file).check


    /* settings */

    component_dir.write_settings("""
ISABELLE_BASH_PROCESS_HOME="$COMPONENT"
ISABELLE_BASH_PROCESS="$ISABELLE_BASH_PROCESS_HOME/${ISABELLE_APPLE_PLATFORM64:-$ISABELLE_PLATFORM64}/bash_process"
""")


    /* README */

    File.write(component_dir.README,
"""The bash_process executable has been built like this:

  cc -Wall bash_process.c -o bash_process


        Makarius
        """ + Date.Format.date(Date.now()) + "\n")
}


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("component_bash_process", "build bash_process component from C source",
      Scala_Project.here,
      { args =>
        var target_dir = Path.current

        val getopts = Getopts("""
Usage: isabelle component_bash_process [OPTIONS]

  Options are:
    -D DIR       target directory (default ".")

  Build prover component from official download.
""",
          "D:" -> (arg => target_dir = Path.explode(arg)))

        val more_args = getopts(args)
        if (more_args.nonEmpty) getopts.usage()

        val progress = new Console_Progress()

        build_bash_process(progress = progress, target_dir = target_dir)
      })
}
