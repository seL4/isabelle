/*  Title:      Tools/Setup/src/Process.java
    Author:     Makarius
    Author:     Fabian Huch

Fundamental process operations.
*/

package isabelle.setup;


import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;


public class Process
{
    /* raw process */

    public static ProcessBuilder builder(
        List<String> cmd, java.io.File cwd, Map<String,String> env, boolean redirect)
    {
        ProcessBuilder builder = new ProcessBuilder();

        // fragile on Windows:
        // see https://docs.microsoft.com/en-us/cpp/cpp/main-function-command-line-args?view=msvc-160
        builder.command(cmd);

        if (cwd != null) builder.directory(cwd);
        if (env != null) {
            builder.environment().clear();
            builder.environment().putAll(env);
        }
        builder.redirectErrorStream(redirect);

        return builder;
    }

    public static class Exec_Result
    {
        private final int _rc;
        private final String _out;
        private final String _err;

        Exec_Result(int rc, String out, String err)
        {
            _rc = rc;
            _out = Library.trim_line(out);
            _err = Library.trim_line(err);
        }

        public int rc() { return _rc; }
        public boolean ok() { return _rc == 0; }
        public String out() { return _out; }
        public String err() { return _err; }
    }

    public static Exec_Result exec(
        List<String> command_line,
        java.io.File cwd,
        Map<String,String> env,
        boolean redirect) throws IOException, InterruptedException
    {
        Path out_file = Files.createTempFile(null, null);
        Path err_file = Files.createTempFile(null, null);
        Exec_Result res;
        try {
            ProcessBuilder builder = builder(command_line, cwd, env, redirect);
            builder.redirectOutput(out_file.toFile());
            builder.redirectError(err_file.toFile());

            java.lang.Process proc = builder.start();
            proc.getOutputStream().close();
            try { proc.waitFor(); }
            finally {
                proc.getInputStream().close();
                proc.getErrorStream().close();
                proc.destroy();
                Thread.interrupted();
            }

            int rc = proc.exitValue();
            String out = File.read(out_file);
            String err = File.read(err_file);
            res = new Exec_Result(rc, out, err);
        }
        finally {
            Files.deleteIfExists(out_file);
            Files.deleteIfExists(err_file);
        }
        return res;
    }


    /* kill process (via bash) */

    static public boolean kill(String group_pid, String signal)
        throws IOException, InterruptedException
    {
        List<String> cmd = new LinkedList<String>();
        if (Environment.is_windows()) {
            cmd.add(Environment.cygwin_root() + "\\bin\\bash.exe");
        }
        else {
            cmd.add("/usr/bin/env");
            cmd.add("bash");
        }
        cmd.add("-c");
        cmd.add("kill -" + signal + " -" + group_pid);
        return exec(cmd, null, null, false).ok();
    }
}
