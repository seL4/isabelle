/*
 * $Id$
 */

package isabelle;

import java.io.*;
import java.util.ArrayList;
import java.util.Locale;
import java.util.concurrent.LinkedBlockingQueue;

/**
 * Posix process wrapper for Isabelle (see also <code>src/Pure/Tools/isabelle_process.ML</code>).
 * <p>
 * 
 * The process model:
 * <p>
 *
 * <ol>
 * <li> input
 * <ul>
 * <li> stdin stream
 * <li> signals (interrupt, kill)
 * </ul>
 *
 * <li> output/results
 * <ul>
 * <li> stdout stream, interspersed with marked Isabelle messages
 * <li> stderr stream
 * <li> process exit (return code)
 * </ul>
 * </ol>
 * 
 * I/O is fully asynchronous, with unrestricted buffers.  Text is encoded as UTF-8.
 * <p>
 * 
 * System properties:
 * <p>
 * 
 * <dl>
 * <dt> <code>isabelle.home</code>  <di> <code>ISABELLE_HOME</code> of Isabelle installation
 *                      (default determined from isabelle-process via <code>PATH</code>)
 * <dt> <code>isabelle.shell</code> <di> optional shell command for <code>isabelle-process</code> (also requires isabelle.home)
 * <dt> <code>isabelle.kill</code>  <di> optional kill command (default <code>kill</code>)
 */

public class IsabelleProcess {
    private volatile Process proc = null;
    private volatile String pid = null;
    private volatile boolean closing = false;
    private LinkedBlockingQueue<String> output = null;


    /**
     * Models failures in process management.
     */
    public static class IsabelleProcessException extends Exception {
        public IsabelleProcessException() {
            super();
        }
        public IsabelleProcessException(String msg) {
            super(msg);
        }
    };


    /**
     * Models cooked results from the process.
     */
    public static class Result {
        public enum Kind {
            STDIN, STDOUT, STDERR, SIGNAL, EXIT,                        // Posix channels/events
            WRITELN, PRIORITY, TRACING, WARNING, ERROR, DEBUG, PROMPT,  // Isabelle messages
            SYSTEM                                                      // internal system notification
        };
        public Kind kind;
        public String result;

        public Result(Kind kind, String result) {
            this.kind = kind;
            this.result = result;
        }

        public boolean isRaw() {
            return
              this.kind == Kind.STDOUT ||
              this.kind == Kind.STDERR;
        }

        public boolean isSystem() {
            return
              this.kind == Kind.STDIN ||
              this.kind == Kind.SIGNAL ||
              this.kind == Kind.EXIT ||
              this.kind == Kind.PROMPT ||
              this.kind == Kind.SYSTEM;
        }

        public String toString() {
            return this.kind.toString() + " [[" + this.result + "]]";
        }
    }


    /**
     * Main result queue -- accumulates cooked messages asynchronously.
     */
    public LinkedBlockingQueue<Result> results;

    private synchronized void putResult(Result.Kind kind, String result) {
        try {
            results.put(new Result(kind, result));
        } catch (InterruptedException exn) {  }
    }


    /**
     * Interrupts Isabelle process via Posix signal.
     * @throws isabelle.IsabelleProcess.IsabelleProcessException
     */
    public synchronized void interrupt() throws IsabelleProcessException
    {
        if (proc != null && pid != null) {
            String kill = System.getProperty("isabelle.kill", "kill");
            String [] cmdline = {kill, "-INT", pid};
            try {
                putResult(Result.Kind.SIGNAL, "INT");
                int rc = Runtime.getRuntime().exec(cmdline).waitFor();
                if (rc != 0) {
                    throw new IsabelleProcessException("Cannot interrupt: kill command failed");
                }
            } catch (IOException exn) {
                throw new IsabelleProcessException(exn.getMessage());
            } catch (InterruptedException exn) {
                throw new IsabelleProcessException("Cannot interrupt: aborted");
            }
        } else {
            throw new IsabelleProcessException("Cannot interrupt: no process");
        }
    }


    /**
     * Kills Isabelle process: try close -- sleep -- destroy.
     */
    public synchronized void kill() throws IsabelleProcessException
    {
        if (proc != null) {
            tryClose();
            try {
                Thread.sleep(300);
            } catch (InterruptedException exn) { }
            putResult(Result.Kind.SIGNAL, "KILL");
            proc.destroy();
            proc = null;
        } else {
            throw new IsabelleProcessException("Cannot kill: no process");
        }
    }


    /**
     * Auxiliary operation to encode text as Isabelle string token.
     */
    public static String encodeString(String str) {
        Locale locale = null;
        StringBuffer buf = new StringBuffer(100);
        int i;
        char c;

        buf.append("\"");
        for (i = 0; i < str.length(); i++) {
            c = str.charAt(i);
            if (c < 32 || c == '\\' || c == '\"') {
                buf.append(String.format(locale, "\\%03d", (int) c));
            } else {
                buf.append(c);
            }
        }
        buf.append("\"");
        return buf.toString();
    }


    /* output being piped into the process (stdin) */

    private volatile BufferedWriter outputWriter;
    private class OutputThread extends Thread
    {
        public void run()
        {
            while (outputWriter != null) {
                try {
                    String s = output.take();
                    if (s.equals("\u0000")) {
                        outputWriter.close();
                        outputWriter = null;
                    } else {
                        putResult(Result.Kind.STDIN, s);
                        outputWriter.write(s);
                        outputWriter.flush();
                    }
                } catch (InterruptedException exn) {
                    putResult(Result.Kind.SYSTEM, "Output thread interrupted");
                } catch (IOException exn) {
                    putResult(Result.Kind.SYSTEM, exn.getMessage());
                }
            }
            putResult(Result.Kind.SYSTEM, "Output thread terminated");
        }
    }
    private OutputThread outputThread;


    // public operations

    /**
     * Feeds arbitrary text into the process.
     */
    public synchronized void output(String text) throws IsabelleProcessException
    {
        if (proc != null && !closing) {
            try {
                output.put(text);
            } catch (InterruptedException ex) {
               throw new IsabelleProcessException("Cannot output: aborted");
            }
        } else if (proc == null) {
            throw new IsabelleProcessException("Cannot output: no process");
        } else {
            throw new IsabelleProcessException("Cannot output: already closing");
        }
    }

    /**
     * Closes Isabelle process input, causing termination eventually.
     */
    public synchronized void close() throws IsabelleProcessException
    {
        output("\u0000");
        closing = true;
        // FIXME watchdog/timeout
    }

    /**
     * Closes Isabelle process input, causing termination eventually -- unless process already terminated.
     */
    public synchronized void tryClose()
    {
        if (proc != null && !closing) {
            try {
                close();
            } catch (IsabelleProcessException ex) {  }
        }
    }

    private synchronized void outputSync(String text) throws IsabelleProcessException
    {
        output(" \\<^sync>\n; " + text + " \\<^sync>;\n");
    }

    /**
     * Feeds exactly one Isabelle command into the process. 
     */
    public synchronized void command(String text) throws IsabelleProcessException
    {
        outputSync("Isabelle.command " + encodeString(text));
    }

    /**
     * Feeds ML toplevel declarations into the process.
     */
    public synchronized void ML(String text) throws IsabelleProcessException
    {
        outputSync("ML " + encodeString(text));
    }


    /* input from the process (stdout/stderr) */

    private volatile BufferedReader inputReader;
    private class InputThread extends Thread
    {
        public void run()
        {
            Result.Kind kind = Result.Kind.STDOUT;
            StringBuffer buf = new StringBuffer(100);

            try {
                while (inputReader != null) {
                    if (kind == Result.Kind.STDOUT && pid != null) {
                        // char mode
                        int c = -1;
                        while ((buf.length() == 0 || inputReader.ready()) &&
                                  (c = inputReader.read()) > 0 && c != 2) {
                            buf.append((char) c);
                        }
                        if (buf.length() > 0) {
                            putResult(kind, buf.toString());
                            buf = new StringBuffer(100);
                        }
                        if (c == 2) {
                            c = inputReader.read();
                            switch (c) {
                                case 'A': kind = Result.Kind.WRITELN; break;
                                case 'B': kind = Result.Kind.PRIORITY; break;
                                case 'C': kind = Result.Kind.TRACING; break;
                                case 'D': kind = Result.Kind.WARNING; break;
                                case 'E': kind = Result.Kind.ERROR; break;
                                case 'F': kind = Result.Kind.DEBUG; break;
                                case 'G': kind = Result.Kind.PROMPT; break;
                                default: kind = Result.Kind.STDOUT; break;
                            }
                        }
                        if (c == -1) {
                            inputReader.close();
                            inputReader = null;
                            tryClose();
                        }
                    } else {
                        // line mode
                        String line = null;
                        if ((line = inputReader.readLine()) != null) {
                            if (pid == null && kind == Result.Kind.STDOUT && line.startsWith("PID=")) {
                                pid = line.substring("PID=".length());
                            } else if (kind == Result.Kind.STDOUT) {
                                buf.append(line);
                                buf.append("\n");
                                putResult(kind, buf.toString());
                                buf = new StringBuffer(100);
                            } else {
                                int len = line.length();
                                if (len >= 2 && line.charAt(len - 2) == 2 && line.charAt(len - 1) == '.') {
                                    buf.append(line.substring(0, len - 2));
                                    putResult(kind, buf.toString());
                                    buf = new StringBuffer(100);
                                    kind = Result.Kind.STDOUT;
                                } else {
                                    buf.append(line);
                                    buf.append("\n");
                                }
                            }
                        } else {
                            inputReader.close();
                            inputReader = null;
                            tryClose();
                        }
                    }
                }
            } catch (IOException exn) {
                putResult(Result.Kind.SYSTEM, exn.getMessage());
            }
            putResult(Result.Kind.SYSTEM, "Input thread terminated");
        }
    }
    private InputThread inputThread;

    private volatile BufferedReader errorReader;
    private class ErrorThread extends Thread
    {
        public void run()
        {
            try {
                while (errorReader != null) {
                    StringBuffer buf = new StringBuffer(100);
                    int c;
                    while ((buf.length() == 0 || errorReader.ready()) && (c = errorReader.read()) > 0) {
                        buf.append((char) c);
                    }
                    if (buf.length() > 0) {
                        putResult(Result.Kind.STDERR, buf.toString());
                    } else {
                        errorReader.close();
                        errorReader = null;
                        tryClose();
                    }
                }
            } catch (IOException exn) {
                putResult(Result.Kind.SYSTEM, exn.getMessage());
            }
            putResult(Result.Kind.SYSTEM, "Error thread terminated");
        }
    }
    private ErrorThread errorThread;


    /* exit thread */

    private class ExitThread extends Thread
    {
        public void run()
        {
            try {
                int rc = proc.waitFor();
                Thread.sleep(300);
                putResult(Result.Kind.SYSTEM, "Exit thread terminated");
                putResult(Result.Kind.EXIT, Integer.toString(rc));
                proc = null;
            } catch (InterruptedException exn) {
                putResult(Result.Kind.SYSTEM, "Exit thread interrupted");
            }
        }
    }
    private ExitThread exitThread;


    /**
     * Creates Isabelle process with specified logic image.
     */
    public IsabelleProcess(String logic) throws IsabelleProcessException
    {
        ArrayList<String> cmdline = new ArrayList<String> ();
        String shell = null;
        String home = null;
        String charset = "UTF-8";

        shell = System.getProperty("isabelle.shell");
        home = System.getProperty("isabelle.home");
        if (shell != null && home != null) {
            cmdline.add(shell);
            cmdline.add(home +  "/bin/isabelle-process");
        } else if (home != null) {
            cmdline.add(home +  "/bin/isabelle-process");
        } else if (shell != null) {
            throw new IsabelleProcessException("Cannot start process: isabelle.shell property requires isabelle.home");
        } else {
            cmdline.add("isabelle-process");
        }
        cmdline.add("-W");
        if (logic != null) cmdline.add(logic);

        try {
            String [] cmd = new String[cmdline.size()];
            cmdline.toArray(cmd);
            proc = Runtime.getRuntime().exec(cmd);
        } catch (IOException exn) {
            throw new IsabelleProcessException(exn.getMessage());
        }

        try {
            outputWriter = new BufferedWriter(new OutputStreamWriter(proc.getOutputStream(), charset));
            inputReader = new BufferedReader(new InputStreamReader(proc.getInputStream(), charset));
            errorReader = new BufferedReader(new InputStreamReader(proc.getErrorStream(), charset));
        } catch (UnsupportedEncodingException exn) {
            proc.destroy();
            throw new Error(exn.getMessage());
        }

        output = new LinkedBlockingQueue<String>();
        outputThread = new OutputThread();

        results = new LinkedBlockingQueue<Result>();
        inputThread = new InputThread();
        errorThread = new ErrorThread();
        exitThread = new ExitThread();

        outputThread.start();
        inputThread.start();
        errorThread.start();
        exitThread.start();
    }
    
    /**
     * Creates Isabelle process with default logic image.
     */
    public IsabelleProcess() throws IsabelleProcessException {
        this(null);
    }
}
