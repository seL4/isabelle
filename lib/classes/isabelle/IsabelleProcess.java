/*
 * IsabelleProcess.java
 *
 * $Id$
 *
 */

import java.io.*;
import java.util.Locale;
import java.util.concurrent.LinkedBlockingQueue;

public class IsabelleProcess {
    private volatile Process proc;
    private volatile String pid;
    private volatile boolean closing = false;
    private LinkedBlockingQueue<String> output;

    /* exceptions */
    
    public static class IsabelleProcessException extends Exception {
	public IsabelleProcessException() {
            super();
	}
	public IsabelleProcessException(String msg) {
            super(msg);
	}
    };


    /* main result queue */
    
    public LinkedBlockingQueue<IsabelleResult> results;

    private synchronized void putResult(IsabelleResult.Kind kind, String result) {
        try {
            results.put(new IsabelleResult(kind, result));
        } catch (InterruptedException exn) {  }
    }

    
    /* encode arbitrary strings */
    
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


    /* interrupt process */

    public synchronized void interrupt() throws IsabelleProcessException
    {
        if (proc != null && pid != null) {
            try {
                int rc = Runtime.getRuntime().exec("kill -INT " + pid).waitFor();
                if (rc != 0) {
                    throw new IsabelleProcessException("Cannot interrupt: kill failed");
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


    /* terminate process */

    public synchronized void terminate()
    {
        // FIXME
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
                        outputWriter.close();    // FIXME timeout
                        outputWriter = null;
                    } else {
                        System.err.println(s);
                        outputWriter.write(s);
                        outputWriter.flush();
                    }
                } catch (InterruptedException exn) {
                    putResult(IsabelleResult.Kind.FAILURE, "Cannot output: aborted");
                } catch (IOException exn) {
                    putResult(IsabelleResult.Kind.FAILURE, exn.getMessage());
                }
            }
        }
    }
    private OutputThread outputThread;

    
    // public operations
    
    public synchronized void output(String text) throws IsabelleProcessException
    {
        if (!closing) {
            try {
                output.put(text);
            } catch (InterruptedException ex) {
               throw new IsabelleProcessException("Cannot output: aborted"); 
            }
        } else {
            throw new IsabelleProcessException("Cannot output: already closing");
        }
    }

    private synchronized void commandWrapping(String cmd, String text) throws IsabelleProcessException
    {
        output(" \\<^sync> " + cmd + " " + encodeString(text) + " \\<^sync>;\n");
    }

    public synchronized void command(String text) throws IsabelleProcessException
    {
        commandWrapping("Isabelle.command", text);
    }

    public synchronized void ML(String text) throws IsabelleProcessException
    {
        commandWrapping("ML", text);
    }

    public synchronized void close() throws IsabelleProcessException
    {
        output("\u0000");
        closing = true;
    }
    
    
    /* input being read from the process (stdout/stderr) */

    private volatile BufferedReader inputReader;
    private volatile BufferedReader errorReader;

    private synchronized void checkTermination()
    {
        if (inputReader == null && errorReader == null) {
            terminate();
        }
    }

    private class InputThread extends Thread
    {
        public void run()
        {
            IsabelleResult.Kind kind = IsabelleResult.Kind.STDOUT;
            StringBuffer buf = new StringBuffer(100);

            try {
                while (inputReader != null) {
                    if (kind == IsabelleResult.Kind.STDOUT && pid != null) {
                        // char mode
                        int c = 0;
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
                                case 'A': kind = IsabelleResult.Kind.WRITELN; break;
                                case 'B': kind = IsabelleResult.Kind.PRIORITY; break;
                                case 'C': kind = IsabelleResult.Kind.TRACING; break;
                                case 'D': kind = IsabelleResult.Kind.WARNING; break;
                                case 'E': kind = IsabelleResult.Kind.ERROR; break;
                                case 'F': kind = IsabelleResult.Kind.DEBUG; break;
                                default: kind = IsabelleResult.Kind.STDOUT; break;
                            }
                        }
                    } else {
                        // line mode
                        String line = null;
                        if ((line = inputReader.readLine()) != null) {
                            if (pid == null && kind == IsabelleResult.Kind.STDOUT && line.startsWith("PID=")) {
                                pid = line.substring("PID=".length());
                            } else if (kind == IsabelleResult.Kind.STDOUT) {
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
                                    kind = IsabelleResult.Kind.STDOUT;
                                } else {
                                    buf.append(line);
                                    buf.append("\n");
                                }
                            }
                        } else {
                            inputReader.close();
                            inputReader = null;
                            checkTermination();
                        }
                    }
                }
            } catch (IOException exn) {
                putResult(IsabelleResult.Kind.FAILURE, exn.getMessage());
            }
            System.err.println("Input thread terminated");
        }
    }
    private InputThread inputThread;

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
                        putResult(IsabelleResult.Kind.STDERR, buf.toString());
                    } else {
                        errorReader.close();
                        errorReader = null;
                        checkTermination();
                    }
                }
            } catch (IOException exn) {
                putResult(IsabelleResult.Kind.FAILURE, exn.getMessage());
            }
            System.err.println("Error thread terminated");
        }
    }
    private ErrorThread errorThread;
    
    
    /* console thread -- demo */

    private class ConsoleThread extends Thread
    {
        public void run()
        {
            IsabelleResult result = null;
            while (result == null || result.kind != IsabelleResult.Kind.EXIT) {
                try {
                    result = results.take();
                    System.err.println(result.toString());
                } catch (InterruptedException ex) {
                    putResult(IsabelleResult.Kind.FAILURE, "Cannot interrupt: aborted");
                }
            }
            System.err.println("Console thread terminated");
        }
    }
    private ConsoleThread consoleThread;


    /* create process */

    public IsabelleProcess(String logic) throws IsabelleProcessException
    {
        String [] cmdline = {"isabelle", "-W", logic};
        String charset = "UTF-8";
        try {
            proc = Runtime.getRuntime().exec(cmdline);
            pid = null;

            output = new LinkedBlockingQueue<String>();
            outputWriter = new BufferedWriter(new OutputStreamWriter(proc.getOutputStream(), charset));
            outputThread = new OutputThread();

            results = new LinkedBlockingQueue<IsabelleResult>();
            inputReader = new BufferedReader(new InputStreamReader(proc.getInputStream(), charset));
            errorReader = new BufferedReader(new InputStreamReader(proc.getErrorStream(), charset));
            inputThread = new InputThread();
            errorThread = new ErrorThread();
            
            consoleThread = new ConsoleThread();
        } catch (IOException exn) {
            terminate();
            throw new IsabelleProcessException(exn.getMessage());
        }

        outputThread.start();
        inputThread.start();
        errorThread.start();
        consoleThread.start();
    }
}
