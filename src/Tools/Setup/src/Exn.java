/*  Title:      Tools/Setup/src/Exn.java
    Author:     Makarius

Support for exceptions (arbitrary throwables).
*/

package isabelle.setup;


import java.io.IOException;
import java.util.LinkedList;
import java.util.List;


public class Exn
{
    /* interrupts */

    public static boolean is_interrupt(Throwable exn)
    {
        boolean found_interrupt = false;
        Throwable e = exn;
        while (!found_interrupt && e != null) {
            found_interrupt = e instanceof InterruptedException;
            e = e.getCause();
        }
        return found_interrupt;
    }

    public static int return_code(Throwable exn, int rc)
    {
        return is_interrupt(exn) ? 130 : rc;
    }


    /* message */

    public static String message(Throwable exn)
    {
        String msg = exn.getMessage();

        if (exn.getClass() == RuntimeException.class)
        {
            return msg == null || msg.isEmpty() ? "Error" : msg;
        }
        else if (exn instanceof IOException)
        {
            return msg == null || msg.isEmpty() ? "I/O error" : "I/O error: " + msg;
        }
        else if (exn instanceof RuntimeException && !msg.isEmpty()) { return msg; }
        else if (exn instanceof InterruptedException) { return "Interrupt"; }
        else { return exn.toString(); }
    }


    /* print */

    public static String trace(Throwable exn)
    {
        List<String> list = new LinkedList<String>();
        for (StackTraceElement elem : exn.getStackTrace()) {
            list.add(elem.toString());
        }
        return Library.cat_lines(list);
    }

    public static boolean debug()
    {
        return System.getProperty("isabelle.debug", "").equals("true");
    }

    public static String print(Throwable exn)
    {
        return debug() ? message(exn) + "\n" + trace(exn) : message(exn);
    }

    public static String print_error(Throwable exn)
    {
        return Library.prefix_lines("*** ", print(exn));
    }
}
