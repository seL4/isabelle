/*  Title:      Tools/Setup/isabelle/setup/Library.java
    Author:     Makarius

Basic library.
*/

package isabelle.setup;


import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;


public class Library
{
    public static String quote(String s)
    {
        return "\"" + s + "\"";
    }

    public static String cat_lines(Iterable<? extends CharSequence> lines)
    {
        return String.join("\n", lines);
    }

    public static List<String> split_lines(String str)
    {
        if (str.isEmpty()) { return List.of(); }
        else {
            List<String> result = new LinkedList<String>();
            result.addAll(Arrays.asList(str.split("\\n")));
            return List.copyOf(result);
        }
    }

    public static String prefix_lines(String prfx, String str)
    {
        if (str.isEmpty()) { return str; }
        else {
            List<String> lines = new LinkedList<String>();
            for (String line : split_lines(str)) { lines.add(prfx + line); }
            return cat_lines(lines);
        }
    }

    public static String trim_line(String s)
    {
        if (s.endsWith("\r\n")) { return s.substring(0, s.length() - 2); }
        else if (s.endsWith("\r") || s.endsWith("\n")) { return s.substring(0, s.length() - 1); }
        else { return s; }
    }
}