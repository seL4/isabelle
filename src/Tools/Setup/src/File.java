/*  Title:      Tools/Setup/src/File.java
    Author:     Makarius
    Author:     Fabian Huch

Fundamental file operations.
*/

package isabelle.setup;


import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.function.BiFunction;
import java.util.regex.Matcher;
import java.util.regex.Pattern;


public class File {
    public static String read(Path path) throws IOException
    {
        return new String(Files.readAllBytes(path), StandardCharsets.UTF_8);
    }

    public static String join_platform_paths(List<Path> paths)
    {
        List<String> strs = new LinkedList<String>();
        for (Path p : paths) { strs.add(p.toString()); }
        return String.join(java.io.File.pathSeparator, strs);
    }

    public static String join_standard_paths(List<Path> paths)
        throws IOException, InterruptedException
    {
        List<String> strs = new LinkedList<String>();
        for (Path p : paths) { strs.add(Environment.standard_path(p.toString())); }
        return String.join(":", strs);
    }

    public static void cygwin_link(String content, java.io.File target) throws IOException
    {
        Path target_path = target.toPath();
        Files.writeString(target_path, "!<symlink>" + content + "\u0000");
        Files.setAttribute(target_path, "dos:system", true);
    }
}
