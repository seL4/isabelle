/*  Title:      Tools/Setup/src/GUI_Setup.scala
    Author:     Makarius

Platform-specific setup for Java/Swing GUI applications.
*/

package isabelle.setup;

import java.util.List;

import com.formdev.flatlaf.FlatLightLaf;
import com.formdev.flatlaf.util.UIScale;


public class GUI_Setup
{
    public static String gui_setup()
    {
        String msg = "";

        if (Environment.is_linux()) {
            if (FlatLightLaf.setup()) {
                int scale = (int) UIScale.getUserScaleFactor();
                if (scale > 1) { msg = "export GDK_SCALE=" + scale; }
            }
        }
        else if (Environment.is_macos()) {
            String java_domain = "com.azul.zulu." + System.getProperty("java.version") + ".java";
            if (!apple_tabbing_mode("read", java_domain)) {
                apple_tabbing_mode("write", java_domain);
            }
        }

        return msg;
    }

    public static boolean apple_tabbing_mode(String op, String domain)
    {
        List<String> cmd = java.util.List.of("defaults", op, domain, "AppleWindowTabbingMode");
        try { return Environment.exec_process(cmd, null, null, false).ok(); }
        catch (Exception e) { return false; }
    }
}
