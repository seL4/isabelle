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

        return msg;
    }
}
