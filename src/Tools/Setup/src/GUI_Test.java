/*  Title:      Tools/Setup/src/GUI_Test.java
    Author:     Makarius

Minimal GUI test as main application entry-point.
*/

package isabelle.setup;

import javax.swing.SwingUtilities;
import javax.swing.JOptionPane;


public class GUI_Test
{
    public static void main(String[] args)
    {
        try {
            SwingUtilities.invokeAndWait(() ->
                JOptionPane.showMessageDialog(null, "Test", "Dialog", JOptionPane.PLAIN_MESSAGE));
        }
        catch (Exception e) {
            e.printStackTrace();
        }
    }
}
