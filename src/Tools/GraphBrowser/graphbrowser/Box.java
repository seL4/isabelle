/***************************************************************************
  Title:      graphbrowser/Box.java
  Author:     Gerwin Klein, TU Muenchen

  A box with width and height. Used instead of java.awt.Dimension for 
  batch mode.

***************************************************************************/

package isabelle.graphbrowser;

public class Box {
  public int width;
  public int height;

  public Box(int w, int h) {
    this.width = w;
    this.height = h;
  }
}
