/***************************************************************************
  Title:      GraphBrowser/Box.java
  ID:         $Id$
  Author:     Gerwin Klein, TU Muenchen
  Copyright   2003  TU Muenchen
  License:    GPL (GNU GENERAL PUBLIC LICENSE)

  A box with width and height. Used instead of java.awt.Dimension for 
  batch mode.

***************************************************************************/

package GraphBrowser;

public class Box {
  public int width;
  public int height;

  public Box(int w, int h) {
    this.width = w;
    this.height = h;
  }
}
