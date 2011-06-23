/*  Title:      Pure/System/Java_Ext_Dirs.java
    Author:     Makarius

Augment Java extension directories.
*/

package isabelle;

public class Java_Ext_Dirs
{
  public static void main(String [] args) {
    StringBuilder s = new StringBuilder();
    s.append(System.getProperty("java.ext.dirs"));
    int i;
    for (i = 0; i < args.length; i++) {
      s.append(System.getProperty("path.separator"));
      s.append(args[i]);
    }
    System.out.println(s.toString());
  }
}

