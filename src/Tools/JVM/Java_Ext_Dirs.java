/*  Title:      Pure/System/Java_Ext_Dirs.java
    Author:     Makarius

Augment Java extension directories.
*/

package isabelle;

public class Java_Ext_Dirs
{
  public static void main(String [] args) {
    StringBuilder s = new StringBuilder();
    int i;
    for (i = 0; i < args.length; i++) {
      s.append(args[i]);
      s.append(System.getProperty("path.separator"));
    }
    s.append(System.getProperty("java.ext.dirs"));
    System.out.println(s.toString());
  }
}

