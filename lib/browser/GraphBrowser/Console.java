/***************************************************************************
  Title:      GraphBrowser/Console.java
  ID:         $Id$
  Author:     Stefan Berghofer, TU Muenchen
  License:    GPL (GNU GENERAL PUBLIC LICENSE)

  This is the graph browser's main class when run as a console application.

***************************************************************************/

package GraphBrowser;

import java.io.*;
import java.util.*;
import java.net.*;
import awtUtilities.*;

public class Console {
	Graph g;
	// TreeBrowser tb;
	String gfname;

  public Console(String name) {
    gfname = name;
  }

	public void PS(String fname,boolean printable) throws IOException {
    g.layout(null);
		g.PS(fname,printable);
	}

	public void initBrowser(InputStream is) {
		try {
			TreeNode tn = new TreeNode("Root", "", -1, true);
      g = new Graph(is, tn);
      
			// gv = new GraphView(new Graph(is, tn), null, null);
      // tb = new TreeBrowser(tn, gv, font);
			// gv.setTreeBrowser(tb);
			// Vector v = new Vector(10,10);
			// tn.collapsedDirectories(v);
			// gv.collapseDir(v);
		} catch (IOException exn) {
			System.err.println("\nI/O error while reading graph file.");
		} catch (ParseError exn) {
			System.err.println("\nParse error in graph file:");
			System.err.println(exn.getMessage());
			System.err.println("\nSyntax:\n<vertexname> <vertexID> <dirname> [ + ] <path> [ < | > ] [ <vertexID> [ ... [ <vertexID> ] ... ] ] ;");
		}
	}

	public static void main(String[] args) {
		try {
      if (args.length <= 1) {
        System.err.println("Graph and output file expected");
        return;
      }
			Console console=new Console(args[0]);

      InputStream is=new FileInputStream(args[0]);
      console.initBrowser(is);
      is.close();      
    
      try {
        if (args[1].endsWith(".ps"))
          console.PS(args[1], true);
        else if (args[1].endsWith(".eps"))
          console.PS(args[1], false);
        else
          System.err.println("Unknown file type: " + args[1]);
      } catch (IOException exn) {
        System.err.println("Unable to write file " + args[1]);
      }
		} catch (IOException exn) {
			System.err.println("Can't open graph file "+args[0]);
		}
	}
}

