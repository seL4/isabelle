/***************************************************************************
  Title:      GraphBrowser/GraphBrowser.java
  ID:         $Id$
  Author:     Stefan Berghofer, TU Muenchen
  Copyright   1997  TU Muenchen

  This is the graph browser's main class. It contains the "main(...)"
  method, which is used for the stand-alone version, as well as
  "init(...)", "start(...)" and "stop(...)" methods which are used for
  the applet version.
  Note: GraphBrowser is designed for the 1.1.x version of the JDK.
***************************************************************************/

package GraphBrowser;

import java.awt.*;
import java.applet.*;
import java.io.*;
import java.util.*;
import java.net.*;
import awtUtilities.*;

public class GraphBrowser extends Applet {
	GraphView gv;
	TreeBrowser tb=null;
	String gfname;

	static boolean isApplet;
	static Frame f;

	public GraphBrowser(String name) {
		gfname=name;
	}

	public GraphBrowser() {}

	public void showWaitMessage() {
		if (isApplet)
			getAppletContext().showStatus("calculating layout, please wait ...");
		else {
			f.setCursor(new Cursor(Cursor.WAIT_CURSOR));
		}
	}

	public void showReadyMessage() {
		if (isApplet)
			getAppletContext().showStatus("ready !");
		else {
			f.setCursor(new Cursor(Cursor.DEFAULT_CURSOR));
		}
	}

	public void viewFile(String fname) {
		try {
			if (isApplet)
				getAppletContext().showDocument(new URL(getDocumentBase(), fname), "_blank");
			else {
				String path = gfname.substring(0, gfname.lastIndexOf('/') + 1);
				BufferedReader br;
				String line, text = "";

				br = new BufferedReader(new FileReader(path + fname));
				while ((line = br.readLine()) != null)
					text += line + "\n";

				if (fname.endsWith(".html")) {
					/**** convert HTML to text (just a quick hack) ****/

					String buf="";
					char[] text2,text3;
					int i,j=0;
					boolean special=false, html=false;
					char ctrl;

					text2 = text.toCharArray();
					text3 = new char[text.length()];
					for (i = 0; i < text.length(); i++) {
						char c = text2[i];
						if (c == '&') {
							special = true;
							buf = "";
						} else if (special) {
							if (c == ';') {
								special = false;
								if (buf.equals("lt"))
									text3[j++] = '<';
								else if (buf.equals("gt"))
									text3[j++] = '>';
								else if (buf.equals("amp"))
									text3[j++] = '&';
							} else
								buf += c;
						} else if (c == '<') {
							html = true;
							ctrl = text2[i+1];
							if ((ctrl == 'P') || (ctrl == 'B'))
								text3[j++] = '\n';		
						} else if (c == '>')
							html = false;
						else if (!html)
							text3[j++] = c;
					}
					text = String.valueOf(text3);
				}
							
				Frame f=new TextFrame(fname.substring(fname.lastIndexOf('/')+1),text);
				f.setSize(500,600);
				f.show();
			}
		} catch (Exception exn) {
			System.out.println("Can't read file "+fname);
		}
	}
				
	public void PS(String fname,boolean printable) throws IOException {
		gv.PS(fname,printable);
	}

	public boolean isEmpty() {
		return tb==null;
	}

	public void initBrowser(InputStream is) {
		try {
			TreeNode tn=new TreeNode("Directories","",-1,true);
			gv=new GraphView(new Graph(is,tn),this);
			tb=new TreeBrowser(tn,gv);
			gv.setTreeBrowser(tb);
			Vector v = new Vector(10,10);
			tn.collapsedDirectories(v);
			gv.collapseDir(v);

			ScrollPane scrollp1 = new ScrollPane();
			ScrollPane scrollp2 = new ScrollPane();
			scrollp1.add(gv);
			scrollp2.add(tb);
			scrollp1.getHAdjustable().setUnitIncrement(20);
			scrollp1.getVAdjustable().setUnitIncrement(20);
			scrollp2.getHAdjustable().setUnitIncrement(20);
			scrollp2.getVAdjustable().setUnitIncrement(20);
			Component gv2 = new Border(scrollp1, 5);
			Component tb2 = new Border(scrollp2, 5);
			GridBagLayout gridbag = new GridBagLayout();
			GridBagConstraints cnstr = new GridBagConstraints();
			setLayout(gridbag);
			cnstr.fill = GridBagConstraints.BOTH;
			cnstr.insets = new Insets(5,5,5,5);
			cnstr.weightx = 1;
			cnstr.weighty = 1;
			cnstr.gridwidth = 1;
			gridbag.setConstraints(tb2,cnstr);
			add(tb2);
			cnstr.weightx = 2.5;
			cnstr.gridwidth = GridBagConstraints.REMAINDER;
			gridbag.setConstraints(gv2,cnstr);
			add(gv2);
		} catch (IOException exn) {
			System.out.println("\nI/O error while reading graph file.");
		} catch (ParseError exn) {
			System.out.println("\nParse error in graph file:");
			System.out.println(exn.getMessage());
			System.out.println("\nSyntax:\n<vertexname> <vertexID> <dirname> [ + ] <path> [ < | > ] [ <vertexID> [ ... [ <vertexID> ] ... ] ] ;");
		}
	}		

	public void init() {
		isApplet=true;
		gfname=getParameter("graphfile");
		try {
			InputStream is=(new URL(getDocumentBase(), gfname)).openConnection().getInputStream();
			initBrowser(is);
			is.close();
		} catch (MalformedURLException exn) {
			System.out.println("Invalid URL: "+gfname);
		} catch (IOException exn) {
			System.out.println("I/O error while reading "+gfname+".");
		}
	}

	public static void main(String[] args) {
		isApplet=false;
		try {
			GraphBrowser gb=new GraphBrowser(args.length > 0 ? args[0] : "");
			if (args.length>0) {
				InputStream is=new FileInputStream(args[0]);
				gb.initBrowser(is);
				is.close();
			}
			f=new GraphBrowserFrame(gb);
			f.setSize(700,500);
			f.show();
		} catch (IOException exn) {
			System.out.println("Can't open graph file "+args[0]);
		}
	}
}

