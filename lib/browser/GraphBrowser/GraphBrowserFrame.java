/***************************************************************************
  Title:      GraphBrowser/GraphBrowserFrame.java
  ID:         $Id$
  Author:     Stefan Berghofer, TU Muenchen
  Copyright   1997  TU Muenchen

  This class is the frame for the stand-alone application. It contains
  methods for handling menubar events.
***************************************************************************/

package GraphBrowser;

import java.awt.*;
import java.io.*;
import awtUtilities.*;

public class GraphBrowserFrame extends Frame {
	GraphBrowser gb;
	MenuItem i1,i2;
	String graphDir,psDir;

	public void checkMenuItems() {
		if (gb.isEmpty()) {
			i1.disable();
			i2.disable();
		} else {
			i1.enable();
			i2.enable();
		}
	}

	public boolean action(Event evt, Object arg) {
		if (evt.target instanceof MenuItem) {
			String label=(String)arg;
			if (label.equals("Quit"))
				System.exit(0);
			else if (label.equals("Export to PostScript")) {
				PS(true,label);
				return true;
			} else if (label.equals("Export to EPS")) {
				PS(false,label);
				return true;
			} else if (label.equals("Open ...")) {
				FileDialog fd=new FileDialog(this,"Open graph file",FileDialog.LOAD);
				if (graphDir!=null)
					fd.setDirectory(graphDir);
				fd.show();
				if (fd.getFile()==null) return true;
				graphDir=fd.getDirectory();
				String fname=graphDir+fd.getFile();
				GraphBrowser gb2=new GraphBrowser(fname);
				try {
					InputStream is=new FileInputStream(fname);
					gb2.initBrowser(is);
					is.close();
				} catch (IOException exn) {
					String button[]={"OK"};
					MessageDialog md=new MessageDialog(this,"Error","Can't open file "+fname+".",button);
					md.resize(350,200);
					md.show();
					return true;
				}
				remove(gb);
				add("Center",gb2);
				gb=gb2;
				checkMenuItems();
				validate();
				return true;
			}
		}
		return false;
	}

	public void PS(boolean printable,String label) {
		FileDialog fd=new FileDialog(this,label,FileDialog.SAVE);
		if (psDir!=null)
			fd.setDirectory(psDir);
		fd.show();
		if (fd.getFile()==null) return;
		psDir=fd.getDirectory();
		String fname=psDir+fd.getFile();

		if ((new File(fname)).exists()) {
			String buttons[]={"Overwrite","Cancel"};
			MessageDialog md=new MessageDialog(this,"Warning",
			      "Warning: File "+fname+" already exists. Overwrite?",
			      buttons);
			md.resize(350,200);
			md.show();
			if (md.getText().equals("Cancel")) return;
		}

		try {
			gb.PS(fname,printable);
		} catch (IOException exn) {
			String button[]={"OK"};
			MessageDialog md=new MessageDialog(this,"Error",
			      "Unable to write file "+fname+".",button);
			md.resize(350,200);
			md.show();
		}
	}

	public GraphBrowserFrame(GraphBrowser br) {
		super("GraphBrowser");
		gb=br;
		MenuBar mb=new MenuBar();
		Menu m1=new Menu("File");
		m1.add(new MenuItem("Open ..."));
		m1.add(i1=new MenuItem("Export to PostScript"));
		m1.add(i2=new MenuItem("Export to EPS"));
		m1.add(new MenuItem("Quit"));
		checkMenuItems();
		mb.add(m1);
		setMenuBar(mb);
		add("Center",br);
	}
}
