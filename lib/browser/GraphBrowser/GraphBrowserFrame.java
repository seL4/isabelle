/***************************************************************************
  Title:      GraphBrowser/GraphBrowserFrame.java
  ID:         $Id$
  Author:     Stefan Berghofer, TU Muenchen

  This class is the frame for the stand-alone application. It contains
  methods for handling menubar events.
***************************************************************************/

package GraphBrowser;

import java.awt.*;
import java.awt.event.*;
import java.io.*;
import awtUtilities.*;

public class GraphBrowserFrame extends Frame implements ActionListener {
	GraphBrowser gb;
	MenuItem i1, i2;
	String graphDir, psDir;

	public void checkMenuItems() {
		if (gb.isEmpty()) {
			i1.setEnabled(false);
			i2.setEnabled(false);
		} else {
			i1.setEnabled(true);
			i2.setEnabled(true);
		}
	}

	public void actionPerformed(ActionEvent evt) {
		String label = evt.getActionCommand();
		if (label.equals("Quit"))
			System.exit(0);
		else if (label.equals("Export to PostScript")) {
			PS(true, label);
			return;
		} else if (label.equals("Export to EPS")) {
			PS(false, label);
			return;
		} else if (label.equals("Open ...")) {
			FileDialog fd = new FileDialog(this, "Open graph file", FileDialog.LOAD);
			if (graphDir != null)
				fd.setDirectory(graphDir);
			fd.setVisible(true);
			if (fd.getFile() == null) return;
			graphDir = fd.getDirectory();
			String fname = graphDir + fd.getFile();
			GraphBrowser gb2 = new GraphBrowser(fname);
			try {
				InputStream is = new FileInputStream(fname);
				gb2.initBrowser(is, false);
				is.close();
			} catch (IOException exn) {
				String button[] = {"OK"};
				MessageDialog md = new MessageDialog(this, "Error",
					"Can't open file " + fname + ".", button);
				md.setSize(350, 200);
				md.setVisible(true);
				return;
			}
			remove(gb);
			add("Center", gb2);
			gb = gb2;
			checkMenuItems();
			validate();
		}
	}

	public void PS(boolean printable,String label) {
		FileDialog fd=new FileDialog(this,label,FileDialog.SAVE);
		if (psDir!=null)
			fd.setDirectory(psDir);
		fd.setVisible(true);
		if (fd.getFile()==null) return;
		psDir=fd.getDirectory();
		String fname=psDir+fd.getFile();

		if ((new File(fname)).exists()) {
			String buttons[]={"Overwrite","Cancel"};
			MessageDialog md=new MessageDialog(this,"Warning",
			      "Warning: File "+fname+" already exists. Overwrite?",
			      buttons);
			md.setSize(350,200);
			md.setVisible(true);
			if (md.getText().equals("Cancel")) return;
		}

		try {
			gb.PS(fname,printable);
		} catch (IOException exn) {
			String button[]={"OK"};
			MessageDialog md=new MessageDialog(this,"Error",
			      "Unable to write file "+fname+".",button);
			md.setSize(350,200);
			md.setVisible(true);
		}
	}

	public GraphBrowserFrame(GraphBrowser br) {
		super("GraphBrowser");
		MenuItem i3, i4;
		gb = br;
		MenuBar mb = new MenuBar();
		Menu m1 = new Menu("File");
		m1.add(i3 = new MenuItem("Open ..."));
		m1.add(i1 = new MenuItem("Export to PostScript"));
		m1.add(i2 = new MenuItem("Export to EPS"));
		m1.add(i4 = new MenuItem("Quit"));
		i1.addActionListener(this);
		i2.addActionListener(this);
		i3.addActionListener(this);
		i4.addActionListener(this);
		checkMenuItems();
		mb.add(m1);
		setMenuBar(mb);
		add("Center", br);
    addWindowListener( new WindowAdapter() {
      public void windowClosing(WindowEvent e) {
        System.exit(0);
      }
    });
	}
}
