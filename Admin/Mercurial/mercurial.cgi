#!/usr/bin/env python
# $Id$
# Isabelle repository service

# adjust python path if not a system-wide install:
import sys
sys.path.insert(0, "/home/isabelle/html-data/isabelle-repos/mercurial-www4/lib64/python2.4/site-packages")

# enable importing on demand to reduce startup time
from mercurial import demandimport; demandimport.enable()

# to send python tracebacks to the browser if an error occurs:
import cgitb
cgitb.enable()

# If you'd like to serve pages with UTF-8 instead of your default
# locale charset, you can do so by uncommenting the following lines.
# Note that this will cause your .hgrc files to be interpreted in
# UTF-8 and all your repo files to be displayed using UTF-8.
#
import os
os.environ["HGENCODING"] = "UTF-8"

from mercurial.hgweb.hgweb_mod import hgweb
import mercurial.hgweb.wsgicgi as wsgicgi

application = hgweb("/home/isabelle/html-data/isabelle-repos/hg", "Isabelle repository")
wsgicgi.launch(application)
