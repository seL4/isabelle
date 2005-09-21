# isaweb configuration
# $Id$

# python interpreter (> 2.2)
PYTHON=python

# GNU find
FIND=find

# HTML tidy (needs not to be set if tidy usage is disabled, see below)
TIDY=tidy

# dirs to copy to build target
STATICDIRS=css img media misc dist

# build target (attention: ~ will not work!)
OUTPUTROOT=/home/proj/isabelle/website

# location of isabelle distribution packages
ISABELLE_DIST=/home/proj/isabelle/dist/Isabelle2004

# location of isabelle library 
ISABELLE_LIBR=/home/proj/isabelle/dist/library-Isabelle2004

# location of doc content file
ISABELLE_DOC_CONTENT_FILE=/home/proj/isabelle/Isabelle2004/doc/Contents

# umask for target files
TARGET_UMASK_FILE=664
TARGET_UMASK_DIR=775

# set to a true value to use the "pypager iso-8859-1" hack
# (may be neccessary for older versions of HTML tidy)
FORCE_ISO_8859_1=

# set to a true value to disable html tidy postprocessing
DISABLE_TIDY=
