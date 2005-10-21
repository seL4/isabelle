# isaweb configuration
# $Id$

# build target (attention: ~ will not work!)
OUTPUTROOT=$(HOME)/isabelle/website_test
#~ OUTPUTROOT=/home/proj/isabelle/website

# location of isabelle distribution packages
ISABELLE_DIST=$(DISTBASE)

# location of doc content file
ISABELLE_DOC_CONTENT_FILE=$(DISTBASE)/$(DISTNAME)/doc/Contents

# dirs to copy to build target
STATICDIRS=css img media misc

# umask/group for target files
TARGET_UMASK_FILE=u=rw,g=rw,o=r
TARGET_UMASK_DIR=u=rwx,g=rwx,o=rx,g+s
TARGET_GROUP=isabelle
LOCAL_UMASK_FILE=u=rw,g=rw,o=r
LOCAL_UMASK_DIR=u=rwx,g=rwx,o=rx,g+s
LOCAL_GROUP=isabelle

# python interpreter (>= 2.3)
PYTHON=python

# GNU find
FIND=find

# GNU copy
COPY=cp

# HTML tidy (needs not to be set if tidy usage is disabled, see below)
TIDY=tidy

# rsync (if not set, use dumb cp instead)
RSYNC=rsync

# set to a true value to use the "pypager iso-8859-1" hack
# (may be neccessary for older versions of HTML tidy)
FORCE_ISO_8859_1=

# set to a true value to disable html tidy postprocessing
DISABLE_TIDY=
