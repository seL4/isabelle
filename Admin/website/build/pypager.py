#!/usr/bin/env python
# -*- coding: Latin-1 -*-

"""
    (on available processing instructions, see the Functions class)
"""

__author__ = 'Florian Haftmann, florian.haftmann@informatik.tu-muenchen.de'
__revision__ = '$Id$'

# generic imports
import sys
import os
from os import path
import posixpath
import shlex
import optparse
import time

# xhtml parsing
from xhtmlparse import TransformerHandler, parseWithER

nbsp = unichr(160)

# global configuration
outputEncoding = 'UTF-8'

# implement your own functions for PIs here
class Functions(object):

    def __init__(self, pc, valdict, modtime, encodingMeta):

        self._pc = pc
        self._valdict = valdict
        self._modtime = modtime
        self._encodingMeta = encodingMeta

    def value(self, handler, key):

        """<?value key="..."?> - inserts a property value given on the command line"""

        value = self._valdict[key]
        handler.characters(value)

    def title(self, handler):

        """<?title?> - inserts the document's title as glimpsed from the <title> tag"""

        handler.characters(handler._title)

    def contentType(self, handler):

        """<?contentType?> - inserts the document's content type/encoding"""

        encoding = self._encodingMeta or handler._encoding
        attr = {
            u"http-equiv": u"Content-Type",
            u"content": u"text/html; charset=%s" % encoding
        }
        handler.startElement(u"meta", attr)
        handler.endElement(u"meta")

    def currentDate(self, handler):

        """<?currentDate?> - inserts the current date"""

        handler.characters(unicode(time.strftime('%Y-%m-%d %H:%M:%S')))

    def modificationDate(self, handler):

        """<?modificationDate?> - inserts the modification date of this file"""

        handler.characters(unicode(time.strftime('%Y-%m-%d %H:%M:%S',
            time.localtime(self._modtime))))

    def relativeRoot(self, handler, href):

        """<?relativeRoot href="..."?> - inserts the relative path specified by href"""

        handler.characters(self._pc.relDstPathOf('//'+href.encode("latin-1")))

    def include(self, handler, file):

        """<?include file="..."?> - includes an XML file"""

        filename = self._pc.absSrcPathOf(file.encode("latin-1"))
        self._modtime = max(self._modtime, os.stat(filename).st_mtime)
        istream = open(filename, "r")
        parseWithER(istream, handler)
        istream.close()

    def navitem(self, handler, target, title):

        """<?navitem target="..." title="..."?> - inserts an item in a navigation list,
            targeting to <target> and entitled <title>"""

        target = self._pc.relDstPathOf(target.encode("latin-1"))
        if self._pc.isSrc(target):
            wrapTagname = u"strong"
        else:
            wrapTagname = u"span"
        attr = {}
        handler.startElement(u"li", attr)
        handler.startElement(wrapTagname, {})
        handler.startElement(u"a", {
            u"href": unicode(target, 'latin-1')
        })
        handler.characters(title)
        handler.endElement(u"a")
        handler.endElement(wrapTagname)
        handler.endElement(u"li")

    def downloadLink(self, handler, target, title = None):

        """<?downloadLink target="..." [title="..."]?> - inserts a link to a file
           to download; if the title is omitted, it is the bare filename itself"""

        targetReal = self._pc.absDstPathOf(target.encode("latin-1"))
        if not title:
            title = unicode(posixpath.split(targetReal)[1], 'latin-1')
        size = os.stat(targetReal).st_size
        handler.startElement(u"a", {
            u"href": target
        })
        handler.characters(title)
        handler.endElement(u"a")

    def downloadCells(self, handler, target, title = None):

        """<?downloadCells target="..." [title="..."]?> - like downloadLink, but
           puts the link into a table cell and appends a table cell displaying the
           size of the linked file"""

        targetReal = self._pc.absDstPathOf(target.encode("latin-1"))
        if not title:
            title = unicode(posixpath.split(targetReal)[1], 'latin-1')
        size = os.stat(targetReal).st_size
        handler.startElement(u"td", {})
        handler.startElement(u"a", {
            u"href": target
        })
        handler.characters(title)
        handler.endElement(u"a")
        handler.endElement(u"td")
        handler.startElement(u"td", {})
        handler.characters(u"%.1f%sMB" % (size / (1024.0 * 1024), unichr(160)))
        handler.endElement(u"td")

    def mirror(self, handler, prefix, title, stripprefix = u""):

        """<?mirror prefix="..." title="..." [stripprefix="..."] ?> - generates a mirror switch link,
           where prefix denotes the base root url of the mirror location
           and title the visible description"""

        title = title.replace(u" ", unichr(160))
        thisloc = self._pc.relLocOfThis()
        if thisloc.startswith(stripprefix):
            thisloc = thisloc[len(stripprefix):]
        else:
            raise Exception("Incompatible mirror (prefix to strip not found): %s" % title.encode("latin-1"))
        handler.startElement(u"a", {u"href": posixpath.join(prefix, thisloc)})
        handler.characters(title)
        handler.endElement(u"a")

    def getPc(self):

        return self._pc

# a notion of paths
class PathCalculator:

    def __init__(self, srcLoc, srcRoot, dstRoot):

        self._src = path.normpath(path.abspath(srcLoc))
        srcPath, self._srcName = path.split(self._src)
        self._srcRoot = path.normpath(path.abspath(srcRoot))
        self._dstRoot = path.normpath(path.abspath(dstRoot))
        self._relRoot = ""
        relLocChain = []
        diffRoot = srcPath
        while diffRoot != self._srcRoot:
            self._relRoot = path.join(self._relRoot, os.pardir)
            diffRoot, chainPiece = path.split(diffRoot)
            relLocChain.insert(0, chainPiece)
        self._relRoot = self._relRoot and self._relRoot + '/'
        self._relLoc = relLocChain and path.join(*relLocChain) or ""

    def isSrc(self, loc):

        return self.absSrcPathOf(loc) == self._src

    def relRootPath(self):

        return self._relRoot

    def absSrcPathOf(self, loc):

        if loc.startswith("//"):
            return path.normpath(path.abspath(loc[2:]))
        else:
            return path.normpath(path.abspath(path.join(self._relLoc, loc)))

    def absDstPathOf(self, loc):

        if loc.startswith("//"):
            return path.join(self._dstRoot, loc[2:])
        else:
            return path.join(self._dstRoot, self._relLoc, loc)

    def relSrcPathOf(self, loc):

        loc = self.absSrcPathOf(loc)
        loc = self.stripCommonPrefix(loc, self._srcRoot)
        loc = self.stripCommonPrefix(loc, self._relLoc)
        return loc

    def relDstPathOf(self, loc):

        loc = self.absDstPathOf(loc)
        loc = self.stripCommonPrefix(loc, self._dstRoot)
        loc = self.stripCommonPrefix(loc, self._relLoc)
        return loc

    def relLocOfThis(self):

        return posixpath.join(self._relLoc, self._srcName)

    def stripCommonPrefix(self, loc, prefix):

        common = self.commonPrefix((loc, prefix))
        if common:
            loc = loc[len(common):]
            if loc and loc[0] == '/':
                loc = loc[1:]
        return loc

    def commonPrefix(self, locs):

        common = path.commonprefix(locs)
        # commonprefix bugs
        if [ loc for loc in locs if len(loc) != common ] and \
            [ loc for loc in locs if len(common) < len(loc) and loc[len(common)] != path.sep ]:
                common = path.split(common)[0]
        if common and common[-1] == path.sep:
            common = common[:-1]

        return common or ""

class FunctionsHandler(TransformerHandler):

    def __init__(self, out, encoding, dtd, func):

        super(FunctionsHandler, self).__init__(out, encoding, dtd)
        self._func = func
        self._title = None

    def transformAbsPath(self, attrs, attrname):

        pathval = attrs.get(attrname, None)
        if pathval and pathval.startswith(u"//"):
            attrs = dict(attrs)
            pathRel = self._func.getPc().relDstPathOf(pathval)
            pathDst = self._func.getPc().absDstPathOf(pathval)
            if not path.exists(pathDst):
                raise Exception("Path does not exist: %s" % pathDst)
            attrs[attrname] = pathRel
            return attrs
        else:
            return attrs

    def startElement(self, name, attrs):

        if name == u"dummy:wrapper":
            return
        # this list is not exhaustive
        for tagname, attrname in ((u"a", u"href"), (u"img", u"src"), (u"link", u"href"), (u"script", u"src")):
            if name == tagname:
                attrs = self.transformAbsPath(attrs, attrname)
        super(FunctionsHandler, self).startElement(name, attrs)

    def endElement(self, name):

        if name == u"dummy:wrapper":
            return
        elif name == u'title':
            self._title = u"".join(self._characterBuffer)
        super(FunctionsHandler, self).endElement(name)

    def processingInstruction(self, target, data):

        self.closeLastStart()
        self.flushCharacterBuffer()
        func = getattr(self._func, target)
        args = {}
        for keyval in shlex.split(data.encode("utf-8")):
            key, val = keyval.split("=", 1)
            args[key] = val
        func(self, **args)


def main():

    # parse command line
    cmdlineparser = optparse.OptionParser(
        usage = '%prog [options] [key=value]* src [dst]',
        conflict_handler = "error",
        description = '''Leightweight HTML page generation tool''',
        add_help_option = True,
    )
    cmdlineparser.add_option("-s", "--srcroot",
        action="store", dest="srcroot",
        type="string", default=".",
        help="source tree root", metavar='location')
    cmdlineparser.add_option("-d", "--dstroot",
        action="store", dest="dstroot",
        type="string", default=".",
        help="destination tree root", metavar='location')
    cmdlineparser.add_option("-t", "--dtd",
        action="store", dest="dtd",
        type="string", default=".",
        help="local mirror of XHTML DTDs", metavar='location')
    cmdlineparser.add_option("-m", "--encodinghtml",
        action="store", dest="encodinghtml",
        type="string", default="",
        help="force value of html content encoding meta tag", metavar='encoding')

    options, args = cmdlineparser.parse_args(sys.argv[1:])

    # check source
    if len(args) < 1:
        cmdlineparser.error("Exactly one soure file must be given")

    # read arguments
    valdict = {}
    if len(args) == 1:
        src = args[0]
        dst = None
    else:
        if "=" in args[-2]:
            src = args[-1]
            dst = None
            vallist = args[:-1]
        else:
            src = args[-2]
            dst = args[-1]
            if dst == "-":
                dst = None
            vallist = args[:-2]
        for keyval in vallist:
            key, val = keyval.split("=", 1)
            valdict[unicode(key, 'latin-1')] = unicode(val, 'latin-1')

    # path calculator
    pc = PathCalculator(src, options.srcroot, options.dstroot)

    # function space
    modtime = os.stat(src).st_mtime
    func = Functions(pc, valdict, modtime, options.encodinghtml)

    # allocate file handles
    istream = open(src, 'r')
    if dst is not None:
        ostream = open(dst, 'wb')
    else:
        ostream = sys.stdout

    # process file
    try:
        transformer = FunctionsHandler(ostream, outputEncoding, options.dtd, func)
        parseWithER(istream, transformer)
    except Exception:
        if dst is not None:
            os.unlink(dst)
        raise

    # close handles
    ostream.close()
    istream.close()

if __name__ == '__main__':
    main()

__todo__ = '''
'''
