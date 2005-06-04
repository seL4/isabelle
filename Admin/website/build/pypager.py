#!/usr/bin/env python
# -*- coding: Latin-1 -*-

__author__ = 'Florian Haftmann, florian.haftmann@informatik.tu-muenchen.de'
__revision__ = '$Id$'

# generic imports
import sys
import os
from os import path
import posixpath
import codecs
import shlex
import optparse
import time

# xml imports
from xml.sax.saxutils import escape
from xml.sax.saxutils import quoteattr
from xml.sax import make_parser as makeParser
from xml.sax.handler import ContentHandler
from xml.sax.handler import EntityResolver
from xml.sax.xmlreader import AttributesImpl as Attributes
from xml.sax import SAXException
from xml.sax import SAXParseException

nbsp = unichr(160)

# global configuration
outputEncoding = 'UTF-8'

# implement your own functions for PIs here
class Functions:

    def __init__(self, pc, valdict, modtime, encodingMeta):

        self._pc = pc
        self._valdict = valdict
        self._modtime = modtime
        self._encodingMeta = encodingMeta

    def getPc(self):

        return self._pc

    def value(self, handler, **args):

        value = self._valdict[args[u"key"]]
        handler.characters(value)

    def title(self, handler, **args):

        handler.characters(handler._title)

    def contentType(self, handler, **args):

        encoding = self._encodingMeta or handler._encoding
        attr = {
            u"http-equiv": u"Content-Type",
            u"content": u"text/html; charset=%s" % encoding
        }
        handler.startElement(u"meta", attr)
        handler.endElement(u"meta")

    def currentDate(self, handler, **args):

        handler.characters(unicode(time.strftime('%Y-%m-%d %H:%M:%S')))

    def modificationDate(self, handler, **args):

        handler.characters(unicode(time.strftime('%Y-%m-%d %H:%M:%S',
            time.localtime(self._modtime))))

    def relativeRoot(self, handler, **args):

        href = args[u"href"].encode("latin-1")
        handler.characters(self._pc.relDstPathOf('//'+href))

    def include(self, handler, **args):

        filename = args[u"file"].encode("latin-1")
        filename = self._pc.absSrcPathOf(filename)
        self._modtime = max(self._modtime, os.stat(filename).st_mtime)
        istream = open(filename, "r")
        parseWithER(istream, handler)
        istream.close()

    def navitem(self, handler, **args):

        target = args[u"target"].encode("latin-1")
        target = self._pc.relDstPathOf(target)
        if self._pc.isSrc(target):
            wrapTagname = u"strong"
        else:
            wrapTagname = u"span"
        title = args[u"title"]
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

    def downloadCells(self, handler, **args):

        target = args[u"target"].encode("latin-1")
        targetReal = self._pc.absDstPathOf(target)
        title = args.get(u"title", unicode(posixpath.split(target)[0], 'latin-1'))
        size = os.stat(targetReal).st_size
        handler.startElement(u"td", {})
        handler.startElement(u"a", {
            u"href": target
        })
        handler.characters(title)
        handler.endElement(u"a")
        handler.endElement(u"td")
        handler.startElement(u"td", {})
        handler.characters(u"%i%sKB" % (size / 1024, unichr(160)))
        handler.endElement(u"td")

# a notion of paths
class PathCalculator:

    def __init__(self, srcLoc, srcRoot, dstRoot):

        self._src = path.normpath(path.abspath(srcLoc))
        srcPath, srcName = path.split(self._src)
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

# the XML transformer
class TransformerHandler(ContentHandler, EntityResolver):

    def __init__(self, out, encoding, dtd, func):

        ContentHandler.__init__(self)
        #~ EntityResolver.__init__(self)
        self._out = codecs.getwriter(encoding)(out)
        self._ns_contexts = [{}] # contains uri -> prefix dicts
        self._current_context = self._ns_contexts[-1]
        self._undeclared_ns_maps = []
        self._encoding = encoding
        self._lastStart = False
        self._func = func
        self._characterBuffer = {}
        self._currentXPath = []
        self._title = None
        self._init = False
        self._dtd = dtd

    def closeLastStart(self):

        if self._lastStart:
            self._out.write(u'>')
            self._lastStart = False

    def flushCharacterBuffer(self):

        self._out.write(escape(u"".join(self._characterBuffer)))
        self._characterBuffer = []

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

    def startDocument(self):

        if not self._init:
            if self._encoding.upper() != 'UTF-8':
                self._out.write(u'<?xml version="1.0" encoding="%s"?>\n' %
                                self._encoding)
            else:
                self._out.write(u'<?xml version="1.0"?>\n')
            self._init = True

    def startPrefixMapping(self, prefix, uri):

        self._ns_contexts.append(self._current_context.copy())
        self._current_context[uri] = prefix
        self._undeclared_ns_maps.append((prefix, uri))

    def endPrefixMapping(self, prefix):

        self._current_context = self._ns_contexts[-1]
        del self._ns_contexts[-1]

    def startElement(self, name, attrs):

        if name == u"dummy:wrapper":
            return
        self.closeLastStart()
        self.flushCharacterBuffer()
        self._out.write(u'<' + name)
        # this list is not exhaustive
        for tagname, attrname in ((u"a", u"href"), (u"img", u"src"), (u"link", u"href")):
            if name == tagname:
                attrs = self.transformAbsPath(attrs, attrname)
        for (name, value) in attrs.items():
            self._out.write(u' %s=%s' % (name, quoteattr(value)))
        self._currentXPath.append(name)
        self._lastStart = True

    def endElement(self, name):

        if name == u"dummy:wrapper":
            return
        elif name == u'title':
            self._title = u"".join(self._characterBuffer)
        self.flushCharacterBuffer()
        if self._lastStart:
            self._out.write(u'/>')
            self._lastStart = False
        else:
            self._out.write('</%s>' % name)
        self._currentXPath.pop()

    def startElementNS(self, name, qname, attrs):

        self.closeLastStart()
        self.flushCharacterBuffer()
        if name[0] is None:
            # if the name was not namespace-scoped, use the unqualified part
            name = name[1]
        else:
            # else try to restore the original prefix from the namespace
            name = self._current_context[name[0]] + u":" + name[1]
        self._out.write(u'<' + name)

        for pair in self._undeclared_ns_maps:
            self._out.write(u' xmlns:%s="%s"' % pair)
        self._undeclared_ns_maps = []

        for (name, value) in attrs.items():
            name = self._current_context[name[0]] + ":" + name[1]
            self._out.write(' %s=%s' % (name, quoteattr(value)))
        self._out.write('>')
        self._currentXPath.append(name)

    def endElementNS(self, name, qname):

        self.flushCharacterBuffer()
        if name[0] is None:
            name = name[1]
        else:
            name = self._current_context[name[0]] + u":" + name[1]
        if self._lastStart:
            self._out.write(u'/>')
            self._lastStart = False
        else:
            self._out.write(u'</%s>' % name)
        self._currentXPath.pop()

    def characters(self, content):

        self.closeLastStart()
        self._characterBuffer.append(content)

    def ignorableWhitespace(self, content):

        self.closeLastStart()
        self.flushCharacterBuffer()
        self._out.write(content)

    def resolveEntity(self, publicId, systemId):

        loc, name = posixpath.split(systemId)
        if loc == u"http://www.w3.org/TR/xhtml1/DTD" or loc == u"":
            systemId = path.join(self._dtd, name)
        return EntityResolver.resolveEntity(self, publicId, systemId)

    def processingInstruction(self, target, data):

        print '*', target
        print '*', data
        self.closeLastStart()
        self.flushCharacterBuffer()
        func = getattr(self._func, target)
        args = {}
        for keyval in shlex.split(data.encode("utf-8")):
            key, val = keyval.split("=", 1)
            args[key] = val
        func(self, **args)

def parseWithER(istream, handler):

    parser = makeParser()
    parser.setContentHandler(handler)
    parser.setEntityResolver(handler)
    parser.parse(istream)

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
        help="force value of html content encoding meta ", metavar='encoding')


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
    transformer = TransformerHandler(ostream, outputEncoding, options.dtd, func)
    parseWithER(istream, transformer)

    # close handles
    ostream.close()
    istream.close()

if __name__ == '__main__':
    main()

__todo__ = '''
'''
