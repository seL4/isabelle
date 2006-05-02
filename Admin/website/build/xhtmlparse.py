#!/usr/bin/env python
# -*- coding: Latin-1 -*-

"""
    Common services for parsing xhtml.
"""

__all__ = ['TransformerHandler']

__author__ = 'Florian Haftmann, florian.haftmann@informatik.tu-muenchen.de'
__revision__ = '$Id$'

from os import path
import codecs
import posixpath
from xml.sax.saxutils import escape
from xml.sax.saxutils import quoteattr
from xml.sax import make_parser as makeParser
from xml.sax.handler import ContentHandler
from xml.sax.handler import EntityResolver
from xml.sax.xmlreader import AttributesImpl as Attributes
from xml.sax import SAXException
from xml.sax import SAXParseException

nbsp = unichr(160)

class TransformerHandler(object, ContentHandler, EntityResolver):

    def __init__(self, out, encoding, dtd):

        ContentHandler.__init__(self)
        self._out = codecs.getwriter(encoding)(out)
        self._encoding = encoding
        self._dtd = dtd
        self._ns_contexts = [{}] # contains uri -> prefix dicts
        self._current_context = self._ns_contexts[-1]
        self._undeclared_ns_maps = []
        self._characterBuffer = {}
        self._lastStart = False
        self._currentXPath = []
        self._init = False

    def closeLastStart(self):

        if self._lastStart:
            self._out.write(u'>')
            self._lastStart = False

    def currentContent(self):

        return u"".join(self._characterBuffer)

    def flushCharacterBuffer(self):

        content = escape(self.currentContent())
        self._out.write(content)
        self._characterBuffer = []

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

        self.closeLastStart()
        self.flushCharacterBuffer()
        self._out.write(u'<' + name)
        for (key, value) in attrs.items():
            self._out.write(u' %s=%s' % (key, quoteattr(value)))
        self._currentXPath.append(name)
        self._lastStart = True

    def endElement(self, name):

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
            systemId = path.abspath(path.join(self._dtd, name))
        return EntityResolver.resolveEntity(self, publicId, systemId)

    def processingInstruction(self, target, data):

        raise Exception("no handler defined for processing instructions")

def parseWithER(istream, handler):

    parser = makeParser()
    parser.setContentHandler(handler)
    parser.setEntityResolver(handler)
    parser.parse(istream)
