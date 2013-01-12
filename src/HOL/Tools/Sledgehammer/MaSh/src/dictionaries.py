#     Title:      HOL/Tools/Sledgehammer/MaSh/src/dictionaries.py
#     Author:     Daniel Kuehlwein, ICIS, Radboud University Nijmegen
#     Copyright   2012
#
# Persistent dictionaries: accessibility, dependencies, and features.

'''
Created on Jul 12, 2012

@author: daniel
'''

from os.path import join
from Queue import Queue
from readData import create_accessible_dict,create_dependencies_dict,create_feature_dict
from cPickle import load,dump

class Dictionaries(object):
    '''
    This class contains all info about name-> id mapping, etc.
    '''
    def __init__(self):
        '''
        Constructor
        '''
        self.nameIdDict = {}
        self.idNameDict = {}
        self.featureIdDict={}
        self.maxNameId = 0
        self.maxFeatureId = 0
        self.featureDict = {}
        self.dependenciesDict = {}
        self.accessibleDict = {}
        self.expandedAccessibles = {}
        # For SInE-like prior
        self.featureCountDict = {}
        self.triggerFeatures = {}
        self.changed = True

    """
    Init functions. Side Effect: nameIdDict, idNameDict, featureIdDict, articleDict get filled!
    """
    def init_featureDict(self,featureFile):
        self.featureDict,self.maxNameId,self.maxFeatureId, self.featureCountDict,self.triggerFeatures = create_feature_dict(self.nameIdDict,self.idNameDict,self.maxNameId,self.featureIdDict,\
                                                                                                       self.maxFeatureId,self.featureCountDict,self.triggerFeatures,featureFile)
    def init_dependenciesDict(self,depFile):
        self.dependenciesDict = create_dependencies_dict(self.nameIdDict,depFile)
    def init_accessibleDict(self,accFile):
        self.accessibleDict,self.maxNameId = create_accessible_dict(self.nameIdDict,self.idNameDict,self.maxNameId,accFile)

    def init_all(self,inputFolder,featureFileName = 'mash_features',depFileName='mash_dependencies',accFileName = 'mash_accessibility'):
        featureFile = join(inputFolder,featureFileName)
        depFile = join(inputFolder,depFileName)
        accFile = join(inputFolder,accFileName)
        self.init_featureDict(featureFile)
        self.init_accessibleDict(accFile)
        self.init_dependenciesDict(depFile)
        self.expandedAccessibles = {}
        self.changed = True

    def get_name_id(self,name):
        """
        Return the Id for a name.
        If it doesn't exist yet, a new entry is created.
        """
        if self.nameIdDict.has_key(name):
            nameId = self.nameIdDict[name]
        else:
            self.nameIdDict[name] = self.maxNameId
            self.idNameDict[self.maxNameId] = name
            nameId = self.maxNameId
            self.maxNameId += 1
            self.changed = True
        return nameId

    def add_feature(self,featureName):
        if not self.featureIdDict.has_key(featureName):
            self.featureIdDict[featureName] = self.maxFeatureId
            self.featureCountDict[self.maxFeatureId] = 0
            self.maxFeatureId += 1
            self.changed = True
        fId = self.featureIdDict[featureName]
        self.featureCountDict[fId] += 1
        return fId

    def get_features(self,line):
        # Feature Ids
        featureNames = [f.strip() for f in line[1].split()]
        features = []
        for fn in featureNames:
            tmp = fn.split('=')
            weight = 1.0
            if len(tmp) == 2:
                fn = tmp[0]
                weight = float(tmp[1])
            fId = self.add_feature(tmp[0])
            features.append((fId,weight))
        return features

    def expand_accessibles(self,acc):
        accessibles = set(acc)
        unexpandedQueue = Queue()
        for a in acc:
            if self.expandedAccessibles.has_key(a):
                accessibles = accessibles.union(self.expandedAccessibles[a])
            else:
                unexpandedQueue.put(a)
        while not unexpandedQueue.empty():
            nextUnExp = unexpandedQueue.get()
            nextUnExpAcc = self.accessibleDict[nextUnExp]
            for a in nextUnExpAcc:
                if not a in accessibles:
                    accessibles = accessibles.union([a])
                    if self.expandedAccessibles.has_key(a):
                        accessibles = accessibles.union(self.expandedAccessibles[a])
                    else:
                        unexpandedQueue.put(a)
        return list(accessibles)

    def parse_fact(self,line):
        """
        Parses a single line, extracting accessibles, features, and dependencies.
        """
        assert line.startswith('! ')
        line = line[2:]

        # line = name:accessibles;features;dependencies
        line = line.split(':')
        name = line[0].strip()
        nameId = self.get_name_id(name)

        line = line[1].split(';')
        # Accessible Ids
        unExpAcc = [self.nameIdDict[a.strip()] for a in line[0].split()]
        self.accessibleDict[nameId] = unExpAcc
        features = self.get_features(line)
        self.featureDict[nameId] = features
        minVal = min([self.featureCountDict[f] for f,_w in features])
        self.triggerFeatures[nameId] = [f for f,_w in features if self.featureCountDict[f] == minVal]
        self.dependenciesDict[nameId] = [self.nameIdDict[d.strip()] for d in line[2].split()]        
        self.changed = True
        return nameId

    def parse_overwrite(self,line):
        """
        Parses a single line, extracts the problemId and the Ids of the dependencies.
        """
        assert line.startswith('p ')
        line = line[2:]

        # line = name:dependencies
        line = line.split(':')
        name = line[0].strip()
        nameId = self.get_name_id(name)

        dependencies = [self.nameIdDict[d.strip()] for d in line[1].split()]
        self.changed = True
        return nameId,dependencies

    def parse_problem(self,line):
        """
        Parses a problem and returns the features, the accessibles, and any hints.
        """
        assert line.startswith('? ')
        line = line[2:]
        name = None

        # Check whether there is a problem name:
        tmp = line.split(':')
        if len(tmp) == 2:
            name = tmp[0].strip()
            line = tmp[1]

        # line = accessibles;features
        line = line.split(';')
        # Accessible Ids, expand and store the accessibles.
        unExpAcc = [self.nameIdDict[a.strip()] for a in line[0].split()]
        if len(self.expandedAccessibles.keys())>=100:
            self.expandedAccessibles = {}
            self.changed = True
        for accId in unExpAcc:
            if not self.expandedAccessibles.has_key(accId):
                accIdAcc = self.accessibleDict[accId]
                self.expandedAccessibles[accId] = self.expand_accessibles(accIdAcc)
                self.changed = True
        accessibles = self.expand_accessibles(unExpAcc)
        features = self.get_features(line)
        # Get hints:
        if len(line) == 3:
            hints = [self.nameIdDict[d.strip()] for d in line[2].split()]
        else:
            hints = []

        return name,features,accessibles,hints

    def save(self,fileName):
        if self.changed:
            dictsStream = open(fileName, 'wb')
            dump((self.accessibleDict,self.dependenciesDict,self.expandedAccessibles,self.featureDict,\
                self.featureIdDict,self.idNameDict,self.maxFeatureId,self.maxNameId,self.nameIdDict,self.featureCountDict,self.triggerFeatures),dictsStream)
            self.changed = False
            dictsStream.close()
    def load(self,fileName):
        dictsStream = open(fileName, 'rb')
        self.accessibleDict,self.dependenciesDict,self.expandedAccessibles,self.featureDict,\
              self.featureIdDict,self.idNameDict,self.maxFeatureId,self.maxNameId,self.nameIdDict,self.featureCountDict,self.triggerFeatures = load(dictsStream)
        self.changed = False
        dictsStream.close()
