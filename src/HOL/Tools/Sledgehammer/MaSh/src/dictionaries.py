#     Title:      HOL/Tools/Sledgehammer/MaSh/src/dictionaries.py
#     Author:     Daniel Kuehlwein, ICIS, Radboud University Nijmegen
#     Copyright   2012-2013
#
# Persistent dictionaries: accessibility, dependencies, and features.

import sys
from os.path import join
from Queue import Queue
from readData import create_accessible_dict,create_dependencies_dict
from cPickle import load,dump
from exceptions import LookupError

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
        self.maxNameId = 1
        self.maxFeatureId = 0
        self.featureDict = {}
        self.dependenciesDict = {}
        self.accessibleDict = {}
        self.expandedAccessibles = {}
        self.accFile =  ''
        self.changed = True
        # Unnamed facts
        self.nameIdDict[''] = 0
        self.idNameDict[0] = 'Unnamed Fact'

    """
    Init functions. nameIdDict, idNameDict, featureIdDict, articleDict get filled!
    """
    def init_featureDict(self,featureFile):
        self.create_feature_dict(featureFile)
        #self.featureDict,self.maxNameId,self.maxFeatureId,self.featureCountDict,self.triggerFeaturesDict,self.featureTriggeredFormulasDict =\
        # create_feature_dict(self.nameIdDict,self.idNameDict,self.maxNameId,self.featureIdDict,self.maxFeatureId,self.featureCountDict,\
        #                     self.triggerFeaturesDict,self.featureTriggeredFormulasDict,sineFeatures,featureFile)
    def init_dependenciesDict(self,depFile):
        self.dependenciesDict = create_dependencies_dict(self.nameIdDict,depFile)
    def init_accessibleDict(self,accFile):
        self.accessibleDict,self.maxNameId = create_accessible_dict(self.nameIdDict,self.idNameDict,self.maxNameId,accFile)

    def init_all(self,args):
        self.featureFileName = 'mash_features'
        self.accFileName = 'mash_accessibility'
        featureFile = join(args.inputDir,self.featureFileName)
        depFile = join(args.inputDir,args.depFile)
        self.accFile = join(args.inputDir,self.accFileName)
        self.init_featureDict(featureFile)
        self.init_accessibleDict(self.accFile)
        self.init_dependenciesDict(depFile)
        self.expandedAccessibles = {}
        self.changed = True

    def create_feature_dict(self,inputFile):
        self.featureDict = {}
        IS = open(inputFile,'r')
        for line in IS:
            line = line.split(':')
            name = line[0]
            # Name Id
            if self.nameIdDict.has_key(name):
                raise LookupError('%s appears twice in the feature file. Aborting.'% name)
                sys.exit(-1)
            else:
                self.nameIdDict[name] = self.maxNameId
                self.idNameDict[self.maxNameId] = name
                nameId = self.maxNameId
                self.maxNameId += 1
            features = self.get_features(line)
            # Store results
            self.featureDict[nameId] = features
        IS.close()
        return

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
        fMul = featureName.split('|')        
        fIds = []
        for f in fMul:
            if not self.featureIdDict.has_key(f):
                self.featureIdDict[f] = self.maxFeatureId
                self.maxFeatureId += 1
                self.changed = True
            fId = self.featureIdDict[f]
            fIds.append(fId)
        if len(fIds) == 1:
            return fIds[0]
        else:
            return fIds

    def get_features(self,line):
        featureNames = [f.strip() for f in line[1].split()]
        features = {}
        for fn in featureNames:
            tmp = fn.split('=')
            weight = 1.0 
            if len(tmp) == 2:
                fn = tmp[0]
                weight = float(tmp[1])
            fId = self.add_feature(tmp[0])
            features[fId] = weight
            #features[fId] = 1.0 ###
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

    def parse_unExpAcc(self,line):
        try:
            unExpAcc = [self.nameIdDict[a.strip()] for a in line.split()]            
        except:
            raise LookupError('Cannot find the accessibles:%s. Accessibles need to be introduced before referring to them.' % line)
        return unExpAcc

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
        features = self.get_features(line)
        self.featureDict[nameId] = features
        try:
            self.dependenciesDict[nameId] = [self.nameIdDict[d.strip()] for d in line[2].split()]        
        except:
            unknownDeps = []
            for d in line[2].split():
                if not self.nameIdDict.has_key(d):
                    unknownDeps.append(d)
            raise LookupError('Unknown fact used as dependency: %s. Facts need to be introduced before being used as depedency.' % ','.join(unknownDeps))
        self.accessibleDict[nameId] = self.parse_unExpAcc(line[0])

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
        try:
            nameId = self.nameIdDict[name]
        except:
            raise LookupError('Trying to overwrite dependencies for unknown fact: %s. Facts need to be introduced before overwriting them.' % name)
        try:
            dependencies = [self.nameIdDict[d.strip()] for d in line[1].split()]
        except:
            unknownDeps = []
            for d in line[1].split():
                if not self.nameIdDict.has_key(d):
                    unknownDeps.append(d)
            raise LookupError('Unknown fact used as dependency: %s. Facts need to be introduced before being used as depedency.' % ','.join(unknownDeps))
        self.changed = True
        return nameId,dependencies

    def parse_problem(self,line):
        """
        Parses a problem and returns the features, the accessibles, and any hints.
        """
        assert line.startswith('? ')
        line = line[2:]
        name = None
        numberOfPredictions = None

        # How many predictions should be returned:
        tmp = line.split('#')
        if len(tmp) == 2:
            numberOfPredictions = int(tmp[0].strip())
            line = tmp[1]

        # Check whether there is a problem name:
        tmp = line.split(':')
        if len(tmp) == 2:
            name = tmp[0].strip()
            line = tmp[1]

        # line = accessibles;features
        line = line.split(';')
        features = self.get_features(line)
        
        # Accessible Ids, expand and store the accessibles.
        #unExpAcc = [self.nameIdDict[a.strip()] for a in line[0].split()]
        unExpAcc = self.parse_unExpAcc(line[0])        
        if len(self.expandedAccessibles.keys())>=100:
            self.expandedAccessibles = {}
            self.changed = True
        for accId in unExpAcc:
            if not self.expandedAccessibles.has_key(accId):
                accIdAcc = self.accessibleDict[accId]
                self.expandedAccessibles[accId] = self.expand_accessibles(accIdAcc)
                self.changed = True
        accessibles = self.expand_accessibles(unExpAcc)
        
        # Get hints:
        if len(line) == 3:
            hints = [self.nameIdDict[d.strip()] for d in line[2].split()]
        else:
            hints = []

        return name,features,accessibles,hints,numberOfPredictions

    def save(self,fileName):
        if self.changed:
            dictsStream = open(fileName, 'wb')
            dump((self.accessibleDict,self.dependenciesDict,self.expandedAccessibles,self.featureDict,\
                self.featureIdDict,self.idNameDict,self.maxFeatureId,self.maxNameId,self.nameIdDict),dictsStream)
            self.changed = False
            dictsStream.close()
    def load(self,fileName):
        dictsStream = open(fileName, 'rb')
        self.accessibleDict,self.dependenciesDict,self.expandedAccessibles,self.featureDict,\
              self.featureIdDict,self.idNameDict,self.maxFeatureId,self.maxNameId,self.nameIdDict = load(dictsStream)
        self.changed = False
        dictsStream.close()
