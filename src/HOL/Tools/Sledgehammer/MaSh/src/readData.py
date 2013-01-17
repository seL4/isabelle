#     Title:      HOL/Tools/Sledgehammer/MaSh/src/readData.py
#     Author:     Daniel Kuehlwein, ICIS, Radboud University Nijmegen
#     Copyright   2012
#
# All functions to read the Isabelle output.

'''
All functions to read the Isabelle output.

Created on July 9, 2012

@author: Daniel Kuehlwein
'''

import sys,logging

def create_feature_dict(nameIdDict,idNameDict,maxNameId,featureIdDict,maxFeatureId,featureCountDict,\
                        triggerFeaturesDict,featureTriggeredFormulasDict,sineFeatures,inputFile):
    logger = logging.getLogger('create_feature_dict')
    featureDict = {}
    IS = open(inputFile,'r')
    for line in IS:
        line = line.split(':')
        name = line[0]
        # Name Id
        if nameIdDict.has_key(name):
            logger.warning('%s appears twice in the feature file. Aborting.',name)
            sys.exit(-1)
        else:
            nameIdDict[name] = maxNameId
            idNameDict[maxNameId] = name
            nameId = maxNameId
            maxNameId += 1
        # Feature Ids
        featureNames = [f.strip() for f in line[1].split()]
        features = []     
        minFeatureCount = 9999999   
        for fn in featureNames:
            weight = 1.0
            tmp = fn.split('=')
            if len(tmp) == 2:
                fn = tmp[0]
                weight = float(tmp[1])
            if not featureIdDict.has_key(fn):
                featureIdDict[fn] = maxFeatureId
                featureCountDict[maxFeatureId] = 0
                maxFeatureId += 1
            fId = featureIdDict[fn]
            features.append((fId,weight))
            if sineFeatures:
                featureCountDict[fId] += 1
                minFeatureCount = min(minFeatureCount,featureCountDict[fId])
        # Store results
        featureDict[nameId] = features
        if sineFeatures:
            triggerFeatures = [f for f,_w in features if featureCountDict[f] == minFeatureCount]
            triggerFeaturesDict[nameId] = triggerFeatures
            for f in triggerFeatures:
                if featureTriggeredFormulasDict.has_key(f): 
                    featureTriggeredFormulasDict[f].append(nameId)
                else:
                    featureTriggeredFormulasDict[f] = [nameId]
    IS.close()
    return featureDict,maxNameId,maxFeatureId,featureCountDict,triggerFeaturesDict,featureTriggeredFormulasDict

def create_dependencies_dict(nameIdDict,inputFile):
    logger = logging.getLogger('create_dependencies_dict')
    dependenciesDict = {}
    IS = open(inputFile,'r')
    for line in IS:
        line = line.split(':')
        name = line[0]
        # Name Id
        if not nameIdDict.has_key(name):
            logger.warning('%s is missing in nameIdDict. Aborting.',name)
            sys.exit(-1)

        nameId = nameIdDict[name]
        dependenciesIds = [nameIdDict[f.strip()] for f in line[1].split()]
        # Store results, add p proves p
        dependenciesDict[nameId] = [nameId] + dependenciesIds
    IS.close()
    return dependenciesDict

def create_accessible_dict(nameIdDict,idNameDict,maxNameId,inputFile):
    logger = logging.getLogger('create_accessible_dict')
    accessibleDict = {}
    IS = open(inputFile,'r')
    for line in IS:
        line = line.split(':')
        name = line[0]
        # Name Id
        if not nameIdDict.has_key(name):
            logger.warning('%s is missing in nameIdDict. Adding it as theory.',name)
            nameIdDict[name] = maxNameId
            idNameDict[maxNameId] = name
            nameId = maxNameId
            maxNameId += 1
        else:
            nameId = nameIdDict[name]
        accessibleStrings = line[1].split()
        accessibleDict[nameId] = [nameIdDict[a.strip()] for a in accessibleStrings]
    IS.close()
    return accessibleDict,maxNameId
