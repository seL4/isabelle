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
