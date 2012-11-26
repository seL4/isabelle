#     Title:      HOL/Tools/Sledgehammer/MaSh/src/snow.py
#     Author:     Daniel Kuehlwein, ICIS, Radboud University Nijmegen
#     Copyright   2012
#
# Wrapper for SNoW.

'''
THIS FILE IS NOT UP TO DATE!
NEEDS SOME FIXING BEFORE IT WILL WORK WITH THE MAIN ALGORITHM

Created on Jul 12, 2012

@author: daniel
'''

import logging,shlex,subprocess,string
from cPickle import load,dump

class SNoW(object):
    '''
    Calls the SNoW framework.
    '''

    def __init__(self):
        '''
        Constructor
        '''
        self.logger = logging.getLogger('SNoW')
        self.SNoWTrainFile = '../tmp/snow.train'
        self.SNoWTestFile = '../snow.test'  
        self.SNoWNetFile = '../tmp/snow.net' 
    
    def initializeModel(self,trainData,dicts):
        """
        Build basic model from training data.
        """     
        # Prepare input files
        self.logger.debug('Creating IO Files')
        OS = open(self.SNoWTrainFile,'w')
        for nameId in trainData:
            features = [f+dicts.maxNameId for f in dicts.featureDict[nameId]]
            features = map(str,features)
            featureString = string.join(features,',')
            dependencies = dicts.dependenciesDict[nameId]
            dependencies = map(str,dependencies)
            dependenciesString = string.join(dependencies,',')
            snowString = string.join([featureString,dependenciesString],',')+':\n' 
            OS.write(snowString)
        OS.close()

        # Build Model
        self.logger.debug('Building Model START.')
        snowTrainCommand = '../bin/snow -train -M+ -I %s -F %s -g- -B :0-%s' % (self.SNoWTrainFile,self.SNoWNetFile,dicts.maxNameId-1)    
        args = shlex.split(snowTrainCommand)
        p = subprocess.Popen(args,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)    
        p.wait()
        self.logger.debug('Building Model END.')   

    
    def update(self,dataPoint,features,dependencies,dicts):
        """
        Updates the Model.
        THIS IS NOT WORKING ATM< BUT WE DONT CARE
        """        
        self.logger.debug('Updating Model START') 
        trainData = dicts.featureDict.keys()       
        self.initializeModel(trainData,dicts)
        self.logger.debug('Updating Model END')
            
    
    def predict(self,features,accessibles,dicts):
        logger = logging.getLogger('predict_SNoW')
         
        OS = open(self.SNoWTestFile,'w')
        features = map(str,features)
        featureString = string.join(features, ',')
        snowString = featureString+':'
        OS.write(snowString)
        OS.close() 
        
        snowTestCommand = '../bin/snow -test -I %s -F %s -o allboth' % (self.SNoWTestFile,self.SNoWNetFile)
        args = shlex.split(snowTestCommand)
        p = subprocess.Popen(args,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)    
        (lines, _stderrdata) = p.communicate()
        logger.debug('SNoW finished.')
        lines = lines.split('\n')    
        assert lines[9].startswith('Example ')
        assert lines[-4] == ''
        predictionsCon = []    
        for line in lines[10:-4]:
            premiseId = int(line.split()[0][:-1])
            predictionsCon.append(premiseId)
        return predictionsCon
    
    def save(self,fileName):
        OStream = open(fileName, 'wb')
        dump(self.counts,OStream)        
        OStream.close()
        
    def load(self,fileName):
        OStream = open(fileName, 'rb')
        self.counts = load(OStream)      
        OStream.close()