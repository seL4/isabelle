#     Title:      HOL/Tools/Sledgehammer/MaSh/src/snow.py
#     Author:     Daniel Kuehlwein, ICIS, Radboud University Nijmegen
#     Copyright   2012
#
# Wrapper for SNoW.

'''

Created on Jul 12, 2012

@author: daniel
'''

import logging,shlex,subprocess,string,shutil
#from cPickle import load,dump

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
        self.defMaxNameId = 100000

    def initializeModel(self,trainData,dicts):
        """
        Build basic model from training data.
        """
        # Prepare input files
        self.logger.debug('Creating IO Files')
        OS = open(self.SNoWTrainFile,'w')
        for nameId in trainData:
            features = [f+dicts.maxNameId for f,_w in dicts.featureDict[nameId]]
            #features = [f+self.defMaxNameId for f,_w in dicts.featureDict[nameId]]
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
        #print snowTrainCommand
        #snowTrainCommand = '../bin/snow -train -M+ -I %s -F %s -g- -B :0-%s' % (self.SNoWTrainFile,self.SNoWNetFile,self.defMaxNameId-1)
        args = shlex.split(snowTrainCommand)
        p = subprocess.Popen(args,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        p.wait()
        self.logger.debug('Building Model END.')

    def update(self,dataPoint,features,dependencies,dicts):
        """
        Updates the Model.
        """
        """
        self.logger.debug('Updating Model START')
        # Ignore Feature weights        
        features = [f+self.defMaxNameId for f,_w in features]
        
        OS = open(self.SNoWTestFile,'w')
        features = map(str,features)
        featureString = string.join(features, ',')
        dependencies = map(str,dependencies)
        dependenciesString = string.join(dependencies,',')
        snowString = string.join([featureString,dependenciesString],',')+':\n'
        OS.write(snowString)
        OS.close()
        snowTestCommand = '../bin/snow -test -I %s -F %s -o allboth -i+' % (self.SNoWTestFile,self.SNoWNetFile) 
        args = shlex.split(snowTestCommand)
        p = subprocess.Popen(args,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        (_lines, _stderrdata) = p.communicate()
        # Move new net file        
        src = self.SNoWNetFile+'.new'
        dst = self.SNoWNetFile
        shutil.move(src, dst)        
        self.logger.debug('Updating Model END')
        """
        # Do nothing, only update at evaluation. Is a lot faster.
        pass


    def predict(self,features,accessibles,dicts):
        trainData = dicts.featureDict.keys()
        self.initializeModel(trainData, dicts)        
        
        logger = logging.getLogger('predict_SNoW')        
        # Ignore Feature weights
        #features = [f+self.defMaxNameId for f,_w in features]
        features = [f+dicts.maxNameId for f,_w in features]

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
        predictionsValues = []
        for line in lines[10:-4]:
            premiseId = int(line.split()[0][:-1])
            predictionsCon.append(premiseId)
            val = line.split()[4]
            if val.endswith('*'):
                val = float(val[:-1])
            else:
                val = float(val)
            predictionsValues.append(val)
        return predictionsCon,predictionsValues

    def save(self,fileName):
        # Nothing to do since we don't update
        pass
    
    def load(self,fileName):
        # Nothing to do since we don't update
        pass
