#     Title:      HOL/Tools/Sledgehammer/MaSh/src/predefined.py
#     Author:     Daniel Kuehlwein, ICIS, Radboud University Nijmegen
#     Copyright   2012
#
# A classifier that uses the Meng-Paulson predictions.

'''
Created on Jul 11, 2012

@author: Daniel Kuehlwein
'''

from cPickle import dump,load

class Predefined(object):
    '''
    A classifier that uses the Meng-Paulson predictions.
    Only used to easily compare statistics between the old Sledgehammer algorithm and the new machine learning ones.
    '''

    def __init__(self,mpPredictionFile):
        '''
        Constructor
        '''
        self.predictionFile = mpPredictionFile

    def initializeModel(self,_trainData,dicts):
        """
        Load predictions.
        """
        self.predictions = {}
        IS = open(self.predictionFile,'r')
        for line in IS:
            line = line.split(':')
            name = line[0].strip()
            predId = dicts.get_name_id(name)
            line = line[1].split()
            predsTmp = []
            for x in line:
                x = x.split('=')
                predsTmp.append(x[0])
            preds = [dicts.get_name_id(x.strip())for x in predsTmp]
            self.predictions[predId] = preds
        IS.close()        

    def update(self,dataPoint,features,dependencies):
        """
        Updates the Model.
        """
        # No Update needed since we assume that we got all predictions
        pass


    def predict(self,problemId):
        """
        Return the saved predictions.
        """
        return self.predictions[problemId]

    def save(self,fileName):
        OStream = open(fileName, 'wb')
        dump((self.predictionFile,self.predictions),OStream)
        OStream.close()

    def load(self,fileName):
        OStream = open(fileName, 'rb')
        self.predictionFile,self.predictions = load(OStream)
        OStream.close()
