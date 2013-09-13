'''
Created on Aug 21, 2013

@author: daniel
'''

from math import log
from KNN import KNN,cosine
from numpy import array

class KNNAdaptPointFeatures(KNN):
    
    def __init__(self,dicts,metric=cosine,alpha = 0.05):
        self.points = dicts.featureDict
        self.metric = self.euclidean    
        self.alpha = alpha
        self.count = 0
        self.featureCount = {}

    def initializeModel(self,trainData,dicts):  
        """
        Build basic model from training data.
        """
        IS = open(dicts.accFile,'r')
        for line in IS:
            line = line.split(':')
            name = line[0]
            nameId = dicts.nameIdDict[name]
            features = dicts.featureDict[nameId]
            dependencies = dicts.dependenciesDict[nameId] 
            self.update(nameId, features, dependencies)
        IS.close()
        
    def update(self,dataPoint,features,dependencies):
        self.count += 1
        for f in features.iterkeys():
            try:
                self.featureCount[f] += 1
            except:
                self.featureCount[f] = 1
        for d in dependencies:
            dFeatures = self.points[d]
            featureUnion = set(dFeatures.keys()) | set(features.keys())
            for f in featureUnion:
                try:
                    pVal = features[f]
                except:
                    pVal = 0.0
                try:
                    dVal = dFeatures[f]
                except:
                    dVal = 0.0
                newDVal = dVal + self.alpha * (pVal - dVal)                
                dFeatures[f] = newDVal           
        
    def euclidean(self,f1,f2):
        diffSum = 0.0        
        f1Set = set(f1.keys())
        featureUnion = f1Set | set(f2.keys())
        for f in featureUnion:
            if not self.featureCount.has_key(f):
                continue
            if self.featureCount[f] == 1:
                continue
            try:
                f1Val = f1[f]
            except:
                f1Val = 0.0
            try:
                f2Val = f2[f]
            except:
                f2Val = 0.0
            diff = f1Val - f2Val
            diffSum += diff * diff
            if f in f1Set:
                diffSum += log(2+self.count/self.featureCount[f]) * diff * diff
            else:
                diffSum += diff * diff            
        #print diffSum,f1,f2
        return diffSum 

class KNNUrban(KNN):
    def __init__(self,dicts,metric=cosine,nrOfNeighbours = 40):
        self.points = dicts.featureDict
        self.metric = metric    
        self.nrOfNeighbours = nrOfNeighbours # Ignored at the moment
    
    def predict(self,features,accessibles,dicts):
        predictions = map(lambda x: self.metric(features,self.points[x]),accessibles)
        pDict = dict(zip(accessibles,predictions))
        for a,p in zip(accessibles,predictions):
            aDeps = dicts.dependenciesDict[a]
            for d in aDeps:
                pDict[d] -= p 
        predictions = []
        names = []
        for n,p in pDict.items():
            predictions.append(p)
            names.append(n)        
        predictions = array(predictions)
        perm = predictions.argsort()
        return array(names)[perm],predictions[perm]
    
    
         