'''
Created on Aug 21, 2013

@author: daniel
'''

from cPickle import dump,load
from numpy import array
from math import sqrt,log

def cosine(f1,f2):
    f1Norm = 0.0
    for f in f1.keys():
        f1Norm += f1[f] * f1[f]
    #assert f1Norm = sum(map(lambda x,y: x*y,f1.itervalues(),f1.itervalues()))
    f1Norm = sqrt(f1Norm) 
    
    f2Norm = 0.0
    for f in f2.keys():
        f2Norm += f2[f] * f2[f]
    f2Norm = sqrt(f2Norm)         
   
    dotProduct = 0.0
    featureIntersection = set(f1.keys()) & set(f2.keys())
    for f in featureIntersection:
            dotProduct += f1[f] * f2[f]
    cosine = dotProduct / (f1Norm * f2Norm)        
    return 1.0 - cosine

def euclidean(f1,f2):
    diffSum = 0.0        
    featureUnion = set(f1.keys()) | set(f2.keys())
    for f in featureUnion:
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
        #if f in f1.keys():
        #    diffSum += log(2+self.pointCount/self.featureCounts[f]) * diff * diff
        #else:
        #    diffSum += diff * diff            
    #print diffSum,f1,f2
    return diffSum

class KNN(object):
    '''
    A basic KNN ranker.
    '''

    def __init__(self,dicts,metric=cosine):
        '''
        Constructor
        '''
        self.points = dicts.featureDict
        self.metric = metric

    def initializeModel(self,_trainData,_dicts):  
        """
        Build basic model from training data.
        """
        pass
    
    def update(self,dataPoint,features,dependencies):
        assert self.points[dataPoint] == features
        
    def overwrite(self,problemId,newDependencies,dicts):
        # Taken care of by dicts
        pass
    
    def delete(self,dataPoint,features,dependencies):
        # Taken care of by dicts
        pass      
    
    def predict(self,features,accessibles,dicts):
        predictions = map(lambda x: self.metric(features,self.points[x]),accessibles)
        predictions = array(predictions)
        perm = predictions.argsort()
        return array(accessibles)[perm],predictions[perm]
    
    def save(self,fileName):
        OStream = open(fileName, 'wb')
        dump((self.points,self.metric),OStream)
        OStream.close()

    def load(self,fileName):
        OStream = open(fileName, 'rb')
        self.points,self.metric = load(OStream)
        OStream.close()

if __name__ == '__main__':
    pass    
        
        