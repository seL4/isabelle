'''
Created on Aug 21, 2013

@author: daniel
'''

from math import log
from gensim import corpora, models, similarities

class ExpandFeatures(object):

    def __init__(self,dicts):
        self.dicts = dicts
        self.featureMap = {}
        self.alpha = 0.1
        self.featureCounts = {}
        self.counter = 0        
        self.corpus = []
        self.LSIModel = models.lsimodel.LsiModel(self.corpus,num_topics=500)

    def initialize(self,dicts):
        self.dicts = dicts
        IS = open(dicts.accFile,'r')
        for line in IS:
            line = line.split(':')
            name = line[0]
            #print 'name',name
            nameId = dicts.nameIdDict[name]    
            features = dicts.featureDict[nameId]
            dependencies = dicts.dependenciesDict[nameId]   
            x = [self.dicts.idNameDict[d] for d in dependencies]
            #print x  
            self.update(features, dependencies)
            self.corpus.append([(x,1) for x in features.keys()])
        IS.close()
        print 'x'
        #self.LSIModel = models.lsimodel.LsiModel(self.corpus,num_topics=500)
        print self.LSIModel
        print 'y'
        
    def update(self,features,dependencies):
        self.counter += 1
        self.corpus.append([(x,1) for x in features.keys()])
        self.LSIModel.add_documents([[(x,1) for x in features.keys()]])
        """
        for f in features.iterkeys():
            try:
                self.featureCounts[f] += 1
            except:
                self.featureCounts[f] = 1
            if self.featureCounts[f] > 100:
                continue
            try:
                self.featureMap[f] = self.featureMap[f].intersection(features.keys())
            except:
                self.featureMap[f] = set(features.keys())
            #print 'fOld',len(fMap),self.featureCounts[f],len(dependencies)

            for d in dependencies[1:]:
                #print 'dep',self.dicts.idNameDict[d]
                dFeatures = self.dicts.featureDict[d]
                for df in dFeatures.iterkeys():
                    if self.featureCounts.has_key(df):
                        if self.featureCounts[df] > 20:
                            continue
                    else:
                        print df
                    try:
                        fMap[df] += self.alpha * (1.0 - fMap[df])
                    except:
                        fMap[df] = self.alpha
            """
            #print 'fNew',len(fMap)
            
    def expand(self,features):
        #print self.corpus[:50]        
        #print corpus
        #tfidfmodel = models.TfidfModel(self.corpus, normalize=True)        
        #print features.keys()        
        #tfidfcorpus = [tfidfmodel[x] for x in self.corpus]
        #newFeatures = LSI[[(x,1) for x in features.keys()]]
        newFeatures = self.LSIModel[[(x,1) for x in features.keys()]]
        print features
        print newFeatures
        #print newFeatures
        
        """
        newFeatures = dict(features)
        for f in features.keys():
            try:
                fC = self.featureCounts[f]
            except:
                fC = 0.5
            newFeatures[f] = log(float(8+self.counter) / fC)
        #nrOfFeatures = float(len(features))
        addedCount = 0
        alpha = 0.2
        #"""
        
        """
        consideredFeatures = []
        while len(newFeatures) < 30:
            #alpha = alpha * 0.5
            minF = None
            minFrequence = 1000000
            for f in newFeatures.iterkeys():
                if f in consideredFeatures:
                    continue
                try:
                    if self.featureCounts[f] < minFrequence:
                        minF = f
                except:
                    pass
            if minF == None:
                break
            # Expand minimal feature
            consideredFeatures.append(minF)
            for expF in self.featureMap[minF]:
                if not newFeatures.has_key(expF):
                    fC = self.featureCounts[minF]
                    newFeatures[expF] = alpha*log(float(8+self.counter) / fC)
        #print features, newFeatures
        #"""
        """
        for f in features.iterkeys():
            try:
                self.featureCounts[f] += 1
            except:
                self.featureCounts[f] = 0            
            if self.featureCounts[f] > 10:
                continue            
            addedCount += 1
            try:
                fmap = self.featureMap[f]
            except:
                self.featureMap[f] = {}
                fmap = {}
            for nf,nv in fmap.iteritems():
                try:
                    newFeatures[nf] += nv
                except:
                    newFeatures[nf] = nv
        if addedCount > 0: 
            for f,w in newFeatures.iteritems():
                newFeatures[f] = float(w)/addedCount
        #"""                    
        """
        deleteF = []
        for f,w in newFeatures.iteritems():
            if w < 0.1:
                deleteF.append(f)
        for f in deleteF:
            del newFeatures[f]
        """
        #print 'fold',len(features)
        #print 'fnew',len(newFeatures)
        return dict(newFeatures)

if __name__ == "__main__":
    pass
    
        