#!/usr/bin/python
#     Title:      HOL/Tools/Sledgehammer/MaSh/src/mash.py
#     Author:     Daniel Kuehlwein, ICIS, Radboud University Nijmegen
#     Copyright   2012
#
# Entry point for MaSh (Machine Learning for Sledgehammer).

'''
MaSh - Machine Learning for Sledgehammer

MaSh allows to use different machine learning algorithms to predict relevant fact for Sledgehammer.

Created on July 12, 2012

@author: Daniel Kuehlwein
'''

import logging,datetime,string,os,sys
from argparse import ArgumentParser,RawDescriptionHelpFormatter
from time import time
from stats import Statistics
from theoryStats import TheoryStatistics
from theoryModels import TheoryModels
from dictionaries import Dictionaries
#from fullNaiveBayes import NBClassifier
from sparseNaiveBayes import sparseNBClassifier
from snow import SNoW
from predefined import Predefined

# Set up command-line parser
parser = ArgumentParser(description='MaSh - Machine Learning for Sledgehammer.  \n\n\
MaSh allows to use different machine learning algorithms to predict relevant facts for Sledgehammer.\n\n\
--------------- Example Usage ---------------\n\
First initialize:\n./mash.py -l test.log -o ../tmp/ --init --inputDir ../data/Jinja/ \n\
Then create predictions:\n./mash.py -i ../data/Jinja/mash_commands -p ../data/Jinja/mash_suggestions -l test.log -o ../tmp/ --statistics\n\
\n\n\
Author: Daniel Kuehlwein, July 2012',formatter_class=RawDescriptionHelpFormatter)
parser.add_argument('-i','--inputFile',help='File containing all problems to be solved.')
parser.add_argument('-o','--outputDir', default='../tmp/',help='Directory where all created files are stored. Default=../tmp/.')
parser.add_argument('-p','--predictions',default='../tmp/%s.predictions' % datetime.datetime.now(),
                    help='File where the predictions stored. Default=../tmp/dateTime.predictions.')
parser.add_argument('--numberOfPredictions',default=200,help="Number of premises to write in the output. Default=200.",type=int)

parser.add_argument('--init',default=False,action='store_true',help="Initialize Mash. Requires --inputDir to be defined. Default=False.")
parser.add_argument('--inputDir',default='../data/20121212/Jinja/',\
                    help='Directory containing all the input data. MaSh expects the following files: mash_features,mash_dependencies,mash_accessibility')
parser.add_argument('--depFile', default='mash_dependencies',
                    help='Name of the file with the premise dependencies. The file must be in inputDir. Default = mash_dependencies')
parser.add_argument('--saveModel',default=False,action='store_true',help="Stores the learned Model at the end of a prediction run. Default=False.")
parser.add_argument('--learnTheories',default=False,action='store_true',help="Uses a two-lvl prediction mode. First the theories, then the premises. Default=False.")


parser.add_argument('--nb',default=False,action='store_true',help="Use Naive Bayes for learning. This is the default learning method.")
parser.add_argument('--snow',default=False,action='store_true',help="Use SNoW's naive bayes instead of Naive Bayes for learning.")
parser.add_argument('--predef',default=False,action='store_true',\
                    help="Use predefined predictions. Used only for comparison with the actual learning. Expects mash_mepo_suggestions in inputDir.")
parser.add_argument('--statistics',default=False,action='store_true',help="Create and show statistics for the top CUTOFF predictions.\
                    WARNING: This will make the program a lot slower! Default=False.")
parser.add_argument('--saveStats',default=None,help="If defined, stores the statistics in the filename provided.")
parser.add_argument('--cutOff',default=500,help="Option for statistics. Only consider the first cutOff predictions. Default=500.",type=int)
parser.add_argument('-l','--log', default='../tmp/%s.log' % datetime.datetime.now(), help='Log file name. Default=../tmp/dateTime.log')
parser.add_argument('-q','--quiet',default=False,action='store_true',help="If enabled, only print warnings. Default=False.")

def main(argv = sys.argv[1:]):
    # Initializing command-line arguments
    args = parser.parse_args(argv)

    # Set up logging
    logging.basicConfig(level=logging.DEBUG,
                        format='%(asctime)s %(name)-12s %(levelname)-8s %(message)s',
                        datefmt='%d-%m %H:%M:%S',
                        filename=args.log,
                        filemode='w')
    console = logging.StreamHandler(sys.stdout)
    console.setLevel(logging.INFO)
    formatter = logging.Formatter('# %(message)s')
    console.setFormatter(formatter)
    logging.getLogger('').addHandler(console)
    logger = logging.getLogger('main.py')
    if args.quiet:
        logger.setLevel(logging.WARNING)
        console.setLevel(logging.WARNING)
    if not os.path.exists(args.outputDir):
        os.makedirs(args.outputDir)

    logger.info('Using the following settings: %s',args)
    # Pick algorithm
    if args.nb:
        logger.info('Using sparse Naive Bayes for learning.')
        model = sparseNBClassifier()
        modelFile = os.path.join(args.outputDir,'NB.pickle')
    elif args.snow:
        logger.info('Using naive bayes (SNoW) for learning.')
        model = SNoW()
        modelFile = os.path.join(args.outputDir,'SNoW.pickle')
    elif args.predef:
        logger.info('Using predefined predictions.')
        #predictionFile = os.path.join(args.inputDir,'mash_meng_paulson_suggestions') 
        predictionFile = os.path.join(args.inputDir,'mash_mepo_suggestions')
        model = Predefined(predictionFile)
        modelFile = os.path.join(args.outputDir,'mepo.pickle')        
    else:
        logger.info('No algorithm specified. Using sparse Naive Bayes.')
        model = sparseNBClassifier()
        modelFile = os.path.join(args.outputDir,'NB.pickle')
    dictsFile = os.path.join(args.outputDir,'dicts.pickle')
    theoryFile = os.path.join(args.outputDir,'theory.pickle')

    # Initializing model
    if args.init:
        logger.info('Initializing Model.')
        startTime = time()

        # Load all data
        dicts = Dictionaries()
        dicts.init_all(args.inputDir,depFileName=args.depFile)
        
        # Create Model
        trainData = dicts.featureDict.keys()
        model.initializeModel(trainData,dicts)

        if args.learnTheories:
            depFile = os.path.join(args.inputDir,args.depFile)
            theoryModels = TheoryModels()
            theoryModels.init(depFile,dicts)
            theoryModels.save(theoryFile)
            
        model.save(modelFile)
        dicts.save(dictsFile)

        logger.info('All Done. %s seconds needed.',round(time()-startTime,2))
        return 0
    # Create predictions and/or update model
    else:
        lineCounter = 1
        statementCounter = 1
        computeStats = False
        dicts = Dictionaries()
        theoryModels = TheoryModels()
        # Load Files
        if os.path.isfile(dictsFile):
            dicts.load(dictsFile)
        if os.path.isfile(modelFile):
            model.load(modelFile)
        if os.path.isfile(theoryFile) and args.learnTheories:
            theoryModels.load(theoryFile)

        # IO Streams
        OS = open(args.predictions,'w')
        IS = open(args.inputFile,'r')

        # Statistics
        if args.statistics:
            stats = Statistics(args.cutOff)
            if args.learnTheories:
                theoryStats = TheoryStatistics()

        predictions = None
        predictedTheories = None
        #Reading Input File
        for line in IS:
#           try:
            if True:
                if line.startswith('!'):
                    problemId = dicts.parse_fact(line)                        
                    # Statistics
                    if args.statistics and computeStats:
                        computeStats = False
                        # Assume '!' comes after '?'
                        if args.predef:
                            predictions = model.predict(problemId)
                        if args.learnTheories:
                            tmp = [dicts.idNameDict[x] for x in dicts.dependenciesDict[problemId]]
                            usedTheories = set([x.split('.')[0] for x in tmp]) 
                            theoryStats.update((dicts.idNameDict[problemId]).split('.')[0],predictedTheories,usedTheories)                        
                        stats.update(predictions,dicts.dependenciesDict[problemId],statementCounter)
                        if not stats.badPreds == []:
                            bp = string.join([str(dicts.idNameDict[x]) for x in stats.badPreds], ',')
                            logger.debug('Bad predictions: %s',bp)

                    statementCounter += 1
                    # Update Dependencies, p proves p
                    dicts.dependenciesDict[problemId] = [problemId]+dicts.dependenciesDict[problemId]
                    if args.learnTheories:
                        theoryModels.update(problemId,dicts)
                    if args.snow:
                        model.update(problemId,dicts.featureDict[problemId],dicts.dependenciesDict[problemId],dicts)
                    else:
                        model.update(problemId,dicts.featureDict[problemId],dicts.dependenciesDict[problemId])
                elif line.startswith('p'):
                    # Overwrite old proof.
                    problemId,newDependencies = dicts.parse_overwrite(line)
                    newDependencies = [problemId]+newDependencies
                    model.overwrite(problemId,newDependencies,dicts)
                    if args.learnTheories:
                        theoryModels.overwrite(problemId,newDependencies,dicts)
                    dicts.dependenciesDict[problemId] = newDependencies
                elif line.startswith('?'):               
                    startTime = time()
                    computeStats = True
                    if args.predef:
                        continue
                    name,features,accessibles = dicts.parse_problem(line)    
                    # Create predictions
                    logger.info('Starting computation for problem on line %s',lineCounter)
                    if args.learnTheories:
                        predictedTheories,accessibles = theoryModels.predict(features,accessibles,dicts)
                    if args.snow:
                        predictions,predictionValues = model.predict(features,accessibles,dicts)
                    else:
                        predictions,predictionValues = model.predict(features,accessibles)
                    assert len(predictions) == len(predictionValues)
                    logger.info('Done. %s seconds needed.',round(time()-startTime,2))
                    # Output        
                    predictionNames = [str(dicts.idNameDict[p]) for p in predictions[:args.numberOfPredictions]]
                    predictionValues = [str(x) for x in predictionValues[:args.numberOfPredictions]]
                    predictionsStringList = ['%s=%s' % (predictionNames[i],predictionValues[i]) for i in range(len(predictionNames))]
                    predictionsString = string.join(predictionsStringList,' ')
                    outString = '%s: %s' % (name,predictionsString)
                    OS.write('%s\n' % outString)
                else:
                    logger.warning('Unspecified input format: \n%s',line)
                    sys.exit(-1)
                lineCounter += 1
            """
            except:
                logger.warning('An error occurred on line %s .',line)
                lineCounter += 1
                continue
            """
        OS.close()
        IS.close()

        # Statistics
        if args.statistics:
            if args.learnTheories:
                theoryStats.printAvg()
            stats.printAvg()

        # Save
        if args.saveModel:
            model.save(modelFile)
            if args.learnTheories:
                theoryModels.save(theoryFile)
        dicts.save(dictsFile)
        if not args.saveStats == None:
            if args.learnTheories:
                theoryStatsFile = os.path.join(args.outputDir,'theoryStats')
                theoryStats.save(theoryStatsFile)
            statsFile = os.path.join(args.outputDir,args.saveStats)
            stats.save(statsFile)
    return 0

if __name__ == '__main__':
    # Example:
    # Jinja
    # ISAR Theories
    #args = ['-l','testNB.log','-o','../tmp/','--statistics','--init','--inputDir','../data/20121221/Jinja/','--learnTheories']    
    #args = ['-i', '../data/20121221/Jinja/mash_commands','-p','../tmp/testNB.pred','-l','../tmp/testNB.log','--nb','-o','../tmp/','--statistics','--saveStats','../tmp/JinjaIsarNB.stats','--cutOff','500','--learnTheories']
    # ISAR NB
    #args = ['-l','testNB.log','-o','../tmp/','--statistics','--init','--inputDir','../data/20121221/Jinja/']    
    #args = ['-i', '../data/20121221/Jinja/mash_commands','-p','../tmp/testNB.pred','-l','../tmp/testNB.log','--nb','-o','../tmp/','--statistics','--saveStats','../tmp/JinjaIsarNB.stats','--cutOff','500']
    # ISAR MePo
    #args = ['-l','testIsabelle.log','-o','../tmp/','--statistics','--init','--inputDir','../data/20121212/Jinja/','--predef']
    #args = ['-i', '../data/20121212/Jinja/mash_commands','-p','../tmp/JinjaMePo.pred','-l','testIsabelle.log','--predef','-o','../tmp/','--statistics','--saveStats','../tmp/JinjaMePo.stats']
    # ISAR NB ATP
    #args = ['-l','testNB.log','-o','../tmp/','--statistics','--init','--inputDir','../data/20121212/Jinja/','--depFile','mash_atp_dependencies']    
    #args = ['-i', '../data/Jinja/mash_commands','-p','../tmp/testNB.pred','-l','../tmp/testNB.log','--nb','-o','../tmp/','--statistics','--saveStats','../tmp/JinjaIsarNB.stats','--cutOff','500','--depFile','mash_atp_dependencies']
    #args = ['-l','testIsabelle.log','-o','../tmp/','--statistics','--init','--inputDir','../data/Jinja/','--predef','--depFile','mash_atp_dependencies']
    #args = ['-i', '../data/Jinja/mash_commands','-p','../tmp/JinjaMePo.pred','-l','testIsabelle.log','--predef','-o','../tmp/','--statistics','--saveStats','../tmp/JinjaMePo.stats','--depFile','mash_atp_dependencies']
    #args = ['-l','testNB.log','-o','../tmp/','--statistics','--init','--inputDir','../data/Jinja/','--depFile','mash_atp_dependencies','--snow']    
    #args = ['-i', '../data/Jinja/mash_commands','-p','../tmp/testNB.pred','-l','../tmp/testNB.log','--snow','-o','../tmp/','--statistics','--saveStats','../tmp/JinjaIsarNB.stats','--cutOff','500','--depFile','mash_atp_dependencies']
    # ISAR Snow
    #args = ['-l','testNB.log','-o','../tmp/','--statistics','--init','--inputDir','../data/20121212/Jinja/','--snow']    
    #args = ['-i', '../data/20121212/Jinja/mash_commands','-p','../tmp/testNB.pred','-l','../tmp/testNB.log','--snow','-o','../tmp/','--statistics','--saveStats','../tmp/JinjaIsarNB.stats','--cutOff','500']
 


    # Probability
    # ISAR NB
    #args = ['-l','testNB.log','-o','../tmp/','--statistics','--init','--inputDir','../data/20121213/Probability/']    
    #args = ['-i', '../data/20121213/Probability/mash_commands','-p','../tmp/testNB.pred','-l','../tmp/testNB.log','--nb','-o','../tmp/','--statistics','--saveStats','../tmp/ProbIsarNB.stats','--cutOff','500']
    # ISAR MePo
    #args = ['-l','testIsabelle.log','-o','../tmp/','--statistics','--init','--inputDir','../data/20121213/Probability/','--predef']
    #args = ['-i', '../data/20121213/Probability/mash_commands','-p','../tmp/JinjaMePo.pred','-l','testIsabelle.log','--predef','-o','../tmp/','--statistics','--saveStats','../tmp/JinjaMePo.stats']
    # ISAR NB ATP
    #args = ['-l','testNB.log','-o','../tmp/','--statistics','--init','--inputDir','../data/20121212/Jinja/','--depFile','mash_atp_dependencies']    
    #args = ['-i', '../data/Jinja/mash_commands','-p','../tmp/testNB.pred','-l','../tmp/testNB.log','--nb','-o','../tmp/','--statistics','--saveStats','../tmp/JinjaIsarNB.stats','--cutOff','500','--depFile','mash_atp_dependencies']
    #args = ['-l','testIsabelle.log','-o','../tmp/','--statistics','--init','--inputDir','../data/Jinja/','--predef','--depFile','mash_atp_dependencies']
    #args = ['-i', '../data/Jinja/mash_commands','-p','../tmp/JinjaMePo.pred','-l','testIsabelle.log','--predef','-o','../tmp/','--statistics','--saveStats','../tmp/JinjaMePo.stats','--depFile','mash_atp_dependencies']
    #args = ['-l','testNB.log','-o','../tmp/','--statistics','--init','--inputDir','../data/Jinja/','--depFile','mash_atp_dependencies','--snow']    
    #args = ['-i', '../data/Jinja/mash_commands','-p','../tmp/testNB.pred','-l','../tmp/testNB.log','--snow','-o','../tmp/','--statistics','--saveStats','../tmp/JinjaIsarNB.stats','--cutOff','500','--depFile','mash_atp_dependencies']


    
    #startTime = time()
    #sys.exit(main(args))
    #print 'New ' + str(round(time()-startTime,2))
    sys.exit(main())
