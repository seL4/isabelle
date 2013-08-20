import datetime
from argparse import ArgumentParser,RawDescriptionHelpFormatter

def init_parser(argv):
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
    parser.add_argument('--numberOfPredictions',default=500,help="Default number of premises to write in the output. Default=500.",type=int)
    
    parser.add_argument('--init',default=False,action='store_true',help="Initialize Mash. Requires --inputDir to be defined. Default=False.")
    parser.add_argument('--inputDir',\
                        help='Directory containing all the input data. MaSh expects the following files: mash_features,mash_dependencies,mash_accessibility')
    parser.add_argument('--depFile', default='mash_dependencies',
                        help='Name of the file with the premise dependencies. The file must be in inputDir. Default = mash_dependencies')
    
    parser.add_argument('--algorithm',default='nb',action='store_true',help="Which learning algorithm is used. nb = Naive Bayes,predef=predefined. Default=nb.")
    # NB Parameters
    parser.add_argument('--NBDefaultPriorWeight',default=20.0,help="Initializes classifiers with value * p |- p. Default=20.0.",type=float)
    parser.add_argument('--NBDefVal',default=-15.0,help="Default value for unknown features. Default=-15.0.",type=float)
    parser.add_argument('--NBPosWeight',default=10.0,help="Weight value for positive features. Default=10.0.",type=float)
    # TODO: Rename to sineFeatures
    parser.add_argument('--sineFeatures',default=False,action='store_true',help="Uses a SInE like prior for premise lvl predictions. Default=False.")
    parser.add_argument('--sineWeight',default=0.5,help="How much the SInE prior is weighted. Default=0.5.",type=float)
    
    parser.add_argument('--statistics',default=False,action='store_true',help="Create and show statistics for the top CUTOFF predictions.\
                        WARNING: This will make the program a lot slower! Default=False.")
    parser.add_argument('--saveStats',default=None,help="If defined, stores the statistics in the filename provided.")
    parser.add_argument('--cutOff',default=500,help="Option for statistics. Only consider the first cutOff predictions. Default=500.",type=int)
    parser.add_argument('-l','--log', default='../tmp/%s.log' % datetime.datetime.now(), help='Log file name. Default=../tmp/dateTime.log')
    parser.add_argument('-q','--quiet',default=False,action='store_true',help="If enabled, only print warnings. Default=False.")
    parser.add_argument('--modelFile', default='../tmp/model.pickle', help='Model file name. Default=../tmp/model.pickle')
    parser.add_argument('--dictsFile', default='../tmp/dict.pickle', help='Dict file name. Default=../tmp/dict.pickle')
    
    parser.add_argument('--port', default='9255', help='Port of the Mash server. Default=9255',type=int)
    parser.add_argument('--host', default='localhost', help='Host of the Mash server. Default=localhost')
    args = parser.parse_args(argv)    
    return args
