from collect import *
from gen_java import *
from gen_tla import *

# relevant files
actionsFile = '../rust/action.rs'
nodeActionsDir = '../nodeActions/'
nodeActionsFile = nodeActionsDir + 'NodeActions.java'
nodeActionsJar = nodeActionsDir + 'NodeActions.jar'
actionTranslatorFile = '../ActionTranslator.tla'

# Get the list of all action names
actionNames = collectActionNames(actionsFile)

# Generate the java collection of all action names
generateJavaClassAndCompile(actionNames, nodeActionsFile, nodeActionsJar)

# Generate the corresponding ActionTranslator.tla file
generateTLA(actionNames, actionTranslatorFile)
