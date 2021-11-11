# Generates the corresponding ActionTranslator.tla file
# from the actions in the implementation

from action_map import *

def generateTLA(actionNames, actionTranslatorFile):

  tlaHeader = '''\
---- MODULE ActionTranslator ----

EXTENDS Bootstrap

'''

  def actionOperatorDef(name):
    return '{name}Action(data) =={actionDef}\n'.format(name=name, actionDef=action(name))

  tlaActionDecls = ''

  for name in actionNames:
    tlaActionDecls += actionOperatorDef(name)

  def translation(idx, name):
    if idx == 0:
      return 'act = "{name}" -> {name}Action(data)\n'.format(name=name)
    else:
      return '      [] act = "{name}" -> {name}Action(data)\n'.format(name=name)

  actionTranslator = '''\

ActionTranslator(input) ==
    LET act  == input[1]
        data == input[2]
    IN
    CASE '''

  for idx, name in enumerate(actionNames):
    actionTranslator += translation(idx, name)

  ending = '\n====\n'

  fw = open(actionTranslatorFile, 'w')
  fw.write(tlaHeader + tlaActionDecls + actionTranslator + ending)
  fw.close()
