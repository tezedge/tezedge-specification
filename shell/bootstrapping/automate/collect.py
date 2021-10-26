# Get the list of all action names from [actionsFile]

def collectActionNames(actionsFile):

  # get action file contents
  fr = open(actionsFile, 'r')
  actionNames = fr.read()
  fr.close()

  # return the list of all action names
  actionNames = actionNames.split('pub enum Action {')
  actionNames = actionNames[1]
  actionNames = actionNames.split('}')
  actionNames = actionNames[0]
  actionNames = actionNames.splitlines()

  # remove empty lines
  while '' in actionNames:
    actionNames.remove('')

  actionNames = map(str.strip, actionNames)
  actionNames = map(lambda s: s.split('(')[0], actionNames)

  # remove comments
  for line in actionNames:
    if line.startswith('//'):
      actionNames.remove(line)
  
  return actionNames
