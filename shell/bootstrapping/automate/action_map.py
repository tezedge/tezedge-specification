# Maps action names to TLA+ definitions

actionMap = {}

actionMap['PeersDnsLookupInit'] = ' UNCHANGED vars'

actionMap['PeersDnsLookupSuccess'] = ' UNCHANGED vars'

# TODO

def action(name):
  res = actionMap.get(name)
  if res != None:
    return res
  else:
    return ' UNCHANGED vars'
