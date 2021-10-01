# Generate the java collection of all action names

import os

def generateJavaClassAndCompile(actionNames, nodeActionsFile, nodeActionsJar):

  javaHeader = '''\
package nodeActions;
import java.util.*;

public class NodeActions {

'''

  def mkJavaString(name):
    return '  public static final String {name} = new String("{name}");\n'.format(name=name)

  javaActionDecls = ''

  for name in actionNames:
    javaActionDecls += mkJavaString(name)

  allActionsMethod = '''\

  public static Set<String> allActions() {
    Set<String> acts = new HashSet<String>();
'''

  def addToSet(obj):
    return '    acts.add({obj});\n'.format(obj=obj)

  for name in actionNames:
    allActionsMethod += addToSet(name)

  allActionsMethod += '''\
    return acts;
  }
}
'''

  # write NodeActions java class
  fw = open(nodeActionsFile, 'w')
  fw.write(javaHeader + javaActionDecls + allActionsMethod)
  fw.close()

  # compile NodeActions
  os.system('javac {file}'.format(file=nodeActionsFile))
  os.system('jar cvf {jar} *'.format(jar=nodeActionsJar))
