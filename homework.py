import Queue

class Tree(object):
    def __init__(self):
        self.left = None
        self.right = None
        self.data = None
        self.parent = None

class kbObject(object):
    def __init__(self):
        self.literals = []
        self.parameters = []
        self.count = 0
        self.negation = []
        self.unifyIndex = []

def convertToKbObject(node,kbObj):
    if(node.left == None and node.right == None):
        kbObj.count += 1
        if str(node.data).startswith('~'):
            kbObj.negation.append(True)
            literal = ''.join(node.data[1:])
            index = literal.find('(')
            kbObj.literals.append(literal[:index])
            kbObj.parameters.append(str(literal[index+1:-1]).split(','))
        else:
            kbObj.negation.append(False)
            literal = str(node.data)
            index = literal.find('(')
            kbObj.literals.append(literal[:index])
            kbObj.parameters.append(literal[index+1:-1].split(','))
    if (node.left != None and node.right != None):
        convertToKbObject(node.left,kbObj)
        convertToKbObject(node.right,kbObj)
    return kbObj

def nodeNegation(node):
    if node.left != None and node.right != None:
        if node.data == '&':
            node.data = '|'
            node.left = nodeNegation(node.left)
            node.right = nodeNegation(node.right)
        elif node.data == '|':
            node.data = '&'
            node.left = nodeNegation(node.left)
            node.right = nodeNegation(node.right)
        else:
            #implies case
            node.data = '&'
            node.right = nodeNegation(node.right)
            #node.left is the same 
    if node.left == None and node.right == None:
        node.data = '~' + node.data
    return node
         

#global variable
kBaseReadyForCNF = []

#Extracts the input string and creates a tree
def ExtractKBase(kBaseInputStr):
    #Returns the root of the knowledge base tree
    kBaseStack = []
    index = 0
    if(kBaseInputStr[0] != '(' or (('&' not in kBaseInputStr) and ('|' not in kBaseInputStr) and ('=' not in kBaseInputStr))):
        #there is no binary operator
        root = Tree()
        root.data = kBaseInputStr
        return root
    operator = None
    for ch in kBaseInputStr:
        kBaseStack.append(ch)
        if(ch == ')' ):
            #pop and form a tree
            count = 0
            operatorFlag = False
            operand1 = ""
            operand2 = ""
            while (True):
                poppedChar = kBaseStack.pop()
                
                #if it is an operator
                if(poppedChar in ['&','|','=']):
                    operatorFlag = True
                    operator = poppedChar
                    continue

                if(operatorFlag == True):
                    if(type(poppedChar) == Tree):
                        operand2 = poppedChar
                        operatorFlag = False

                        #extra pop to remove the bracket in the stack
                        kBaseStack.pop()
                        
                        root = Tree()
                        root.data = operator
                        
                        leftNode= Tree()
                        rightNode = Tree()

                        leftNode = operand2
                        leftNode.parent = root
                        root.left = leftNode

                        if(type(operand1) == Tree):
                            rightNode = operand1
                            rightNode.parent = root
                            root.right = rightNode
                        else:
                            #removing extra bracket at the end
                            rightNode.data = operand1[:-1]
                            rightNode.parent = root
                            root.right = rightNode
                        kBaseStack.append(root)
                        break
                    else:
                        operand2 = poppedChar + operand2

                if(operatorFlag == False):
                    if(type(poppedChar) == Tree):
                        operand1 = poppedChar
                    else:
                        #(~(a&b)) case
                        if(poppedChar != Tree and type(operand1) == Tree and poppedChar == '~'):
                            operand1 = nodeNegation(operand1)
                        elif (poppedChar != Tree and type(operand1) == Tree and poppedChar == '('):
                            x = 1
                        else:
                            operand1 = poppedChar + operand1
                
                #modifying count value accordingly
                if(poppedChar == ')'):
                    count -= 1
                if(poppedChar == '('):
                    count += 1
                
                #if count value reached 0 and no operator found while popping
                if(count == 0 and operatorFlag == False):
                    kBaseStack.append(operand1)
                    break

                #if count value reached 0 and an operator is also found
                if(count == 0 and operatorFlag == True):
                    root = Tree()
                    rightNode = Tree()
                    leftNode = Tree()
                    root.data = operator
                    if(type(operand1) == Tree):
                        rightNode = operand1
                        if(type(operand2) == Tree):    
                            leftNode = operand2
                        else:
                            #removing extra bracket at the beggining
                            leftNode.data = operand2[1:]
                    else:
                        #removing extra bracket at the end
                        rightNode.data = operand1[:-1]
                        if(type(operand2) == Tree):
                            leftNode = operand2
                        else:
                            #removing extra bracket at the beggining
                            leftNode.data = operand2[1:]

                    #root and child properties
                    leftNode.parent = root
                    rightNode.parent = root
                    root.left = leftNode
                    root.right = rightNode
                    kBaseStack.append(root)
                    break

    return kBaseStack.pop()


def printTree(root):
    if(root.left == None and root.right == None):
        print root.data
    else:
        printTree(root.left)
        print root.data
        printTree(root.right)


def negateTreeBranch(node):

    # if it is "implies" again
    if node.data == '=':
        EvaluateImplicationAndSimplify(node)

    #Demorgan's law of negation
    if node.data == '&':
        node.data = '|'
        node.left = negateTreeBranch(node.left)
        node.right = negateTreeBranch(node.right)
    elif node.data == '|':
        node.data = '&'
        node.left = negateTreeBranch(node.left)
        node.right = negateTreeBranch(node.right)

    #For an expression string
    else:
        node.data = '(' + '~' + node.data + ')'

    return node

def checkAndNode(node):
    if node!= None :
        if node.data == '&':
            return True
    if node.left != None: 
        if(checkAndNode(node.left)):
            return True
    if node.right != None:
        if(checkAndNode(node.right)):
            return True
    #elif node.left != None:
    #    return checkAndNode(node.left)
    #elif node.right != None:
    #    return checkAndNode(node.right)
    return False
def EvaluateImplicationAndSimplify(node):
    if (node.data == '='):
        node.data = '|'
        node.left = negateTreeBranch(node.left)
    elif node.data == '&' or node.data == '|':
        node.left = EvaluateImplicationAndSimplify(node.left)
        node.right = EvaluateImplicationAndSimplify(node.right)
    else:
        #if th control is here => it is a leaf node and is an expression
        return node

    return node

def convertToCNF(node,kBaseInCNF):
    global kBaseReadyForCNF
    if (node.left == None and node.right == None):
        return node
        
    if node.data in ['&','|']:
        if node.data == '&':
            #If '&' => split and run cnf on the two branches separately
            node.left.parent = None
            node.right.parent = None
            kBaseReadyForCNF.append(node.left)
            kBaseReadyForCNF.append(node.right)
            #(convertToCNF(node.left,kBaseInCNF))
            #(convertToCNF(node.right,kBaseInCNF))
             
        if (node.data == '|'):
            if (node.left.data not in ['&','|'] and node.right.data not in ['&','|']):
                return node
            if (node.left.data in ['&','|'] and node.right.data not in ['&','|']):
                    if node.left.data == '&':
                        #construct a new node for the expression
                        #nag - yo yo
                        newNode = Tree()
                        newNode.parent = node.parent
                        newNode.data = '&'

                        #node1
                        currentRootNode1 = Tree()
                        currentRootNode1.data = '|'
                        currentRootNode1.left = node.left.left
                        currentRootNode1.right = node.right
                        #setting the pointers 
                        #node.left.left.parent = currentRootNode1
                        #node.right.parent = currentRootNode1
                        #currentRootNode1.parent = None
                        ##calling cnf on the new node
                        #return convertToCNF(currentRootNode1,kBaseInCNF)


                        #node2
                        currentRootNode2 = Tree()
                        currentRootNode2.data = '|'
                        currentRootNode2.left = node.left.right
                        currentRootNode2.right = node.right
                        #setting the pointers 
                        #node.left.right.parent = currentRootNode2
                        #node.right.parent = currentRootNode2
                        #currentNode2.parent = None
                        #calling cnf on the new node
                        #return convertToCNF(currentRootNode2,kBaseInCNF)

                        newNode.left = currentRootNode1
                        newNode.right = currentRootNode2

                        node = newNode
                        if (newNode.parent == None):
                            return convertToCNF(newNode,kBaseInCNF) 
                        else:
                            return newNode
                        

                    if node.left.data == '|':
                        #here we just call cnf on the branches of the tree
                        andNodePresent = checkAndNode(node.left)
                        if (andNodePresent):
                            newNode = Tree()
                            newNode.data = node.data
                            newNode.parent = node.parent
                            newNode.left = convertToCNF(node.left,kBaseInCNF)
                            newNode.right = convertToCNF(node.right,kBaseInCNF)
                            node = newNode
                            return convertToCNF(newNode,kBaseInCNF)
                        else:
                            return node

            elif (node.right.data in ['&','|'] and node.left.data not in ['&','|']):
                if node.right.data == '&':
                    #construct a new node for the expression

                    newNode = Tree()
                    newNode.parent = node.parent
                    newNode.data = '&'

                    #node1
                    currentRootNode1 = Tree()
                    currentRootNode1.data = '|'
                    currentRootNode1.left = node.right.left
                    currentRootNode1.right = node.left

                    #setting the pointers 
                    #node.right.left.parent = currentRootNode1
                    #node.left.parent = currentRootNode1

                    #currentNode1.parent = None
                    #kBaseInCNF.append((currentRootNode1,kBaseInCNF))

                    #node2
                    currentRootNode2 = Tree()
                    currentRootNode2.data = '|'
                    currentRootNode2.left = node.right.right
                    currentRootNode2.right = node.left

                    #setting the pointers 
                    #node.right.right.parent = currentRootNode2
                    #node.left.parent = currentRootNode2
                    #currentNode2.parent = None
                    #kBaseInCNF.append((currentRootNode2,kBaseInCNF))

                    newNode.left = currentRootNode1
                    newNode.right = currentRootNode2

                    node = newNode
                    
                    #try
                    return newNode
                    #return convertToCNF(newNode,kBaseInCNF)

                if (node.right.data == '|'):
                    andNodePresent = checkAndNode(node.right)
                    if (andNodePresent):
                        newNode = Tree()
                        newNode.parent = node.parent
                        newNode.left = convertToCNF(node.left,kBaseInCNF)
                        newNode.right = convertToCNF(node.right,kBaseInCNF)
                        node = newNode
                        return convertToCNF(newNode,kBaseInCNF)
                    else:
                        return node


            if node.left.data in ['&','|'] and node.right.data in ['&','|']:
                #converting to cnf
                if((node.left.data == '&' and node.right.data == '&') or (node.left.data == '&' and node.right.data == '|')):
                    #construct a new node for the expression

                    newNode = Tree()
                    newNode.parent = node.parent
                    newNode.data = '&'

                    #node1
                    currentRootNode1 = Tree()
                    currentRootNode1.data = '|'
                    currentRootNode1.left = node.left.left
                    currentRootNode1.right = node.right
                    #setting the pointers 
                    #node.left.left.parent = currentRootNode1
                    #node.right.parent = currentRootNode1
                    #currentRootNode1.parent = None
                    #calling cnf on the new node
                    #return (newNode,kBaseInCNF)

                    #node2
                    currentRootNode2 = Tree()
                    currentRootNode2.data = '|'
                    currentRootNode2.left = node.left.right
                    currentRootNode2.right = node.right

                    #setting the pointers 
                    #node.left.right.parent = currentRootNode2
                    #node.right.parent = currentRootNode2
                    #currentNode2.parent = None
                    #calling cnf on the new node

                    newNode.left = currentRootNode1
                    newNode.right = currentRootNode2
                    node = newNode

                    #try
                    return newNode
                    #return convertToCNF(newNode,kBaseInCNF)
                    
                if(node.right.data == '&' and node.left.data == '|'):
                    #construct a new node for the expression

                    newNode = Tree()
                    newNode.parent = node.parent
                    newNode.data = '&'

                    #node1
                    currentRootNode1 = Tree()
                    currentRootNode1.data = '|'
                    currentRootNode1.left = node.right.left
                    currenRootNode1.right = node.left

                    #setting the pointers 
                    #node.right.left.parent = currentRootNode1
                    #node.left.parent = currentRootNode1

                    #currentNode1.parent = None
                    #return convertToCNF(currentRootNode1,kBaseInCNF)

                    #node2
                    currentRootNode2 = Tree()
                    currentRootNode2.data = '|'
                    currentRootNode2.left = node.right.right
                    currentRootNode2.right = node.left

                    #setting the pointers 
                    #node.right.right.parent = currentRootNode2
                    #node.left.parent = currentRootNode2
                    #currentNode2.parent = None

                    newNode.left = currentRootNode1
                    newNode.right = currentRootNode2
                    node = newNode
                    
                    #return convertToCNF(newNode,kBaseInCNF)
                    #try
                    return newNode

                if (node.right.data == '|' and node.left.data == '|'):
                    andNodePresentLeft = checkAndNode(node.left)
                    andNodePresentRight = checkAndNode(node.right)
                    if (andNodePresentLeft and andNodePresentRight):
                        newNode = Tree()
                        newNode.parent = node.parent
                        newNode.left = convertToCNF(node.left,kBaseInCNF)
                        newNode.right = convertToCNF(node.right,kBaseInCNF)
                        node = newNode
                        return convertToCNF(newNode,kBaseInCNF)
                    elif (andNodePresentLeft and not andNodePresentRight):
                        newNode = Tree()
                        newNode.left = convertToCNF(node.left,kBaseInCNF)
                        newNode.right = node.right
                        node = newNode
                        return convertToCNF(newNode,kBaseInCNF)
                    elif (not andNodePresentLeft and andNodePresentRight):
                        newNode = Tree()
                        newNode.left = convertToCNF(node.left,kBaseInCNF)
                        newNode.right = node.right
                        node = newNode
                        return convertToCNF(newNode,kBaseInCNF)
                    else:
                        return node
    #return node


def evaluateNegationAndBraces(node):
    if node.left == None and node.right == None:
        negateCount = 0
        nodeStr = list(node.data)
        updatedNodeStr = ""
        for i in range(len(nodeStr)):
            if(nodeStr[i] == '$'):
                continue
            if(nodeStr[i] == '~'):
                negateCount +=1
                continue
            elif(nodeStr[i]  == '(' ):
                if(nodeStr[i+1] == '~' or nodeStr[i+1] == '('):
                    nodeStr[-1] = '$'
                else:
                    updatedNodeStr = updatedNodeStr + nodeStr[i]
                continue
            else:
                updatedNodeStr = updatedNodeStr + nodeStr[i] 
        if(negateCount %2 == 0):
            node.data = updatedNodeStr
        else:
            node.data = '~' + updatedNodeStr
    if(node.left != None and node.right != None):
        evaluateNegationAndBraces(node.left)
        evaluateNegationAndBraces(node.right)
    return node

def simplifyAndUnify(kbObj1,kbObj2):
    resultObj = kbObject()
    unifyFlag = None
    resultLiteralparams = {}
    for i in range(kbObj1.count):
        for j in range(kbObj2.count):
            if (unifyFlag != None and (unifyFlag)):
                break
                #then dont include kbobj1 and kbobj2 but include remaining all literals
                #resultObj.count +=2

                #resultObj.literals.append(kbObj1.literals[j])
                #resultObj.parameters.append(list(kbObj1.parameters))
                #resultObj.negation = kbObj1.negation

                #resultObj.literals.append(kbObj2.literals[j]) 
                #resultObj.literals.append(list(kbObj2.parameters))
                #resultObj.negation = kbObj2.negation

                #continue

            if kbObj1.literals[i] == kbObj2.literals[j] :
                if (kbObj1.negation[i] == (not kbObj2.negation[j])):
                    count1 = len(kbObj1.parameters[i])
                    count2 = len(kbObj2.parameters[j])
                    if(count1 == count2):
                        unifyFlag = None
                        for  k in range(len(kbObj1.parameters[i])):
                            #if parameters count is the same. there are 4 cases of parameters mactching
                            #case 1: x,y
                            if ((kbObj1.parameters[i][k] != kbObj2.parameters[j][k]) and (str(kbObj1.parameters[i][k])[0].islower()) and (str(kbObj2.parameters[j][k])[0].islower())):
                                unifyFlag = False
                                break
                            #case 2: A,B
                            elif ((kbObj1.parameters[i][k] != kbObj2.parameters[j][k]) and (str(kbObj1.parameters[i][k])[0].isupper()) and (str(kbObj2.parameters[j][k])[0].isupper())):
                                unifyFlag = False
                                break
                            else:
                                unifyFlag = True
                                kbObj1.unifyIndex = [i,j]
                                kbObj2.unifyIndex = [j,i]
                                break

                        if (unifyFlag):
                            for  k in range(len(kbObj1.parameters[i])):
                                if (kbObj1.parameters[i][k] == kbObj2.parameters[j][k]):
                                    #resultLiteralparams.append(kbObj1.parameters[k])
                                    continue
                                if (str(kbObj1.parameters[i][k])[0].isupper()):
                                    resultLiteralparams[kbObj2.parameters[j][k]] = kbObj1.parameters[i][k]
                                    continue
                                if (str(kbObj2.parameters[j][k])[0].isupper()):
                                    resultLiteralparams[kbObj1.parameters[i][k]] = kbObj2.parameters[j][k]
                                    continue

            #Resolution and Unification logic : return true/false
            #if (unifyFlag != None and (not unifyFlag)):
            #    resultObj.count +=2

            #    resultObj.literals.append(kbObj1.literals[j])
            #    resultObj.parameters.append(list(kbObj1.parameters))
            #    resultObj.negation = kbObj1.negation

            #    resultObj.literals.append(kbObj2.literals[j]) 
            #    resultObj.literals.append(list(kbObj2.parameters))
            #    resultObj.negation = kbObj2.negation

            #    #unification
            #    continue
        #break statement
        if (unifyFlag != None and (unifyFlag)):
                break

    #if unifyFlag is set to true: continue appending the literals
    if(unifyFlag != None and (unifyFlag)):
        for i in range(kbObj1.count):
            if(kbObj1.unifyIndex[0] == i):
                continue
            resultObj.count += 1
            resultObj.literals.append(kbObj1.literals[i])
            resultObj.parameters.append((kbObj1.parameters[i]))
            resultObj.negation.append(((kbObj1.negation[i])))

        for i in range(kbObj2.count):
            if(kbObj2.unifyIndex[0] == i):
                continue
            resultObj.count += 1
            resultObj.literals.append(kbObj2.literals[i])
            resultObj.parameters.append((kbObj2.parameters[i]))
            resultObj.negation.append(((kbObj2.negation[i])))
        for paramList in resultObj.parameters:
            for i in range(len(paramList)):
                if (paramList[i] in resultLiteralparams):
                    paramList[i] = resultLiteralparams[paramList[i]]
    if (unifyFlag):
        return resultObj
    else:
        resultObj.count = -1
        return resultObj
                    

def Resolve(kbObjects,kbObjToProve,runCount):
    runCount += 1
    #kbObjToProve.negation = not kbObjToProve.negation
    kbObjects.append(kbObjToProve)
    for obj in kbObjects:
        for i in range(kbObjToProve.count):
            if (kbObjToProve.literals[i] in obj.literals):
                index = obj.literals.index(kbObjToProve.literals[i])
                bool1 = obj.negation[index]
                bool2 = not (kbObjToProve.negation[0])
                if(bool1  == bool2):
                    #unification
                    resultObj = simplifyAndUnify(obj,kbObjToProve)
                    if (resultObj.count == -1 or (resultObj.count >= (obj.count + kbObjToProve.count))):
                        continue
                    else:
                        if(resultObj.count == 0):
                            return True
                        else:
                            kbObjects.append(resultObj)
                            if (runCount < 1000):
                                return Resolve(kbObjects,resultObj,runCount)
                            else:
                                return False
    return False               

                    

def main():

    #test
    a = Tree()
    a.data = '&'
    a.left = Tree()
    a.right = Tree()
    a.left.data = "a"
    a.right.data = "b"

    a = nodeNegation(a)
    #test

    #read input file content
    fileReader = open("input.txt")
    fileContent = fileReader.read().split("\n")
    
    #statements to prove 
    toProveCount = int(fileContent[0]) + 1
    toProve = fileContent[1:toProveCount]
    
    #KnowledgeBase
    kBaseCount = fileContent[int(fileContent[0]) + 1]
    kBaseStart = int(fileContent[0]) + 2
    kBaseInput = fileContent[kBaseStart:]

    #Extracting knowledge base
    #kBaseRootList has the list of all the root nodes of the knowledge base expressions
    kBaseRootList = []
    for kBaseInputStr in kBaseInput:
        if kBaseInputStr == "":
            continue
        #Removing > sign from => sign and whitespaces if any in the logical expressions
        formattedkBaseInput = str(kBaseInputStr).replace(' ','').replace('>','')
        kBaseRootList.append(ExtractKBase(formattedkBaseInput))

    #Making the kBaseStrings ready for CNF
    node = Tree()
    global kBaseReadyForCNF
    for node in kBaseRootList:
        kBaseReadyForCNF.append(EvaluateImplicationAndSimplify(node))
    
    checkAndNode(kBaseReadyForCNF[0])

    #CNF Evaluation
    kBaseInCNF = []
    for node in kBaseReadyForCNF:
        cnfNode = convertToCNF(node,kBaseReadyForCNF)
        while(cnfNode != None and checkAndNode(cnfNode)):
            cnfNode = convertToCNF(cnfNode,kBaseReadyForCNF)
        if(cnfNode != None):
            kBaseInCNF.append(cnfNode)
        
    #Evaluate all negations and make it ready for resolution
    NodesForResolution = []
    for node in kBaseInCNF:
        NodesForResolution.append(evaluateNegationAndBraces(node))
    
    #Resolution
    kbObjects = []
    for node in NodesForResolution:
        kbObj = kbObject()
        kbObj = convertToKbObject(node,kbObj)
        kbObjects.append(kbObj)
    
    #converting the statements to prove in to objects and Resoltion Logic
    kbObjToProveList = []
    result = []
    for Statement in toProve:
        kbNodetoProve = ExtractKBase(Statement)
        kbNodetoProve = evaluateNegationAndBraces(kbNodetoProve)
        kbObjToProve = kbObject()
        kbObjToProve = convertToKbObject(kbNodetoProve,kbObjToProve)
        kbObjToProveList.append(kbObjToProve)

        #negate the toProve obj
        kbObjToProve.negation[0] = (not (kbObjToProve.negation[0]))

        #Resolution and Unification
        runCount = 0
        result.append(Resolve(list(kbObjects),kbObjToProve,runCount))

    fileName = "output.txt"
    fileWriter = open(fileName,'w')
    for i in range(len(result)):
        if result[i] == True:
            fileWriter.write("TRUE")
        else:
            fileWriter.write("FALSE")
        fileWriter.write('\n')

main()
