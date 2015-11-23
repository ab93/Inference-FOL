__author__ = 'Avik'

import sys
from utils import *
from unifier import *

def tokenize(string):
    string = '(' + string + ')'
    string = string.replace('(',' ( ')
    string = string.replace(')',' ) ')
    string = string.replace('^', ' ^ ')
    string = string.replace(',', ' ')
    string = string.replace('=>',' => ')

    return string.strip().split()

def parse(string):
    return readTokenList(tokenize(string))

def readTokenList(tokens):
    firstToken = tokens.pop(0)

    if firstToken == '(':
        expression = []
        while tokens[0] != ')':
            expression.append(readTokenList(tokens))
        tokens.pop(0)
        return expression

    else:
        return firstToken


def findVariables(clause):
    if isVariable(clause):
        return [clause]
    elif isPredicate(clause):
        return clause.args
    elif clause.op == '~':
        return findVariables(clause.args[0])
    else:
        first_arg_vbls = findVariables(clause.args[0])
        second_arg_vbls = findVariables(clause.args[1])
        return first_arg_vbls + second_arg_vbls

x_count = 0

def replaceWithVariables(clause,theta = {}):
    global x_count

    assert isinstance(clause,Clause)
    if isPredicate(clause):
        theta_copy = theta.copy()
        new_args = []
        for arg in clause.args:
            if not isVariable(arg):
                new_arg_clause = Clause('x_' + str(x_count))
                theta_copy[new_arg_clause] = arg
                new_args.append(new_arg_clause)
                x_count += 1

        return Clause(clause.op, new_args), theta_copy


def getInput():
    with open(sys.argv[2],'r+') as f:
        queryCount = int(f.readline().strip())

        while queryCount > 0:
            goal = f.next().strip()
            queryCount -= 1
            #print goal

        KBcount = int(f.next().strip())
        print KBcount

        KB = KnowledgeBase()
        #clause = convertToClause(parse('~Criminal(West)'))
        #KB.tell(clause)

        while KBcount > 0:
            clause = f.next().strip()
            KBcount -= 1
            #print parse(clause)
            clause = convertToClause(parse(clause))
            KB.tell(clause)
            #print clause,findVariables(clause)
            #print "negation:",negate(clause)
            #raw_input()
    print KB.clauses
    goal = convertToClause(parse('F(Bob)'))
    print KB.fetchRulesforGoal(goal)
    print replaceWithVariables(goal)

def main():
    getInput()
    #print tokenize('D(x,y) ^ Q(y) => C(x,y)')
    #print parse('D(x,y) ^ Q(y) => C(x,y)')
    #print tokenize('B(John,Alice)')


if __name__ == '__main__':
    main()