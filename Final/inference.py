
__author__ = 'avik'

import sys

OPERATORS = ['^', '=>', '~', 'v']
VARCOUNT = 0
GOALS = set()


class KnowledgeBase:
    def __init__(self, initial_clauses = []):
        self.clauses = {}
        for clause in initial_clauses:
            self.tell(clause)

    def tell(self, clause):
        self.setPredicateIndex(clause, clause)

    def ask(self, query):
        return FOL_BC_ask(self, query)

    def setPredicateIndex(self, mainClause, innerClause):
        if isPredicate(innerClause):
            if innerClause.op in self.clauses:
                if mainClause not in self.clauses[innerClause.op]:
                    self.clauses[innerClause.op].append(mainClause)
            else:
                self.clauses[innerClause.op] = [mainClause]

        elif innerClause.op == '~':
            self.setPredicateIndex(mainClause, innerClause.args[0])

        else:
            self.setPredicateIndex(mainClause, innerClause.args[0])
            self.setPredicateIndex(mainClause, innerClause.args[1])

    def fetchRulesForGoal(self, goal):
        try:
            predicate = self.getPredicate(goal)
            if predicate in self.clauses:
                return self.clauses[predicate]

        except IndexError:
            allClauses = []
            for key in self.clauses.keys():
                allClauses += self.clauses[key]
            return list(set(allClauses))

    def getPredicate(self, goal):
        if isPredicate(goal):
            return goal.op
        else:
            return self.getPredicate(goal.args[0])

    def display(self):
        for key in self.clauses.keys():
            print key,':',self.clauses[key]


class Clause:
    def __init__(self, op, args = []):
        self.op = op
        self.args = map(convertToClause, args)

    def __hash__(self):
        return hash(self.op) ^ hash(tuple(self.args))

    def __repr__(self):
        if len(self.args) == 0:
            return self.op

        elif self.op not in OPERATORS:
            args = str(self.args[0])
            for arg in self.args[1:]:
                args = args + ', ' + str(arg)
            return self.op + '(' + args + ')'

        elif self.op == '~':
            if self.args[0].op not in OPERATORS:
                return '~' + str(self.args[0])
            else:
                return '~' + '(' + str(self.args[0]) + ')'

        else:
            stringRepr = ''
            if self.args[0].op in OPERATORS:
                stringRepr = '(' + str(self.args[0]) + ')'
            else:
                stringRepr = str(self.args[0])
            stringRepr += ' ' + self.op + ' '

            if self.args[1].op in OPERATORS:
                stringRepr += '(' + str(self.args[1]) + ')'
            else:
                stringRepr += str(self.args[1])
            return stringRepr

    def __eq__(self, other):
        return isinstance(other, Clause) and self.op == other.op and self.args == other.args

    def display(self):
        print("op:",self.op)
        print("args:",self.args)


def convertToClause(item):
    if isinstance(item, Clause):
        return item

    if '=>' in item:
        pos = item.index('=>')
        lhs = item[:pos]
        rhs = item[pos + 1:]
        clause = Clause('=>', [lhs, rhs])
        return clause

    elif 'v' in item:
        pos = item.index('v')
        first = item[:pos]
        second = item[pos + 1:]
        clause = Clause('v', [first, second])
        return clause

    elif '^' in item:
        pos = item.index('^')
        first = item[:pos]
        second = item[pos + 1:]
        clause = Clause('^', [first, second])
        return clause

    elif '~' in item:
        pos = item.index('~')
        clause = Clause('~', [item[pos + 1:]])
        return clause

    elif isinstance(item, str):
        return Clause(item)

    if len(item) == 1:
        return convertToClause(item[0])

    simpleClause = Clause(item[0], item[1:][0])
    return simpleClause


def negate(clause):
    if clause.op not in OPERATORS:
        if clause.args == []:
            return Clause('~', [clause.op])
        else:
            if clause.op[0] == '~':
                return Clause(clause.op[1:],clause.args)
            else:
                return Clause('~', [Clause(clause.op, clause.args)])

    if clause.op == '^':
        return Clause('v', map(negate, clause.args))

    elif clause.op == '^':
        return Clause('v', map(negate, clause.args))

    elif clause.op == '=>':
        return Clause('^', [clause.args[0], negate(clause.args[1])])

    else:
        return clause.args[0]


def breakNesting(clause):
    if clause.op == '=>':
        negClause = negate(clause.args[0])
        expanded = breakNesting(negClause)
        return Clause('v', [expanded, clause.args[1]])

    elif clause.op == '~':
        if clause.args[0].op in OPERATORS:
            negClause = negate(clause.args[0])
            expanded = breakNesting(negClause)
            return expanded
        else:
            return clause

    elif clause.op in ['^', 'v']:
        arg1 = breakNesting(clause.args[0])
        arg2 = breakNesting(clause.args[1])
        return Clause(clause.op, [arg1, arg2])

    else:
        return clause


def isPredicate(clause):
    if clause.op[0] != '~':
        return clause.op not in OPERATORS and clause.op[0].isupper()
    else:
        return clause.op not in OPERATORS and clause.op[1].isupper()


def isVariable(item):
    return isinstance(item, Clause) and item.op.islower() and item.args == []


def unify(x, y, subst = {}):
    if subst is None:
        return None

    elif x == y:
        return subst

    elif isVariable(x):
        return unifyVars(x, y, subst)

    elif isVariable(y):
        return unifyVars(y, x, subst)

    elif isinstance(x, Clause) and isinstance(y, Clause):
        return unify(x.args, y.args, unify(x.op, y.op, subst))

    elif isinstance(x, list) and isinstance(y, list) and len(x) == len(y):
        return unify(x[1:], y[1:], unify(x[0], y[0], subst))

    else:
        return None


def unifyVars(var, x, subst):
    if var in subst:
        return unify(subst[var], x, subst)

    newSubst = subst.copy()
    newSubst[var] = x
    return newSubst



def standardizeVars(clause, stdVars = None):
    global VARCOUNT

    if stdVars is None:
        stdVars = {}

    if not isinstance(clause, Clause):
        return clause

    if isVariable(clause):
        if clause in stdVars:
            return stdVars[clause]
        else:
            newVar = Clause('v_' + str(VARCOUNT))
            VARCOUNT += 1
            stdVars[clause] = newVar
            return newVar
    else:
        return Clause(clause.op, (standardizeVars(arg, stdVars) for arg in clause.args))


def substitute(theta, clause):
    assert isinstance(clause, Clause)

    if isVariable(clause):
        if clause in theta:
            return theta[clause]
        else:
            return clause
    else:
        return Clause(clause.op, (substitute(theta, arg) for arg in clause.args))


def changeToImplication(clause):
    if clause.op == '=>':
        return breakNesting(clause.args[0]), clause.args[1]
    else:
        return [], clause


def FOL_BC_and(KB, goals, theta):
    if theta is None:
        pass

    elif isinstance(goals, list) and len(goals) == 0:
        yield theta

    else:
        if goals.op == '^':
            first = goals.args[0]
            rest = goals.args[1]

            if first.op == '^':
                while not isPredicate(first):
                    rest = Clause('^', [first.args[1], rest])
                    first = first.args[0]
        else:
            first = goals
            rest = []

        for theta1 in FOL_BC_or(KB, substitute(theta, first), theta):
            for theta2 in FOL_BC_and(KB, rest, theta1):
                yield theta2


def FOL_BC_or(KB, goal, theta):
    if goal in GOALS:
        return

    GOALS.add(goal)

    for rule in KB.fetchRulesForGoal(goal):
        stdRule = standardizeVars(rule)
        lhs, rhs = changeToImplication(stdRule)
        #print "lhs,rhs,goal:",lhs,rhs,goal,"\n"

        for theta1 in FOL_BC_and(KB, lhs, unify(rhs, goal, theta)):
            yield theta1


def FOL_BC_ask(KB, query):
    return FOL_BC_or(KB, query, {})


def parse(sentence):
    sentence = '(' + sentence + ')'
    sentence = sentence.replace('(', ' ( ')
    sentence = sentence.replace(')', ' ) ')
    sentence = sentence.replace(',', ' ')

    sentence = sentence.replace('v', ' v ')
    sentence = sentence.replace('^', ' ^ ')
    sentence = sentence.replace('~', ' ~ ')
    sentence = sentence.replace('=>', ' => ')

    tokens = sentence.split()
    return readTokenList(tokens)


def readTokenList(List):
    first = List.pop(0)

    if first == '(':
        new_expression = []
        while List[0] != ')':
            new_expression.append(readTokenList(List))
        List.pop(0)
        return new_expression
    else:
        return first


def printOutputFile(result):
    with open('output.txt','a+') as outputFile:
        outputFile.write(result + '\n')

def setOutputFile():
    outputFile = open('output.txt','w')
    outputFile.close()


def main():
    global VARCOUNT, GOALS
    queries = []
    rules = []

    with open(sys.argv[2]) as f:
        queryCount = int(f.readline().strip())

        while queryCount > 0:
            goal = f.next().strip()
            queryCount -= 1
            queries.append(goal)

        KBcount = int(f.next().strip())

        while KBcount > 0:
            clause = f.next().strip()
            rules.append(clause)
            KBcount -= 1

    KB = KnowledgeBase(map(convertToClause,map(parse,rules)))
    #KB.display()

    setOutputFile()

    for i in range(len(queries)):
        Q = convertToClause(parse(queries[i]))
        GOALS.clear()
        VARCOUNT = 0
        flag = False

        for ans in KB.ask(Q):
            flag = True
            break

        if flag:
            #print "TRUE"
            printOutputFile('TRUE')
        else:
            #print "FALSE"
            printOutputFile('FALSE')


if __name__ == '__main__':
    main()
