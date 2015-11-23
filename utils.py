OPERATORS = ['^','=>','~','v']


class KnowledgeBase:
    def __init__(self,initialClauses = []):
        self.clauses = {}
        for clause in initialClauses:
            self.tell(clause)

    def tell(self,clause):
        self.predicateIndex(clause,clause)

    #def ask(self,query):
    #    return fol_bc_ask(self,query)

    def predicateIndex(self,mainClause,insideClause):
        #print "mainClause,insideClause:",mainClause,',', insideClause
        #print insideClause.op
        if isPredicate(insideClause):
            if insideClause.op in self.clauses:
                if mainClause not in self.clauses[insideClause.op]:
                    self.clauses[insideClause.op].append(mainClause)
            else:
                self.clauses[insideClause.op] = [mainClause]
        elif insideClause.op == '~':
            self.predicateIndex(mainClause,insideClause.args[0])
        else:
            self.predicateIndex(mainClause, insideClause.args[0])
            self.predicateIndex(mainClause, insideClause.args[1])

        #print self.clauses,"\n"

    def retrievePredicate(self,goal):
        if isPredicate(goal):
            return goal.op
        else:
            self.retrievePredicate(goal.args[0])

    def fetchRulesforGoal(self,goal):
        try:
            predicate =  self.retrievePredicate(goal)
            if predicate in self.clauses:
                return self.clauses[predicate]
        except IndexError:
            allClauses = []
            for key in self.clauses.keys():
                allClauses += self.clauses[key]
            return list(set(allClauses))



class Clause:

    def __init__(self,op, args = [], parents = None):
        self.op = op
        self.parents = parents
        self.args = map(convertToClause,args)  ##here it is

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
            str_repn = ''
            #print "ARGS:",self.args[0].op
            if self.args[0].op in OPERATORS:
                str_repn = '(' + str(self.args[0]) + ')'
            else:
                str_repn = str(self.args[0])
            str_repn += ' ' + self.op + ' '

            if self.args[1].op in OPERATORS:
                str_repn += '(' + str(self.args[1]) + ')'
            else:
                str_repn += str(self.args[1])
            return str_repn

    def __eq__(self, other):
        return isinstance(other, Clause) and self.op == other.op and self.args == other.args

    def display(self):
        print "op:",self.op
        print "args:",self.args
        print "par:",self.parents


def convertToClause(item):

    if isinstance(item,Clause):
        return item

    if '=>' in item:
        #print "here"
        pos = item.index('=>')
        lhs = item[:pos]
        rhs = item[pos+1:]
        #print lhs,rhs
        clause = Clause('=>',[lhs,rhs])
        #print clause
        #clause.display()
        return  clause

    elif '^' in item:
        pos = item.index('^')
        lhs = item[:pos]
        rhs = item[pos+1:]
        clause = Clause('^',[lhs,rhs])
        #clause.display()
        return clause

    elif 'v' in item:
        pos = item.index('v')
        lhs = item[:pos]
        rhs = item[pos+1:]
        clause = Clause('v',[lhs,rhs])
        #clause.display()
        return clause

    elif '~' in item:
        pos = item.index('~')
        clause = Clause('~',[item[pos + 1:]])
        #clause.display()
        return clause

    elif isinstance(item,str):
        return Clause(item)

    if len(item) == 1:
        return convertToClause(item[0])

    simpleClause = Clause(item[0], item[1:][0])
    #simpleClause.display()
    return simpleClause

def negate(clause):

    print "NEG:"
    clause.display()

    if clause.op not in OPERATORS:
        # means a clause like 'P' or 'Has'...
        print "Not in operators"
        if clause.args == []:
            # simple clause like 'P'
            return Clause('~', [clause.op])
        else:
            # clause like ['Has', ['Avik', 'Chocolate']]
            # in that case 'Has' will be the op and rest the arguments
            # of the clause in the '~' "level"
            if clause.op[0] == '~':   # for cases like D(x,y) => ~H(y) where ~H(y) is being tackled
                return Clause(clause.op[1:],clause.args)
            else:
                return Clause('~', [Clause(clause.op, clause.args)])

    if clause.op == '^':
        print "here ^"
        # ~(P ^ Q) becomes ~P v ~Q
        return Clause('v', map(negate, clause.args))
    # or
    elif clause.op == 'v':
        print "here v"
        # ~(P v Q) becomes ~P ^ ~Q
        return Clause('^', map(negate, clause.args))
    # implies
    elif clause.op == '=>':
        print "here =>"
        # ~(P => Q) becomes P ^ ~Q
        return Clause('^', [clause.args[0], negate(clause.args[1])])
    # not
    else:
        print "NOT!!!\n"
        return clause.args[0]   # there will only be one argument


def break_nesting(clause):

    if clause.op == '=>':
        # expand P => Q as ~P v Q
        negated_precedent = negate(clause.args[0]) # this is ~P
        # break the nesting of ~P
        broken_negated_precedent = break_nesting(negated_precedent)
        return Clause('v', [broken_negated_precedent, clause.args[1]])

    elif clause.op == '~':
        # only continue breaking nesting if the operator of the not clause's
        # argument is a logical operator
        if clause.args[0].op in OPERATORS:
            # expand
            negated_not_clause = negate(clause.args[0])
            broken_negated_not_clause = break_nesting(negated_not_clause)
            return broken_negated_not_clause
        else:
            # just keep the whole thing as it is
            # we want the ~P etc. to stay as they are so we can count
            # the number of negative and positive literals
            return clause
    elif clause.op in ['^', 'v']:
        # break the nesting of their arguments and return them as themselves
        broken_first_arg = break_nesting(clause.args[0])
        broken_second_arg = break_nesting(clause.args[1])
        return Clause(clause.op, [broken_first_arg, broken_second_arg])
    else:
        # simple propositions such as 'P' or 'Loves(Aashish, Chocolate)'
        # send back straight away, nothing to do
        return clause


def isPredicate(clause):   # CHANGED A BIT FROM ORIGINAL
    if clause.op[0] != '~':
        return clause.op not in OPERATORS and clause.op[0].isupper()
    else:
        return clause.op not in OPERATORS and clause.op[1].isupper()