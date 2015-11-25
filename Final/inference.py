
import sys

################### PrintProof begin ###########################################

#from FolBC import *

def complete_substitute(theta, clause):

    for i in range(0, len(theta.keys())):
        clause = substitute(theta, clause)
    return clause


def print_parent(theta, clause):

    if clause not in parent_clauses:
        print 'We know', complete_substitute(theta, clause), '(given)'
        return

    parents, law_used, clause_used = parent_clauses[clause]
    for parent in parents:
        print_parent(theta, parent)
    print 'which leads to', complete_substitute(theta, clause),

    if clause_used is not None:
        print '(' + law_used, 'on', str(clause_used) + ')'
    else:
        print '(' + law_used + ')'


####################### PrintProof ends ########################################

####################### KBUtils begin ##########################################

#import FolBC

OPERATORS = ['^', '=>', '~', 'v']

class KnowledgeBase:

    def __init__(self, initial_clauses = []):
        self.clauses = {}
        for clause in initial_clauses:
            self.tell(clause)

    def tell(self, clause):
        self.predicate_index(clause, clause)

    def ask(self, query):
        return fol_bc_ask(self, query)

    def predicate_index(self, main_clause, inside_clause):

        if is_predicate(inside_clause):
            if inside_clause.op in self.clauses:
                if main_clause not in self.clauses[inside_clause.op]:
                    self.clauses[inside_clause.op].append(main_clause)
            else:
                self.clauses[inside_clause.op] = [main_clause]

        elif inside_clause.op == '~':
            self.predicate_index(main_clause, inside_clause.args[0])

        else:
            self.predicate_index(main_clause, inside_clause.args[0])
            self.predicate_index(main_clause, inside_clause.args[1])

    def fetch_rules_for_goal(self, goal):
        try:
            predicate = self.retrieve_predicate(goal)
            if predicate in self.clauses:
                return self.clauses[predicate]

        except IndexError:
            all_clauses = []
            for key in self.clauses.keys():
                all_clauses += self.clauses[key]
            return list(set(all_clauses))

    def retrieve_predicate(self, goal):
        if is_predicate(goal):
            return goal.op
        else:
            return self.retrieve_predicate(goal.args[0])


class Clause:

    def __init__(self, op, args = [], parents = None):
        self.op = op
        self.parents = parents
        self.args = map(convert_to_clause, args)

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
        return isinstance(other, Clause) and self.op == other.op and \
        self.args == other.args

    def display(self):
        print("op:",self.op)
        print("args:",self.args)
        print("par:",self.parents)


def convert_to_clause(item):
    if isinstance(item, Clause):
        return item

    if '=>' in item:
        implication_posn = item.index('=>')
        lhs = item[:implication_posn]
        rhs = item[implication_posn + 1:]
        impl_clause = Clause('=>', [lhs, rhs])
        return impl_clause

    elif 'v' in item:
        or_posn = item.index('v')
        first_disjunct = item[:or_posn]
        second_disjunct = item[or_posn + 1:]
        or_clause = Clause('v', [first_disjunct, second_disjunct])
        return or_clause

    elif '^' in item:
        and_posn = item.index('^')
        first_conjunct = item[:and_posn]
        second_conjunct = item[and_posn + 1:]
        and_clause = Clause('^', [first_conjunct, second_conjunct])
        return and_clause

    elif '~' in item:
        not_posn = item.index('~')
        not_clause = Clause('~', [item[not_posn + 1:]])
        return not_clause

    elif isinstance(item, str):
        return Clause(item)
    if len(item) == 1:
        return convert_to_clause(item[0])

    simple_clause = Clause(item[0], item[1:][0])
    return simple_clause


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


def break_nesting(clause):

    if clause.op == '=>':
        negated_precedent = negate(clause.args[0])
        broken_negated_precedent = break_nesting(negated_precedent)
        return Clause('v', [broken_negated_precedent, clause.args[1]])

    elif clause.op == '~':
        if clause.args[0].op in OPERATORS:
            negated_not_clause = negate(clause.args[0])
            broken_negated_not_clause = break_nesting(negated_not_clause)
            return broken_negated_not_clause
        else:
            return clause

    elif clause.op in ['^', 'v']:
        broken_first_arg = break_nesting(clause.args[0])
        broken_second_arg = break_nesting(clause.args[1])
        return Clause(clause.op, [broken_first_arg, broken_second_arg])

    else:
        return clause


def is_predicate(clause):

    if clause.op[0] != '~':
        return clause.op not in OPERATORS and clause.op[0].isupper()
    else:
        return clause.op not in OPERATORS and clause.op[1].isupper()


################ KBUtil ends ###################################################

################ Unifier ends ##################################################

#from KBUtil import *

def is_variable(item):
    return isinstance(item, Clause) and item.op.islower() and item.args == []


def unify(x, y, subst = {}):

    if subst is None:
        return None

    elif x == y:
        return subst

    elif is_variable(x):
        return unify_vars(x, y, subst)

    elif is_variable(y):
        return unify_vars(y, x, subst)

    elif isinstance(x, Clause) and isinstance(y, Clause):
        return unify(x.args, y.args, unify(x.op, y.op, subst))

    elif isinstance(x, list) and isinstance(y, list) and len(x) == len(y):
        return unify(x[1:], y[1:], unify(x[0], y[0], subst))

    else:
        return None


def unify_vars(var, x, subst):
    if var in subst:
        return unify(subst[var], x, subst)

    subst_copy = subst.copy()
    subst_copy[var] = x
    return subst_copy

############ Unifier ends ######################################################

############ FolBC starts ######################################################

#from Unifier import *

VARIABLE_COUNTER = 0
parent_clauses = {}
GOALS = set()
TARGET = Clause('')

def standardize_vbls(clause, already_stdized = None):
    global VARIABLE_COUNTER

    if already_stdized is None:
        already_stdized = {}

    if not isinstance(clause, Clause):
        return clause

    if is_variable(clause):
        if clause in already_stdized:
            return already_stdized[clause]
        else:
            new_vbl = Clause('v_' + str(VARIABLE_COUNTER))
            VARIABLE_COUNTER += 1
            already_stdized[clause] = new_vbl
            return new_vbl
    else:
        return Clause(clause.op, (standardize_vbls(arg, already_stdized) for arg in clause.args))


def substitute(theta, clause):
    assert isinstance(clause, Clause)

    if is_variable(clause):
        if clause in theta:
            return theta[clause]
        else:
            return clause
    else:
        return Clause(clause.op, (substitute(theta, arg) for arg in clause.args))


def convert_to_implication(clause):
    if clause.op == '=>':
        return break_nesting(clause.args[0]), clause.args[1]
    else:
        return [], clause


def fol_bc_and(kb, goals, theta):
    if theta is None:
        pass

    elif isinstance(goals, list) and len(goals) == 0:
        yield theta

    else:
        if goals.op == '^':
            first_arg = goals.args[0]
            second_arg = goals.args[1]

            if first_arg.op == '^':
                while not is_predicate(first_arg):
                    second_arg = Clause('^', [first_arg.args[1], second_arg])
                    first_arg = first_arg.args[0]
        else:
            first_arg = goals
            second_arg = []

        for theta1 in fol_bc_or(kb, substitute(theta, first_arg), theta):
            if isinstance(second_arg, Clause):
                parent_clauses[substitute(theta, goals)] = ([substitute(theta, first_arg), substitute(theta1, second_arg)], 'Rule of conjunction', None)

            for theta2 in fol_bc_and(kb, second_arg, theta1):
                yield theta2


def fol_bc_or(kb, goal, theta):

    print "in fol_bc_or..."

    if goal in GOALS:
        print "GOTCHAAA!!!!!",goal,'\n'
        return

    print "goal:",goal
    GOALS.add(goal)
    print "GOALS:",GOALS
    possible_rules = kb.fetch_rules_for_goal(goal)
    print "possible rules:",possible_rules
    for rule in possible_rules:
        stdized_rule = standardize_vbls(rule)
        lhs, rhs = convert_to_implication(stdized_rule)

        #print lhs,rhs
        #raw_input()

        rhs_unify_try = unify(rhs, goal, theta)

        print "rhs_unify_try,rhs,goal:",rhs_unify_try,',',rhs,',',goal
        raw_input()

        if rhs_unify_try is not None:

            if lhs != []:

                if lhs.op == '^':
                    substituted_lhs_args = [substitute(rhs_unify_try, arg) for arg in lhs.args]
                    parent_clauses[substitute(rhs_unify_try, lhs)] = (substituted_lhs_args, 'Rule of conjunction', None)

                parent_clauses[goal] = ([substitute(rhs_unify_try, stdized_rule)], 'Modus Ponens', None)
                parent_clauses[substitute(rhs_unify_try, stdized_rule)] = ([substitute(rhs_unify_try, lhs)], 'Rule of universal instantiation', rule)
                for keys in parent_clauses.keys():
                    print keys,':',parent_clauses[keys]
                print '\n'
                #raw_input()

        for theta1 in fol_bc_and(kb, lhs, rhs_unify_try):
            yield theta1


def fol_bc_ask(kb, query):
    #print query
    #global TARGET,GOALS
    #GOALS = []
    #TARGET = query

    return fol_bc_or(kb, query, {})

########## FolBC ends ##########################################################

########## Parse starts ########################################################

def tokenize(string):

    string = '(' + string + ')'

    string = string.replace('(', ' ( ')
    string = string.replace(')', ' ) ')
    string = string.replace(',', ' ')

    string = string.replace('v', ' v ')
    string = string.replace('^', ' ^ ')
    string = string.replace('~', ' ~ ')
    string = string.replace('=>', ' => ')


    return string.split()

def parse(program):
    return read_from_tokens(tokenize(program))

def read_from_tokens(token_list):
    first_token = token_list.pop(0)

    if first_token == '(':
        new_expression = []

        while token_list[0] != ')':
            new_expression.append(read_from_tokens(token_list))
        token_list.pop(0)
        return new_expression
    else:
        return first_token

######### Parse Ends ###########################################################

######### Autoprover starts ####################################################
#from Parser import *
#from FolBC import *
#from PrintProof import *
#from HelpMessage import *
#import sys


def find_variables(clause):

    if is_variable(clause):
        return [clause]
    elif is_predicate(clause):
        return clause.args
    elif clause.op == '~':
        return find_variables(clause.args[0])
    else:
        first_arg_vbls = find_variables(clause.args[0])
        second_arg_vbls = find_variables(clause.args[1])
        return first_arg_vbls + second_arg_vbls



x_count = 0

def replace_with_variables(clause, theta = {}):

    global x_count

    assert isinstance(clause, Clause)
    if is_predicate(clause):
        theta_copy = theta.copy()
        new_args = []
        for arg in clause.args:
            if not is_variable(arg):
                new_arg_clause = Clause('x_' + str(x_count))
                theta_copy[new_arg_clause] = arg
                new_args.append(new_arg_clause)
                x_count += 1
        return Clause(clause.op, new_args), theta_copy


#def printOutputFile(result):
#    pass

#def setOutputFile():
#    pass


input_kb = KnowledgeBase(
    map(convert_to_clause,map(parse,
    ['A(x) => H(x)',
    'D(x,y) => ~H(y)',
    'B(x,y) ^ C(x,y) => A(x)',
    'B(John,Alice)',
    'B(John,Bob)',
    'D(x,y) ^ Q(y) => C(x,y)',
    'D(John,Alice)',
    'Q(Bob)',
    'D(John,Bob)',
    'F(x) => G(x)',
    'G(x) => H(x)',
    'H(x) => F(x)',
    'R(x) => H(x)',
    'R(Tom)'
    ])))

test_kb = KnowledgeBase(
    map(convert_to_clause,map(parse,
    ['A(x,y) ^ B(z,w) => C(x,w)',
    'C(y,x) => A(x,y)',
    'C(x,y) => B(y,x)',
    'A(EE,CS)'
    'B(MS,PHD)'
    ])))

#kb = crime_kb
kb = test_kb
#kb = input_kb
#for keys in kb.clauses.keys():
#    print keys,':',kb.clauses[keys]
#raw_input()


#query = convert_to_clause(parse('F(Bob)'))
#query = convert_to_clause(parse('G(Tom)'))
query = convert_to_clause(parse('C(PHD,PHD)'))

# to check if the statement has been proved
proof_flag = False

vbls_in_query = find_variables(query)
#print vbls_in_query
#print replace_with_variables(query),"\n"
print query


#####   #####   FOR THE INPUT FILE

queries = []
rules = []
with open(sys.argv[2],'r+') as f:
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
        #print parse(clause)
        #clause = convert_to_clause(parse(clause))
        #KB.tell(clause)
        #rules.append(clause)

print "queries:",queries
print "rules:",rules

KB = KnowledgeBase(map(convert_to_clause,map(parse,rules)))

for keys in KB.clauses.keys():
    print keys,':',KB.clauses[keys]

#Q = convert_to_clause(parse(queries[0]))

for i in range(len(queries)):
    Q = convert_to_clause(parse(queries[i]))
    GOALS.clear()
    parent_clauses = {}
    VARIABLE_COUNTER = 0
    x_count = 0
    flag = False
    for ans in KB.ask(Q):
        flag = True
        break

    if flag:
        print "TRUE"
    else:
        print "FALSE"

    raw_input()

#flag = False

#for answer in KB.ask(Q):
    #print '\n:\n'
    #print answer
#    print "True"
#    flag = True
#    break
    #raw_input()
    #print_parent(answer, Q)

#if not flag:
#    print "False"

####

"""   ### DELETE THIS LATER
for answer in kb.ask(query):
     #comment the below part out if you're using the program as a query-based system
    #if all(reqd_theta[key] == answer[key] for key in reqd_theta.keys()):
        # all keys match
    #    print '\nProof:\n'
    #    print_parent(answer, query)
    #    proof_flag = True
    #    break
    # uncomment this and run to see all proofs obtained by the query-based system
    print '\nProof:\n'
    print answer
    raw_input()
    print_parent(answer, query)

if not proof_flag:
    print '\nSorry, your statement could not be proved.\n'
else:
    print ''
"""

######### Autoprover ends ##########################################################
