
from Parser import *
from FolBC import *
from PrintProof import *
from HelpMessage import *
import sys

#______________________________________________________________________________

def find_variables(clause):

    """
    Finds the variables in a clause.
    """

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

#______________________________________________________________________________


x_count = 0

def replace_with_variables(clause, theta = {}):

    """
    Replaces constants in clause with variables and return the substitutions
    that on substitution will yield the statement to prove.
    """

    global x_count

    assert isinstance(clause, Clause)
    if is_predicate(clause):
        # replace arguments of the clause with a variable
        theta_copy = theta.copy()
        new_args = []
        for arg in clause.args:
            if not is_variable(arg):
                new_arg_clause = Clause('x_' + str(x_count))
                theta_copy[new_arg_clause] = arg
                new_args.append(new_arg_clause)
                x_count += 1
        return Clause(clause.op, new_args), theta_copy

#______________________________________________________________________________


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


#kb = crime_kb
kb = input_kb
for keys in kb.clauses.keys():
    print keys,':',kb.clauses[keys]
raw_input()


#query = convert_to_clause(parse('F(Bob)'))
query = convert_to_clause(parse('G(Tom)'))

# to check if the statement has been proved
proof_flag = False

vbls_in_query = find_variables(query)
#print vbls_in_query
#print replace_with_variables(query),"\n"
print query

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
