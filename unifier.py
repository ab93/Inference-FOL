
from utils import *

def isVariable(item):
    return isinstance(item, Clause) and item.op.islower() and item.args == []

def unify(x,y,subst = {}):

    if subst is None:
        return None

    elif x == y:
        return subst

    elif isVariable(x):
        return unifyVars(x,y,subst)

    elif isVariable(y):
        return unifyVars(y,x,subst)

    elif isinstance(x,Clause) and isinstance(y,Clause):
        return unify(x.args,y.args,unify(x.op,y.op,subst))

    elif isinstance(x,list) and isinstance(y,list) and len(x) == len(y):
        return unify(x[1:], y[1:], unify(x[0], y[0], subst))

    else:
        return None

def unifyVars(var,x,subst):
    if var in subst:
        return unify(subst[var],x,subst)
    subst_copy = subst.copy()
    subst_copy[var] = x
    return subst_copy