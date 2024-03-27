import itertools as it
import hwtypes as ht
from hwtypes import smt_utils as fc
import pysmt.shortcuts as smt
import pysmt.logics as logics

_cache = {}
def new_var(s, bvlen):
    if s in _cache:
        return _cache[s]
    v = ht.SMTBitVector[bvlen](name=s)
    _cache[s] = v
    return v

def get_model(query, solver_name='z3', logic=None):
    vars = query.get_free_variables()
    model = smt.get_model(smt.And(query), solver_name=solver_name, logic=logic)
    if model:
        return {v: int(model.get_value(v).constant_value()) for v in vars}
    return False

def is_constant(var: ht.SMTBit):
    return var.value.is_constant()

def all_smt(formula, keys=None, solver_name='z3'):
    vars = formula.get_free_variables()
    if keys is None:
        keys = vars
    with smt.Solver(solver_name, logic=logics.QF_BV) as solver:
        solver.add_assertion(formula)
        while solver.solve():
            yield {k: int(solver.get_value(k).constant_value()) for k in vars}
            partial_model = [smt.EqualsOrIff(k, solver.get_value(k)) for k in keys]
            solver.add_assertion(smt.Not(smt.And(partial_model)))


def next_state(cur : ht.SMTBit, cnt : ht.SMTBitVector, alive_vals, dead_vals):
    alive_next = fc.Or([cnt == i for i in alive_vals]).to_hwtypes()
    dead_next = fc.Or([cnt == i for i in dead_vals]).to_hwtypes()
    return cur.ite(alive_next, dead_next)

def find_oscillating_gol_patterns(num_steps, nR, nC, alive_vals=[2, 3], dead_vals=[3]):

    bvlen = 3
    BV = ht.SMTBitVector[bvlen]

    #Delcare Variables

    #create free variales for each None in alive_vals and dead_vals
    alive_vals = [BV(val) if val is not None else new_var(f"alive_{i}", bvlen) for i, val in enumerate(alive_vals)]
    dead_vals = [BV(val) if val is not None else new_var(f"dead_{i}", bvlen) for i, val in enumerate(dead_vals)]

    v = [
        [[new_var(f"v_{r}_{c}_{i}", bvlen) for c in range(nC)] for r in range(nR)] for i in range(num_steps+1)
    ]

    # This should print a sequence of board states using '.' for empty and '#' for filled
    # Each state should be seperated horizontally by a column of spaces
    # v is a 3D array of variables representing the game of life state at each step
    def pretty_print(model):
        #Alive and dead contain variables. We need to print the values of the variables
        print("Alive values: ", end='')
        for var in alive_vals:
            if var.value.is_constant():
                print(int(var.value.constant_value()), end=' ')
            else:
                print(model[var.value], end=' ')
        print()
        print("Dead values: ", end='')
        for var in dead_vals:
            if var.value.is_constant():
                print(int(var.value.constant_value()), end=' ')
            else:
                print(model[var.value], end=' ')
        print()

        for r in range(nR):
            for i in range(num_steps+1):
                for c in range(nC):
                    if model[v[i][r][c].value]:
                        print('#', end=' ')
                    else:
                        print('.', end=' ')
                print(' ', end='')
            print()



    #Declare Constraints

    #Each board var is either 0 or 1
    cons = []
    for r, c in it.product(range(nR), range(nC)):
        for i in range(num_steps+1):
            cons.append(v[i][r][c] < 2)

    #The boundary of the board is always dead
    cons_boundary = []
    for i in range(num_steps+1):
        for r, c in it.product(range(nR), range(nC)):
            if r == 0 or r == nR-1 or c == 0 or c == nC-1:
                cons_boundary.append(v[i][r][c] == 0)

    #Constraint that each alive and dead value is strictly ordered
    cons_unique = []
    for v0, v1 in zip(alive_vals[:-1], alive_vals[1:]):
        cons_unique.append(v0 < v1)
    for v0, v1 in zip(dead_vals[:-1], dead_vals[1:]):
        cons_unique.append(v0 < v1)
    cons_unique.append(dead_vals[0] > 0)
    cons_unique.append(alive_vals[0] > 0)


    #Constraint that vk is the next state of vk-1
    cons_rules = []
    for r, c in it.product(range(nR), range(nC)):
        for i in range(num_steps):
            n = BV(0)
            for dr, dc in it.product([-1, 0, 1], [-1, 0, 1]):
                if dr == 0 and dc == 0:
                    continue
                if 0 <= r + dr < nR and 0 <= c + dc < nC:
                    n += v[i][r + dr][c + dc]

            next_val = next_state(v[i][r][c]==1, n, alive_vals, dead_vals)
            cons_rules.append(v[i+1][r][c] == next_val)

    #ocillating pattern constraint
    cons_oscillating = []
    for r, c in it.product(range(nR), range(nC)):
        cons_oscillating.append(v[0][r][c] == v[num_steps][r][c])

    # for each prime factor of num_steps, make sure that the pattern is not static
    cons_unique_occilating = []
    for i in range(1, num_steps//2+1):
        if num_steps % i == 0:
            cons_or = []
            for r, c in it.product(range(nR), range(nC)):
                cons_or.append(v[0][r][c] != v[i][r][c])
            cons_unique_occilating.append(fc.Or(cons_or).to_hwtypes())
    query = fc.And(cons + cons_rules + cons_boundary + cons_oscillating + cons_unique_occilating + cons_unique).to_hwtypes()

    #use v[0], dead_vals, alive_vals as keys
    keys = [v[0][r][c].value for r, c in it.product(range(nR), range(nC))]
    keys += [var.value for var in (alive_vals + dead_vals) if not is_constant(var)]
    for model in all_smt(query.value, keys):
        pretty_print(model)
        print()

def find_static_gol_patterns(nR, nC):
    find_oscillating_gol_patterns(1, nR, nC)

#find_static_gol_patterns(10, 10)
alive_vals = [None, None]
dead_vals = [None, None]
find_oscillating_gol_patterns(3, 5, 6, alive_vals, dead_vals)