import random
import time
import itertools

# ------ Utility Functions ------

def print_cnf(cnf):
    """Nicely print a CNF formula."""
    return ' ∧ '.join(['(' + ' ∨ '.join((f'x{abs(l)}' if l>0 else f'¬x{abs(l)}') for l in sorted(c)) + ')' for c in cnf])

# ------ Resolution Solver (Verbose) ------

def resolution_solve_verbose(cnf, verbose=True):
    """
    Naive propositional resolution, with optional verbose tracing.
    Returns True if UNSAT (empty clause derived), False if SAT (no new resolvents).
    """
    clauses = set(frozenset(c) for c in cnf)
    if verbose:
        print("Initial clauses:", print_cnf(clauses))
    new = set()
    round = 1
    while True:
        if verbose:
            print(f"\nResolution Round {round}:")
        pairs = itertools.combinations(clauses, 2)
        for c1, c2 in pairs:
            for l in c1:
                if -l in c2:
                    resolvent = (set(c1) | set(c2)) - {l, -l}
                    if verbose:
                        print(f" Resolvant of {set(c1)} and {set(c2)} on literal {l}: {resolvent}")
                    if not resolvent:
                        if verbose:
                            print("Derived empty clause. CNF is UNSAT.")
                        return True
                    new.add(frozenset(resolvent))
        if new.issubset(clauses):
            if verbose:
                print("No new clauses can be derived. CNF is SAT (wrt resolution saturation).")
            return False
        clauses |= new
        new.clear()
        round += 1

# ------ DP Solver (Verbose) ------

def dp_solve_verbose(cnf, variables=None, verbose=True, depth=0):
    """
    Davis-Putnam elimination with verbose steps.
    Returns True if UNSAT, False if SAT.
    """
    indent = '  ' * depth
    if variables is None:
        variables = set(abs(l) for c in cnf for l in c)
    if not cnf:
        if verbose:
            print(indent + "CNF empty — trivially SAT.")
        return False
    if any(len(c)==0 for c in cnf):
        if verbose:
            print(indent + "Found empty clause — CNF is UNSAT.")
        return True
    v = variables.pop()
    if verbose:
        print(indent + f"Eliminate variable x{v}")
        print(indent + " Current CNF:", print_cnf(cnf))
    pos = [c for c in cnf if v in c]
    neg = [c for c in cnf if -v in c]
    others = [c for c in cnf if v not in c and -v not in c]
    resolvents = []
    for c1 in pos:
        for c2 in neg:
            resolvent = (c1|c2) - {v, -v}
            resolvents.append(resolvent)
            if verbose:
                print(indent + f"  Resolvent of {c1} & {c2}: {resolvent}")
    new_cnf = others + resolvents
    return dp_solve_verbose(new_cnf, set(variables), verbose, depth+1)

# ------ DPLL Solver (Verbose) ------

def dpll_solve_verbose(cnf, assignment=None, verbose=True, depth=0):
    """
    DPLL with unit propagation & pure-literal elimination (verbose).
    Returns True if SAT, False if UNSAT.
    """
    indent = '  ' * depth
    if assignment is None:
        assignment = {}
    if verbose and depth==0:
        print("Initial CNF:", print_cnf(cnf))
    # Unit propagation
    while True:
        # find unit
        unit = [next(iter(c)) for c in cnf if len(c)==1]
        if unit:
            for l in unit:
                v, val = abs(l), (l>0)
                assignment[v] = val
                if verbose:
                    print(indent + f"Unit propagate x{v}={'T' if val else 'F'}")
                cnf = propagate(cnf, v, val)
            continue
        # pure literal
        counts = {l: sum(1 for c in cnf if l in c) for c in cnf for l in c}
        pure = [l for l in counts if -l not in counts]
        if pure:
            l = pure[0]
            v, val = abs(l), (l>0)
            assignment[v] = val
            if verbose:
                print(indent + f"Pure literal x{v}={'T' if val else 'F'}")
            cnf = propagate(cnf, v, val)
            continue
        break
    if not cnf:
        if verbose:
            print(indent + "All clauses satisfied — CNF is SAT.")
        return True
    if any(len(c)==0 for c in cnf):
        if verbose:
            print(indent + "Empty clause found — backtrack (UNSAT branch)")
        return False
    # choose variable
    l = next(iter(next(iter(cnf))))
    v = abs(l)
    if verbose:
        print(indent + f"Branch on x{v} = True/False")
    for val in (True, False):
        if verbose:
            print(indent + f"Try x{v}={'T' if val else 'F'}")
        new = propagate(cnf, v, val)
        if dpll_solve_verbose(new, {**assignment, v: val}, verbose, depth+1):
            return True
    if verbose:
        print(indent + f"Both assignments for x{v} failed — UNSAT at this branch.")
    return False

# ------ Clause Propagation ------

def propagate(cnf, var, value):
    new = []
    for c in cnf:
        if (value and var in c) or (not value and -var in c):
            continue
        reduced = set(c)
        falsified = -var if value else var
        reduced.discard(falsified)
        new.append(reduced)
    return new

# ------ Random CNF Generator ------

def generate_random_cnf(n_vars, n_clauses, size):
    cnf = []
    for _ in range(n_clauses):
        clause = set()
        while len(clause) < size:
            lit = random.randint(1, n_vars) * (1 if random.random()<0.5 else -1)
            clause.add(lit)
        cnf.append(clause)
    return cnf

# ------ Detailed Examples ------
if __name__ == '__main__':
    random.seed(0)
    small_cnf = [ {1, -2}, {2, 3}, {-1, -3} ]
    print("\n=== Detailed Resolution Example ===")
    print("Formula:", print_cnf(small_cnf))
    resolution_solve_verbose(small_cnf)

    print("\n=== Detailed DP Example ===")
    print("Formula:", print_cnf(small_cnf))
    unsat = dp_solve_verbose(small_cnf.copy())
    print("Result:", "UNSAT" if unsat else "SAT")

    print("\n=== Detailed DPLL Example ===")
    print("Formula:", print_cnf(small_cnf))
    sat = dpll_solve_verbose(small_cnf.copy())
    print("Result:", "SAT" if sat else "UNSAT")

    # Quick sanity check on known examples
    tests = {
        "Tautology SAT": [{1, -1}],
        "Contradiction UNSAT": [{1}, {-1}],
        "Parity(2) SAT": [{1,2}, {-1,-2}],
        "Parity(2) UNSAT": [{1,2}, {-1,-2}, {1,-2}]
    }
    print("\n=== Quick Tests ===")
    for name, cnf in tests.items():
        print(f"\n{name} ({print_cnf(cnf)}):")
        print("  Resolution →", "UNSAT" if resolution_solve_verbose(cnf, verbose=False) else "SAT")
        print("  DP →", "UNSAT" if dp_solve_verbose(cnf.copy(), verbose=False) else "SAT")
        print("  DPLL →", "SAT" if dpll_solve_verbose(cnf.copy(), verbose=False) else "UNSAT")

    # Benchmark remains as before (omitted for brevity)
