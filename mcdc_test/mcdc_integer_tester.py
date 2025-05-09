from pyeda.inter import *
from itertools import product
from z3 import ( 
    Or as Z3Or, 
    Bool as Z3Bool,

)
from typing import List, Tuple
from datetime import datetime


class MCDCIntegerTester:
    def __init__(self, conditions: List[Tuple[str, callable]], decision_structure: str):
        self.conditions = conditions
        self.boolean_vars = [bddvar(f"B{i}") for i in range(len(conditions))]
        self.condition_map = {f"B{i}": cond for i, (desc, cond) in enumerate(conditions)}
        
        # Parsing and create the decision structure dynamically
        self.expr = self._parse_decision_structure(decision_structure)
        self.bdd = expr2bdd(self.expr)
        
        self.coverage_data = {
            'total_cases': 0,
            'covered_conditions': set(),
            'test_cases': [],
            'timestamp': datetime.utcnow().strftime('%Y-%m-%d %H:%M:%S')
        }

    def _parse_decision_structure(self, decision_str: str) -> object:
        """Parse a decision structure string into a PyEDA expression."""
        def _tokenize(expr: str) -> List[str]:
            expr = expr.replace('(', ' ( ').replace(')', ' ) ')
            return expr.split()

        def _parse_tokens(tokens: List[str]) -> object:
            if not tokens:
                raise ValueError("Empty expression")

            def get_precedence(op):
                return {
                    'NOT': 3,
                    'AND': 2,
                    'OR': 1
                }.get(op, 0)

            output = []
            operators = []

            for token in tokens:
                if token.startswith('B'):  
                    var_index = int(token[1:])
                    if var_index >= len(self.boolean_vars):
                        raise ValueError(f"Variable {token} exceeds number of conditions")
                    output.append(self.boolean_vars[var_index])
                elif token == '(':
                    operators.append(token)
                elif token == ')':
                    while operators and operators[-1] != '(':
                        op = operators.pop()
                        if op == 'NOT':
                            val = output.pop()
                            output.append(~val)
                        else:
                            right = output.pop()
                            left = output.pop()
                            if op == 'AND':
                                output.append(left & right)
                            elif op == 'OR':
                                output.append(left | right)
                    operators.pop()  # Removing '('
                else:  
                    while (operators and operators[-1] != '(' and 
                           get_precedence(operators[-1]) >= get_precedence(token)):
                        op = operators.pop()
                        if op == 'NOT':
                            val = output.pop()
                            output.append(~val)
                        else:
                            right = output.pop()
                            left = output.pop()
                            if op == 'AND':
                                output.append(left & right)
                            elif op == 'OR':
                                output.append(left | right)
                    operators.append(token)

            while operators:
                op = operators.pop()
                if op == 'NOT':
                    val = output.pop()
                    output.append(~val)
                else:
                    right = output.pop()
                    left = output.pop()
                    if op == 'AND':
                        output.append(left & right)
                    elif op == 'OR':
                        output.append(left | right)

            return output[0]

        tokens = _tokenize(decision_str)
        return _parse_tokens(tokens)
    
#Testing tokens 
if __name__ == "__main__":
    conditions = [
        ("x > 5", lambda env: env["var_0"] > 5),
        ("y != 10", lambda env: env["var_1"] != 10)
    ]
    decision_structure = "B0 AND B1"
    tester = MCDCIntegerTester(conditions, decision_structure)

    print("Truth Table (from BDD):")
    print("B0 B1 | Output")
    for b0, b1 in product([0, 1], repeat=2):
        result = tester.bdd.restrict({tester.boolean_vars[0]: b0,
                                      tester.boolean_vars[1]: b1}).is_one()
        print(f" {b0}  {b1}  |   {int(result)}")