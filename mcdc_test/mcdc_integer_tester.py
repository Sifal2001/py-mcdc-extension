from pyeda.inter import *
from itertools import product
from z3 import ( 
    Solver,
    Int,
    sat,
    BoolRef,
    Or as Z3Or, 
    Bool as Z3Bool,

)
from typing import Dict, List, Tuple, Union, Callable
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
    
    def _create_constraint(self, var, op: str, value: int, target: bool) -> BoolRef:
        operators = {
            '>': lambda x, y: x > y if target else x <= y,
            '<': lambda x, y: x < y if target else x >= y,
            '>=': lambda x, y: x >= y if target else x < y,
            '<=': lambda x, y: x <= y if target else x > y,
            '==': lambda x, y: x == y if target else x != y,
            '!=': lambda x, y: x != y if target else x == y
        }

        if op not in operators:
            raise ValueError(f"Unsupported operator: {op}")
            
        return operators[op](var, value)

    def evaluate_condition(self, env: Dict) -> bool:
        # Creating a dictionary of boolean values for each condition
        bool_values = {}
        for i, (desc, cond) in enumerate(self.conditions):
            bool_values[f"B{i}"] = cond(env)
        
        # Evaluating using the BDD with the assigned values
        assignment = {var: bool_values[var.name] for var in self.boolean_vars}
        return self.bdd.restrict(assignment).is_one()
    

class Z3Tester:
    def __init__(self):
        self.conditions = [("x > 5", lambda env: env["x"] > 5)]
        self.boolean_vars = [bddvar("B0")]

    def _create_constraint(self, var, op: str, value: int, target: bool):
        operators = {
            '>': lambda x, y: x > y if target else x <= y,
            '<': lambda x, y: x < y if target else x >= y,
            '>=': lambda x, y: x >= y if target else x < y,
            '<=': lambda x, y: x <= y if target else x > y,
            '==': lambda x, y: x == y if target else x != y,
            '!=': lambda x, y: x != y if target else x == y
        }

        if op not in operators:
            raise ValueError(f"Unsupported operator: {op}")

        return operators[op](var, value)

    def evaluate_condition(self, env):
        return self.conditions[0][1](env)

# Testing _create_constraint
tester = Z3Tester()
x = Int("x")
constraint = tester._create_constraint(x, ">", 5, True)

s = Solver()
s.add(constraint)
s.add(x < 10)

if s.check() == sat:
    print("Constraint satisfied with:", s.model())
else:
    print("No solution found")

# Testing evaluate_condition
print("Evaluate condition with x = 7:", tester.evaluate_condition({"x": 7}))  
print("Evaluate condition with x = 4:", tester.evaluate_condition({"x": 4}))  