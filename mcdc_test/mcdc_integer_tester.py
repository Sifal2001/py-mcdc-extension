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
    
    
    def find_integer_inputs(self, target_bools: Dict[str, int], condition_tested: str) -> Dict[str, int]:
        #Finding integer inputs satisfying the target boolean values
        s = Solver()
        
        # Creating Z3 variables for each condition
        vars_dict = {}
        for i in range(len(self.conditions)):
            vars_dict[f"var_{i}"] = Int(f'var_{i}')
        
        # Extracting operators and values from condition descriptions
        for var_name, target_value in target_bools.items():
            idx = int(var_name[1:])  # Extracting index from Bx
            desc = self.conditions[idx][0]
            
            # Parsing the condition description
            parts = desc.split()
            var = vars_dict[f"var_{idx}"]
            op = parts[1]
            value = int(parts[2])
            
            # Adding the constraint
            s.add(self._create_constraint(var, op, value, bool(target_value)))
        
        # Adding boundary constraints
        for var in vars_dict.values():
            s.add(var >= -100, var <= 100)

        if s.check() == sat:
            model = s.model()
            return {name: model[var].as_long() 
                   for name, var in vars_dict.items()}
        return None

# Testing find_integer_inputs
conditions = [
    ("x > 5", lambda env: env["var_0"] > 5),
    ("y != 10", lambda env: env["var_1"] != 10),
]

tester = MCDCIntegerTester(conditions, "B0 OR B1")

# Target boolean condition: B0 = True, B1 = False
target_bools: Dict[str, int] = {
    'B0': 1,
    'B1': 0
}

inputs = tester.find_integer_inputs(target_bools, "B0")

# Print result
print("Generated Inputs:", inputs)

