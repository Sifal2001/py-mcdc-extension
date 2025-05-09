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
    
    def generate_mcdc_tests(self) -> List[Dict]:
        """Generate MC/DC test cases"""
        test_cases = []
        
        # For each condition
        for i, var in enumerate(self.boolean_vars):
            pair_found = False
            
            # Trying different combinations for independence pairs
            for others in range(2 ** (len(self.boolean_vars) - 1)):
                # Create two assignments that differ only in var
                assignment1 = {}
                assignment2 = {}
                
                # Setting up the assignments
                bit = 0
                for j, other_var in enumerate(self.boolean_vars):
                    if j == i:
                        assignment1[other_var.name] = 0
                        assignment2[other_var.name] = 1
                    else:
                        val = (others >> bit) & 1
                        assignment1[other_var.name] = val
                        assignment2[other_var.name] = val
                        bit += 1
                
                # Finding inputs for both assignments
                inputs1 = self.find_integer_inputs(assignment1, var.name)
                inputs2 = self.find_integer_inputs(assignment2, var.name)
                
                if inputs1 and inputs2:
                    # Verifying independence
                    output1 = self.evaluate_condition(inputs1)
                    output2 = self.evaluate_condition(inputs2)
                    
                    if output1 != output2:
                        pair_found = True
                        test_case1 = {
                            'inputs': inputs1,
                            'expected_output': output1,
                            'condition_tested': var.name,
                            'condition_value': 0,
                            'assignments': assignment1
                        }
                        test_case2 = {
                            'inputs': inputs2,
                            'expected_output': output2,
                            'condition_tested': var.name,
                            'condition_value': 1,
                            'assignments': assignment2
                        }
                        test_cases.extend([test_case1, test_case2])
                        self.coverage_data['covered_conditions'].add(var.name)
                        self.coverage_data['total_cases'] += 2
                        self.coverage_data['test_cases'].extend([test_case1, test_case2])
                        break
            
            if not pair_found:
                print(f"Warning: Could not find independence pair for condition {var.name}")
        
        return test_cases


#Testing genarate_mcdc_tests
conditions = [
    ("x > 0", lambda env: env["var_0"] > 0),
    ("y == 5", lambda env: env["var_1"] == 5)
]
decision_structure = "B0 AND B1"

tester = MCDCIntegerTester(conditions, decision_structure)
test_cases = tester.generate_mcdc_tests()

for i, test in enumerate(test_cases, 1):
    print(f"Test Case {i}:")
    print(f"  Inputs: {test['inputs']}")
    print(f"  Expected Output: {test['expected_output']}")
    print(f"  Condition Tested: {test['condition_tested']}")
    print(f"  Boolean Assignments: {test['assignments']}")


assert len(test_cases) == 4, "Should produce 2 test cases per condition"
print(" Correct number of test cases (2 per condition)")

for i in range(0, len(test_cases), 2):
    c1, c2 = test_cases[i], test_cases[i + 1]
    assert c1["condition_tested"] == c2["condition_tested"], "Pair must test the same condition"
    print(f" Condition {c1['condition_tested']} tested independently")
    assert c1["expected_output"] != c2["expected_output"], "Outputs must differ"
    print(f" Condition {c1['condition_tested']} causes output to change")
    # Verifying other boolean assignments are the same
    for k in c1["assignments"]:
        if k != c1["condition_tested"]:
            assert c1["assignments"][k] == c2["assignments"][k], f"{k} should match in both assignments"
print("✅ All MC/DC condition independence checks passed")