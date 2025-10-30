import random

def generate_random_cnf(filename, num_vars, num_clauses, max_clause_size=None):
    """
    Generate a random CNF file with the given number of variables and clauses.
    
    Args:
        filename (str): Output filename (e.g., "test.cnf")
        num_vars (int): Number of variables (positive integers)
        num_clauses (int): Number of clauses
        max_clause_size (int, optional): Max number of literals per clause (default: num_vars)
    """
    if max_clause_size is None:
        max_clause_size = num_vars

    with open(filename, "w") as f:
        # Write header comments
        f.write("c comment line\n")
        f.write("c this is a test problem\n\n")
        f.write(f"p cnf {num_vars} {num_clauses}\n\n")

        # Generate each clause
        for _ in range(num_clauses):
            clause_size = random.randint(1, max_clause_size)  # random clause length
            clause_vars = random.sample(range(1, num_vars + 1), k=clause_size)
            # Randomly negate literals
            clause = [str(var if random.choice([True, False]) else -var) for var in clause_vars]
            clause_line = " ".join(clause) + " 0\n"
            f.write(clause_line)

    print(f"✅ CNF file '{filename}' created with {num_vars} vars and {num_clauses} clauses.")


# Example usage:
if __name__ == "__main__":
    generate_random_cnf("test4.cnf", num_vars=300, num_clauses=40000)
