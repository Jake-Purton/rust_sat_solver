mod cnf;

use cnf::CNF;
use std::io::Read;

fn main() {
    // let path = "input.txt";
    // let file = File::open(path).expect("Failed to open input.txt");
    // let reader = BufReader::new(file);

    let mut buf = String::new();
    std::io::stdin().read_to_string(&mut buf).expect("failed to read stdin");

    let mut clauses: Vec<Vec<i32>> = Vec::new();
    let mut current_clause: Vec<i32> = Vec::new();

    for line in buf.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('c') {
            continue;
        }
        if line.starts_with('p') {
            continue;
        }
        for token in line.split_whitespace() {
            let lit: i32 = match token.parse() {
                Ok(n) => n,
                Err(_) => continue,
            };
            if lit == 0 {
                if !current_clause.is_empty() {
                    clauses.push(current_clause);
                    current_clause = Vec::new();
                }
            } else {
                current_clause.push(lit);
            }
        }
    }

    if !current_clause.is_empty() {
        clauses.push(current_clause);
    }

    let mut cnf = CNF { clauses, model: Vec::new() };

    // println!("{:?}", cnf);
    // To solve after loading:

    if cnf.solve() {
        println!("SATISFIABLE");
    } else {
        println!("UNSATISFIABLE");
    }
    // println!("{:?}", cnf);
}