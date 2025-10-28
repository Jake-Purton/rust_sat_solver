mod cnf;

use cnf::CNF;

fn main() {

    let mut c = CNF {clauses: vec![vec![1, 2, -1], vec![3, -2], vec![-2], vec![4, 3], vec![2]], model: Vec::new()};

    println!("{:?}", c);
    println!("{:?}", c.solve());
    println!("{:?}", c);

}
