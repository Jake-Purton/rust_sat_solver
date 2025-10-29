use std::collections::HashSet;

#[derive(Debug, Clone)]
pub struct CNF {
    pub clauses: Vec<Vec<i32>>,
    pub model: Vec<i32>,
}

impl CNF {

    pub fn pure_literal (&mut self) {

        // set containing all literals
        let mut set: HashSet<i32> = HashSet::new();

        for clause in &self.clauses {
            for l in clause {
                set.insert(*l);
            }
        }

        let mut one_found = false;

        for i in set.clone() {
            if !set.contains(&-i) {
                // would be faster if it was a prepend

                // add that variable as a unit clause
                self.clauses.push(vec![i]);
                self.unit_prop();
                one_found = true
            }
        }

        if !one_found {
            return;
        } else {
            self.pure_literal();
        }
    }

    pub fn unit_prop (&mut self) {

        let mut unit: Option<i32> = None;

        for clause in &self.clauses {
            if clause.len() == 1 {
                unit = Some(clause[0]);
                self.model.push(clause[0]);
                break;
            }
        }

        // if you have a unit to propogate
        if let Some(unit) = unit {
            let mut i = 0;
            let mut changed = false;
            while i < self.clauses.len() {
                // if clause is satisfied by the unit, remove whole clause
                if self.clauses[i].contains(&unit) {
                    self.clauses.remove(i);
                    changed = true;
                    // continue without incrementing i because vector shifted
                    continue;
                }

                // remove occurrences of -unit from the clause
                let original_len = self.clauses[i].len();
                self.clauses[i].retain(|&lit| lit != -unit);
                if self.clauses[i].len() != original_len {
                    changed = true;
                }
                i += 1;
            }

            if changed {
                self.unit_prop();
            }
        }

    }

    pub fn solve (&mut self) -> bool {

        loop {
            let m = self.model.len();
            
            self.unit_prop();
            self.pure_literal();
            if m == self.model.len() {
                break;
            }
        }

        if self.clauses.len() == 0 {
            // sat
            return true;
        } else {

            for clause in &self.clauses {
                if clause.len() == 0 {
                    // unsat
                    return false
                }
            }

            // clone it
            let mut d = self.clone();

            // choose a random literal to make true
            let l = d.clauses[0][0];
            d.clauses.push(vec![l]);

            // if that is solvable then
            if d.solve() {
                self.model = d.model;
                // shoukld probably reset clauses too
                return true;
            } else {
                self.clauses.push(vec![-l]);
                return self.solve();
            }

        }

    }
}