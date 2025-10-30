use std::collections::{HashSet, VecDeque};

#[derive(Debug, Clone)]
pub struct CNF {
    pub clauses: VecDeque<Vec<i32>>,
    pub model: Vec<i32>,

    // have the decisio  stack and push stuff onto it
    // when tou want to backtrack return the state that you want go back to / the level you wabt or size
    // of the stack
    // pub decision_stack: Vec<(i32, bool)>
    // boolean true if it was a decision, false if it was implied by something else
}

impl CNF {

    pub fn pure_literal(&mut self) {
        // iterative pure literal elimination
        loop {
            let mut all: HashSet<i32> = HashSet::new();
            for clause in &self.clauses {
                for &l in clause {
                    all.insert(l);
                }
            }

            let mut pure: HashSet<i32> = HashSet::new();
            for &l in &all {
                if !all.contains(&-l) {
                    // skip if already assigned (avoid duplicates)
                    if !self.model.contains(&l) && !self.model.contains(&-l) {
                        pure.insert(l);
                    }
                }
            }

            if pure.is_empty() {
                break;
            }

            // add pure literals to model
            for &l in &pure {
                if !self.model.contains(&l) {
                    self.model.push(l);
                }
            }

            // remove clauses satisfied by any pure literal
            self.clauses
                .retain(|clause| !clause.iter().any(|lit| pure.contains(lit)));

            // continue loop to find newly exposed pure literals
        }
    }

    pub fn unit_prop(&mut self) {
        loop {
            // find a unit clause
            let mut unit_opt: Option<i32> = None;
            for clause in &self.clauses {
                if clause.len() == 1 {
                    unit_opt = Some(clause[0]);
                    break;
                }
            }

            let unit = match unit_opt {
                Some(u) => u,
                None => break, // no more unit clauses
            };

            // record assignment if not already present
            if !self.model.contains(&unit) {
                self.model.push(unit);
            }

            // propagate unit: remove clauses satisfied by unit and remove -unit from others
            let mut i = 0;
            let mut changed = false;
            while i < self.clauses.len() {
                // if clause is satisfied by the unit, remove whole clause
                if self.clauses[i].contains(&unit) {
                    self.clauses.remove(i);
                    changed = true;
                    continue; // don't increment i, vector shifted
                }

                // remove occurrences of -unit from the clause
                let original_len = self.clauses[i].len();
                self.clauses[i].retain(|&lit| lit != -unit);
                if self.clauses[i].len() != original_len {
                    changed = true;
                }

                // if clause became empty, keep it (solve will detect unsat)
                i += 1;
            }

            // continue loop if any change produced new unit clauses
            if !changed {
                // still need to continue because we consumed one unit; check for more
                continue;
            }
        }
    }

    pub fn solve (&mut self) -> bool {

        // maybe sort first
        // this is not yet faster but could be maybe 
        // self.clauses.make_contiguous().sort_unstable_by_key(|clause| clause.len());

        // this is slower
        // do tautological reduction first
        // let mut prune_vec = Vec::new();
        // for c in 0..self.clauses.len() {
        //     for i in &self.clauses[c] {
        //         if self.clauses[c].contains(&-i) {

        //             prune_vec.push(c);                    
        //             break;

        //         }
        //     }
        // }

        // while let Some(a) = prune_vec.pop() {
        //     self.clauses.remove(a);
        // }

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
            d.clauses.push_front(vec![l]);

            // if that is solvable then
            if d.solve() {
                self.model = d.model;
                // shoukld probably reset clauses too
                return true;
            } else {
                self.clauses.push_front(vec![-l]);
                return self.solve();
            }

        }

    }
}