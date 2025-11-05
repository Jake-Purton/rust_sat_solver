use std::collections::{HashMap, HashSet};

#[derive(Debug, Clone)]
pub struct Cnf {
    pub clauses: Vec<Vec<i32>>,
    
    pub model: HashSet<i32>,

    // have the decisio  stack and push stuff onto it
    // when tou want to backtrack return the state that you want go back to / the level you wabt or size
    // of the stack
    pub decision_stack: Vec<(i32, bool)>
    // boolean flag is the decision flag
}

enum Decision {
    True,
    False,
    Undecided
}

impl Cnf {

    fn evaluate_clause(&self, clause: usize) -> Decision {
        let mut undecided = false;
        for literal in &self.clauses[clause] {
            if self.model.contains(literal) {
                return Decision::True;
            } else if !self.model.contains(&-literal) {
                undecided = true;
            }
        }

        if undecided {
            Decision::Undecided
        } else {
            Decision::False
        }
    }

    fn pure_literal(&mut self) {
        let mut polarities: HashMap<i32, i8> = HashMap::new();

        for (index, clause) in self.clauses.iter().enumerate() {
            if matches!(self.evaluate_clause(index), Decision::True) {
                continue;
            }

            for lit in clause {
                let var = lit.abs();
                // Skip assigned literals
                if self.model.contains(lit) || self.model.contains(&-lit) {
                    continue;
                }

                let entry = polarities.entry(var).or_insert(0);
                if *lit > 0 {
                    *entry |= 1; // bit 0 = positive
                } else {
                    *entry |= 2; // bit 1 = negative
                }
            }
        }

        // Find pure literals (only one polarity)
        for (&var, &mask) in polarities.iter() {
            if mask == 1 {
                // Pure positive
                self.model.insert(var);
                self.decision_stack.push((var, false)); // implied
            } else if mask == 2 {
                // Pure negative
                self.model.insert(-var);
                self.decision_stack.push((-var, false));
            }
        }
    }

    fn unit_propigate (&mut self) -> bool {
        loop {
            let mut found_unit = false;

            for (index, clause) in self.clauses.iter().enumerate() {

                // skip satisfied clauses
                if matches!(self.evaluate_clause(index), Decision::True) {
                    continue;
                }

                match self.evaluate_clause(index) {
                    Decision::True => continue,
                    Decision::False => return false,
                    Decision::Undecided => (),
                }

                // get all of the unassigned literals
                let unassigned: Vec<i32> = clause
                    .iter()
                    .filter(|lit| !self.model.contains(*lit) && !self.model.contains(&-**lit))
                    .cloned()
                    .collect();

                if unassigned.len() == 1 {
                    let lit = unassigned[0];
                    self.model.insert(lit);
                    self.decision_stack.push((lit, false)); // false = implied, not a decision
                    found_unit = true;
                    break; // restart scanning after each propagation
                }
            }

            if !found_unit {
                break; // nothing more to propagate
            }
        }

        true
    }

    // backtrack to before the last decision
    pub fn backtrack (&mut self) {

        while let Some(a) = self.decision_stack.pop() {
            
            self.model.remove(&a.0);

            if a.1 {
                return;
            }

        }

    }

    pub fn choose_unassigned_literal (&self) -> i32 {
        for i in &self.clauses {
            for l in i {
                if !self.model.contains(l) {
                    return *l; 
                }
            }
        }

        0
    }

    pub fn solve (&mut self) -> bool {
        self.pure_literal();

        if !self.unit_propigate() {
            return false;
        }

        // check if it's solved
        for i in 0..self.clauses.len() {
            if matches!(self.evaluate_clause(i), Decision::True) {
                return true;
            }
        }

        let lit = self.choose_unassigned_literal();
        if lit == 0 {
            return true;
        }

        // do decision
        self.model.insert(lit);
        self.decision_stack.push((lit, true));

        if self.solve() {
            return true;
        }

        // try the other one
        self.backtrack();
        self.model.insert(-lit);
        self.decision_stack.push((-lit, true));

        if self.solve() {
            return true;
        }

        // failed
        self.backtrack();
        false
    }
}