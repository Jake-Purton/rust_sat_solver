use std::collections::{HashMap};

#[derive(Debug, Clone)]
pub struct Cnf {
    pub clauses: Vec<Vec<i32>>,
    
    pub model: Vec<Option<bool>>,

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

    pub fn new(clauses: Vec<Vec<i32>>) -> Self {

        let mut largest = 0;

        for i in &clauses {
            for l in i {
                if largest < *l {
                    largest = *l;
                }
            }
        }

        Self { clauses, model: vec![None; largest as usize], decision_stack: Vec::new() }

    }

    #[inline]
    fn insert(&mut self, lit: i32) {
        let var = lit.abs() as usize;
        
        if lit > 0 {
            self.model[var - 1] = Some(true);
        } else {
            self.model[var - 1] = Some(false)
        }
    }

    #[inline]
    fn remove(&mut self, lit: i32) {
        let var = lit.abs() as usize;

        self.model[var-1] = None;
    }

    #[inline]
    fn is_true(&self, lit: i32) -> bool {
        let var = lit.abs() as usize;
        match self.model[var - 1] {
            Some(val) => (lit > 0 && val) || (lit < 0 && !val),
            None => false,
        }
    }

    #[inline]
    fn is_false(&self, lit: i32) -> bool {
        let var = lit.abs() as usize;
        match self.model[var - 1] {
            Some(val) => (lit > 0 && !val) || (lit < 0 && val),
            None => false,
        }
    }

    #[inline]
    fn contains(&self, lit: i32) -> bool {
        let var = lit.abs() as usize;
        return !self.model[var-1].is_none();
    }

    fn evaluate_clause(&self, clause: usize) -> Decision {
        let mut undecided = false;
        for literal in &self.clauses[clause] {


            if self.is_true(*literal) {
                return Decision::True;
            } else if !self.is_false(*literal) {
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
                if self.contains(*lit) {
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
                self.insert(var);
                self.decision_stack.push((var, false)); // implied
            } else if mask == 2 {
                // Pure negative
                self.insert(-var);
                self.decision_stack.push((-var, false));
            }
        }
    }

    fn unit_propigate (&mut self) -> bool {
        loop {
            let mut found_unit = false;

            for index in 0..self.clauses.len() {

                match self.evaluate_clause(index) {
                    Decision::True => continue,
                    Decision::False => return false,
                    Decision::Undecided => (),
                }


                let mut unassigned_count = 0;
                let mut last_unassigned = 0;
                for lit in &self.clauses[index] {
                    if self.is_true(*lit) {
                        break;
                    }
                    if !self.contains(*lit) {
                        unassigned_count += 1;
                        last_unassigned = *lit;
                    }
                }

                if unassigned_count == 1 {
                    self.insert(last_unassigned);
                    self.decision_stack.push((last_unassigned, false));
                    found_unit = true;
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
            
            self.remove(a.0);

            if a.1 {
                return;
            }

        }

    }

    pub fn choose_unassigned_literal (&self) -> Option<i32> {
        for i in &self.clauses {
            for l in i {
                if !self.contains(*l) {
                    return Some(*l); 
                }
            }
        }

        None
    }

    pub fn solve_not_recursive(&mut self) -> bool {
        self.pure_literal();

        // the decision and a boolean to store if we have tried that decisions negation
        let mut decisions: Vec<(i32, bool)> = Vec::new();

        loop {
            // if there is a conflict 
            if !self.unit_propigate() {


                if let Some((last_decision, tried_neg)) = decisions.pop() {
                    self.backtrack();

                    if !tried_neg {
                        // try the opposite branch
                        self.insert(-last_decision);
                        self.decision_stack.push((-last_decision, true));
                        decisions.push((-last_decision, true));
                        continue;
                    } else {
                        // keep going back
                        continue;
                    }
                } else {
                    // Nothing left to backtrack — unsat
                    return false;
                }
            }

            // Check if solved
            if self
                .clauses
                .iter()
                .enumerate()
                .all(|(i, _)| matches!(self.evaluate_clause(i), Decision::True))
            {
                return true;
            }

            // choose
            let Some(lit) = self.choose_unassigned_literal() else {
                return true; // All assigned
            };

            // assign
            self.insert(lit);
            self.decision_stack.push((lit, true));
            decisions.push((lit, false));
        }
    }


    pub fn _solve (&mut self) -> bool {
        self.pure_literal();

        if !self.unit_propigate() {
            return false;
        }

        // check if it's solved
        if self.clauses.iter().enumerate().all(|c| matches!(self.evaluate_clause(c.0), Decision::True)) {
            return true;
        }

        let lit = self.choose_unassigned_literal();
        if lit.is_none() {
            return true;
        }

        let lit = lit.unwrap();

        // do decision
        self.insert(lit);
        self.decision_stack.push((lit, true));

        if self._solve() {
            return true;
        }

        // try the other one
        self.backtrack();
        self.insert(-lit);
        self.decision_stack.push((-lit, true));

        if self._solve() {
            return true;
        }

        // failed
        self.backtrack();
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sat() {
        // (x1 or x2) and (not x1 or x2) and (not x2 or x3)
        let clauses = vec![vec![1, 2], vec![-1, 2], vec![-2, 3]];
        let mut cnf = Cnf::new(clauses);
        assert!(cnf._solve());
    }

    #[test]
    fn test_unsat() {
        // (x1) and (not x1)
        let clauses = vec![vec![1], vec![-1]];
        let mut cnf = Cnf::new(clauses);
        assert!(!cnf._solve());
    }
}