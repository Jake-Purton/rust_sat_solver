use std::collections::HashSet;

#[derive(Debug, Clone)]
pub struct Cdcl {
    pub clauses: Vec<Vec<i32>>,
    pub model: Vec<Option<bool>>,
    pub decision_stack: Vec<(i32, u32, bool)>, // literal, level, decision flag
    pub assignment_level: Vec<Option<u32>>,
    pub reason: Vec<Option<usize>>, // reason clause for each var
    pub current_level: u32,
}



enum Decision {
    True,
    False,
    Undecided
}

impl Cdcl {

    pub fn new(clauses: Vec<Vec<i32>>) -> Self {

        let mut largest = 0;

        for i in &clauses {
            for l in i {
                if largest < l.abs() {
                    largest = l.abs();
                }
            }
        }

        Self { 
            clauses, 
            model: vec![None; largest as usize], 
            decision_stack: Vec::new(),
            assignment_level: vec![None; largest as usize],
            reason: vec![None; largest as usize],
            current_level: 0,
        }

    }

    #[inline]
    fn insert(&mut self, lit: i32, level: u32, reason: Option<usize>) {
        let var = lit.abs() as usize;
        
        if lit > 0 {
            self.model[var - 1] = Some(true);
        } else {
            self.model[var - 1] = Some(false);
        }
        
        self.assignment_level[var - 1] = Some(level);
        self.reason[var - 1] = reason;
        self.decision_stack.push((lit, level, reason.is_none()));
    }

    #[inline]
    fn remove(&mut self, lit: i32) {
        let var = lit.abs() as usize;

        self.model[var-1] = None;
        self.assignment_level[var-1] = None;
        self.reason[var-1] = None;
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
        return self.model[var-1].is_some();
    }

    #[inline]
    fn get_level(&self, lit: i32) -> Option<u32> {
        let var = lit.abs() as usize;
        self.assignment_level[var - 1]
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

    // Returns None if no conflict, Some(clause_index) if conflict
    fn unit_propigate(&mut self) -> Option<usize> {
        loop {
            let mut found_unit = false;

            for index in 0..self.clauses.len() {

                match self.evaluate_clause(index) {
                    Decision::True => continue,
                    Decision::False => return Some(index), // conflict
                    Decision::Undecided => (),
                }


                let mut unassigned_count = 0;
                let mut last_unassigned = 0;
                for lit in &self.clauses[index] {
                    if self.is_true(*lit) {
                        unassigned_count = 0;
                        break;
                    }
                    if !self.contains(*lit) {
                        unassigned_count += 1;
                        last_unassigned = *lit;
                    }
                }

                if unassigned_count == 1 {
                    self.insert(last_unassigned, self.current_level, Some(index));
                    found_unit = true;
                    break; // restart propagation
                }

            }

            if !found_unit {
                break; // nothing more to propagate
            }
        }

        None // no conflict
    }

    // (learned clause, backjump level)
    fn analyse_conflict(&self, conflict_clause: usize) -> (Vec<i32>, u32) {
        
        // get the conflicting clause
        let mut learned: Vec<i32> = self.clauses[conflict_clause].clone();
        let mut seen: HashSet<i32> = HashSet::new();
        
        // get all of the variables into a set
        for &lit in &learned {
            seen.insert(lit.abs());
        }

        // figure out how many variables conflicting are from the current decision level
        let count_current_level = |clause: &Vec<i32>| -> usize {
            clause.iter()
                .filter(|&&lit| self.get_level(lit) == Some(self.current_level))
                .count()
        };
        
        // find the first UIP 
        let mut trail_idx = self.decision_stack.len();
        while count_current_level(&learned) > 1 && trail_idx > 0 {
            trail_idx -= 1;
            let (lit, level, _) = self.decision_stack[trail_idx];
            
            if level != self.current_level {
                continue;
            }
            
            // if its not in the clause
            let var = lit.abs();
            if !seen.contains(&var) {
                continue;
            }
            
            // find the clause (reason) that caused this variable assignment
            // if it was a decision skip it
            let reason_idx = match self.reason[(var - 1) as usize] {
                Some(idx) => idx,
                None => continue,
            };
            
            // remove the literal
            learned.retain(|&l| l.abs() != var);
            seen.remove(&var);
            
            // add the negation conflicting variables except for the resolved one
            // if our thing forces 7 to be false then the negation of the rest of the variables in that clause
            // allow 7 to be true for example
            // this is probably the msot confusing part
            for &reason_lit in &self.clauses[reason_idx] {
                let reason_var = reason_lit.abs();
                if reason_var != var && !seen.contains(&reason_var) {
                    learned.push(reason_lit);
                    seen.insert(reason_var);
                }
            }
        }
        
        // backjump to the second highest decision level
        let mut backjump_level = 0;
        for &lit in &learned {
            if let Some(lvl) = self.get_level(lit) {
                if lvl < self.current_level && lvl > backjump_level {
                    backjump_level = lvl;
                }
            }
        }
        
        (learned, backjump_level)
    }

    // backtrack to a specific level
    fn backtrack_to_level(&mut self, target_level: u32) {
        while let Some((_lit, level, _)) = self.decision_stack.last() {
            if *level <= target_level {
                break;
            }
            
            let (lit, _, _) = self.decision_stack.pop().unwrap();
            self.remove(lit);
        }
        
        self.current_level = target_level;
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
        if let Some(_) = self.unit_propigate() {
            return false; // already unsat
        }

        loop {
            // Check if all variables assigned
            let Some(lit) = self.choose_unassigned_literal() else {
                return true; // satisfiable
            };

            // decide
            self.current_level += 1;
            self.insert(lit, self.current_level, None);

            // keep propogatinf until no more conflicts or unsat
            while let Some(conflict_clause) = self.unit_propigate() {
                if self.current_level == 0 {
                    return false; // UNSAT
                }

                // analyse the conflicts to get the learned clauses
                let (learned_clause, backjump_level) = self.analyse_conflict(conflict_clause);
                
                // append the learned clause to be propogated
                self.clauses.push(learned_clause);
                
                // backjump
                self.backtrack_to_level(backjump_level);
                
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sat() {
        // (x1 or x2) and (not x1 or x2) and (not x2 or x3)
        let clauses = vec![vec![1, 2], vec![-1, 2], vec![-2, 3]];
        let mut cnf = Cdcl::new(clauses);
        assert!(cnf.solve_not_recursive());
    }

    #[test]
    fn test_unsat() {
        // (x1) and (not x1)
        let clauses = vec![vec![1], vec![-1]];
        let mut cnf = Cdcl::new(clauses);
        assert!(!cnf.solve_not_recursive());
    }
}