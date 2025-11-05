use std::collections::HashMap;

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

    #[allow(dead_code)]
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
                self.insert(var, self.current_level, None);
            } else if mask == 2 {
                // Pure negative
                self.insert(-var, self.current_level, None);
            }
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

    // Analyze conflict and return (learned_clause, backjump_level)
    fn analyze_conflict(&self, conflict_clause: usize) -> (Vec<i32>, u32) {
        use std::collections::HashSet;
        
        let mut learned = self.clauses[conflict_clause].clone();
        let mut seen: HashSet<i32> = HashSet::new();
        
        // Count literals at current level
        let mut current_level_count = 0;
        for &lit in &learned {
            if self.get_level(lit) == Some(self.current_level) {
                current_level_count += 1;
            }
        }
        
        // Resolve until we have exactly one literal at current level (1st-UIP)
        let mut trail_idx = self.decision_stack.len();
        while current_level_count > 1 && trail_idx > 0 {
            trail_idx -= 1;
            let (lit, level, _) = self.decision_stack[trail_idx];
            
            if level != self.current_level {
                continue;
            }
            
            if !learned.contains(&lit) {
                continue;
            }
            
            // Get reason clause for this literal
            let var = lit.abs() as usize;
            if let Some(reason_idx) = self.reason[var - 1] {
                // Resolve: remove lit and add literals from reason
                learned.retain(|&l| l != lit);
                
                for &reason_lit in &self.clauses[reason_idx] {
                    if reason_lit != lit && !seen.contains(&reason_lit.abs()) {
                        learned.push(reason_lit);
                        seen.insert(reason_lit.abs());
                    }
                }
                
                // Recount current level literals
                current_level_count = 0;
                for &l in &learned {
                    if self.get_level(l) == Some(self.current_level) {
                        current_level_count += 1;
                    }
                }
            }
        }
        
        // Calculate backjump level: second highest decision level in learned clause
        let mut max_level = 0;
        for &lit in &learned {
            if let Some(lvl) = self.get_level(lit) {
                if lvl < self.current_level && lvl > max_level {
                    max_level = lvl;
                }
            }
        }
        
        (learned, max_level)
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
        // Skip pure literal - usually not worth the overhead
        // self.pure_literal();

        // Initial unit propagation at level 0
        if let Some(_conflict) = self.unit_propigate() {
            return false; // UNSAT at level 0
        }

        loop {
            // Choose next literal to assign
            let Some(lit) = self.choose_unassigned_literal() else {
                return true; // All variables assigned, SAT
            };

            // Make decision
            self.current_level += 1;
            self.insert(lit, self.current_level, None);

            // Unit propagation
            loop {
                match self.unit_propigate() {
                    None => break, // No conflict, continue with next decision
                    Some(conflict_clause) => {
                        // Conflict found
                        if self.current_level == 0 {
                            return false; // UNSAT
                        }

                        // Analyze conflict and learn clause
                        let (learned_clause, backjump_level) = self.analyze_conflict(conflict_clause);
                        
                        // Add learned clause
                        self.clauses.push(learned_clause.clone());
                        
                        // Backjump
                        self.backtrack_to_level(backjump_level);
                        
                        // The learned clause should be unit under backjump level
                        // Continue propagating
                    }
                }
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