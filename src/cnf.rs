use std::collections::HashSet;

#[derive(Debug, Clone)]
pub struct Cnf {
    pub clauses: Vec<Vec<i32>>,
    
    pub model: Vec<Option<bool>>,

    // have the decisio  stack and push stuff onto it
    // when tou want to backtrack return the state that you want go back to / the level you wabt or size
    // of the stack

    // decision and clause
    pub decision_stack: Vec<(i32, Option<usize>)>,
    pub dl: u32,
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

        Self { clauses, model: vec![None; largest as usize], decision_stack: Vec::new(), dl: 0 }

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

    // #[inline]
    // fn remove(&mut self, lit: i32) {
    //     let var = lit.abs() as usize;

    //     self.model[var-1] = None;
    // }

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
                    self.decision_stack.push((last_unassigned, Some(index)));
                    found_unit = true;
                }

            }

            if !found_unit {
                break; // nothing more to propagate
            }
        }

        true
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

    fn backjump(&mut self, dl: u32) {
        while dl < self.dl {
            if let Some((lit, reason)) = self.decision_stack.pop() {
                self.model[lit.abs() as usize - 1] = None;
                if reason.is_none() {
                    self.dl -= 1;
                }
            }
        }
    }


    fn clean(&mut self) {
        let mut new_clauses = Vec::new();

        for clause in &self.clauses {
            let mut seen = std::collections::HashSet::new();
            let mut cleaned = Vec::new();
            let mut tautology = false;

            for &lit in clause {
                // check for tautology (contains both lit and -lit)
                if seen.contains(&-lit) {
                    tautology = true;
                    break;
                }

                // insert literal if new
                if seen.insert(lit) {
                    cleaned.push(lit);
                }
            }

            if !tautology {
                // Optional: sort and deduplicate for consistency
                cleaned.sort();
                cleaned.dedup();
                new_clauses.push(cleaned);
            }
        }

        self.clauses = new_clauses;
    }

    pub fn solve_cdcl (&mut self) -> bool {

        // self.clean();
        self.unit_propigate();

        loop {
            // backtracking

            while self.not_satisfiable() {

                if self.dl == 0 {
                    return false;
                }

                let (learned_clause, dl) = self.analyse_conflict();
                
                self.backjump(dl);
                self.clauses.push(learned_clause);

                self.unit_propigate();

            }

            // choose that variable
            if let Some(l) = self.choose_unassigned_literal() {
                self.dl += 1;
                self.decision_stack.push((l, None));
                self.insert(l);
                self.unit_propigate();
            }


            // end

            if self.all_clauses_solved() {
                break;
            }

        }

        true

    }

    fn analyse_conflict(&self) -> (Vec<i32>, u32) {
        // 1️⃣ Find the conflicting clause
        let mut conflict_clause = None;
        for clause in &self.clauses {
            if clause.iter().all(|&lit| self.is_false(lit)) {
                conflict_clause = Some(clause.clone());
                break;
            }
        }
        let mut conflict = conflict_clause.expect("analyse_conflict called but no conflict clause found");

        // 2️⃣ Bookkeeping
        let mut seen: HashSet<i32> = HashSet::new(); // seen variable indices (abs)
        let mut learnt: Vec<i32> = Vec::new();
        let mut counter = 0; // how many lits in conflict are from current dl
        let mut uip: i32 = 0; // the UIP literal (with sign)
        let mut idx = self.decision_stack.len();

        // optional debug
        // println!("[analyse_conflict] start conflict={:?} dl={}", conflict, self.dl);

        // 3️⃣ Main resolution loop
        loop {
            // mark literals in current conflict clause
            for &lit in &conflict {
                let var = lit.abs();
                if !seen.contains(&var) {
                    seen.insert(var);

                    let (dl, _) = self.decision_level(var);
                    if dl == self.dl {
                        counter += 1;
                    } else {
                        // keep literals from earlier levels for the learned clause
                        learnt.push(lit);
                    }
                }
            }

            // walk backward on the decision stack to find the last assigned var that is in 'seen'
            loop {
                if idx == 0 {
                    break;
                }
                idx -= 1;
                uip = self.decision_stack[idx].0; // literal (signed) that was assigned
                let var = uip.abs();
                if seen.contains(&var) {
                    break;
                }
            }

            // handle corner (shouldn't normally happen)
            if counter == 0 {
                // no literal from current level found (shouldn't happen in normal CDCL)
                break;
            }

            // we are resolving on the variable `uip.abs()`
            counter -= 1;
            if counter == 0 {
                // found the 1-UIP: stop resolving
                break;
            }

            // otherwise, resolve conflict with the reason clause for the UIP variable
            let (_, reason_opt) = self.decision_level(uip.abs());
            if let Some(reason_idx) = reason_opt {
                let reason_clause = &self.clauses[reason_idx];

                // Proper resolution: new_conflict = (conflict \ {v}) ∪ (reason_clause \ {v})
                let v = uip.abs();
                let mut new_conflict: Vec<i32> = Vec::new();
                let mut inserted: HashSet<i32> = HashSet::new();

                // keep conflict literals except those with var v
                for &lit in &conflict {
                    if lit.abs() != v {
                        if inserted.insert(lit) {
                            new_conflict.push(lit);
                        }
                    }
                }

                // add reason literals (except var v), avoid duplicates
                for &lit in reason_clause {
                    if lit.abs() != v {
                        if inserted.insert(lit) {
                            new_conflict.push(lit);
                        }
                    }
                }

                conflict = new_conflict;
            } else {
                // if no reason (decision variable), we can't resolve further
                break;
            }
        }

        // 4️⃣ Build learned clause: literals from earlier levels + negation of UIP
        // negate UIP literal:
        learnt.push(-uip);

        // Optional: canonicalize learned clause (sort/dedup)
        learnt.sort();
        learnt.dedup();

        // 5️⃣ Compute backtrack level: max decision level among learnt literals except UIP
        let backtrack_level = learnt
            .iter()
            .filter(|&&lit| lit.abs() != uip.abs())
            .map(|&lit| self.decision_level(lit.abs()).0)
            .max()
            .unwrap_or(0);

        // debug
        // println!("[analyse_conflict] learned={:?} backtrack={}", learnt, backtrack_level);

        (learnt, backtrack_level)
    }

    fn decision_level(&self, lit: i32) -> (u32, Option<usize>) {

        let mut dl = 0;

        for i in &self.decision_stack {

            if i.1.is_none() {
                dl += 1;
            }

            if i.0.abs() == lit.abs() {
                return (dl, i.1);
            }

        }

        println!("THIS SHOULD NOT OCCUR");

        return (0, None);

    }

    fn is_partial (&self) -> bool {
        self.model.iter().any(|assignment| *assignment == None)
    }

    fn not_satisfiable (&self) -> bool {
        self.clauses.iter().any(|clause| {
            clause.iter().all(|&lit| self.is_false(lit))
        })
    }

    fn all_clauses_solved(&self) -> bool {
        // for all clauses
        self.clauses.iter().all(|clause| {
            // any var must be true
            clause.iter().any(|&lit| self.is_true(lit))
        })
    }
}
