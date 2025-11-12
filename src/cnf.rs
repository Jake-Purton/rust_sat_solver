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

    // watched literals for clauses
    pub watched: Vec<(usize, usize)>,
}



enum Decision {
    True,
    False,
    Undecided
}

impl Cnf {

    pub fn new(clauses: Vec<Vec<i32>>) -> Self {

        let mut watched: Vec<(usize, usize)> = vec![(0, 1); clauses.len()];

        let mut largest = 0;



        for i in 0..clauses.len() {

            if clauses[i].len() == 1 {

                watched[i].1 = 0;

            }



            for l in 0..clauses[i].len() {

                if largest < clauses[i][l].abs() {

                    largest = clauses[i][l].abs();

                }

            }

        }



        Self {

            clauses,

            model: vec![None; largest as usize],

            decision_stack: Vec::new(),

            dl: 0,

            watched,

        }

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

    fn eval_watched(&mut self, index: usize) -> Decision {

        // optimise later

        if self.watched[index].0 == self.watched[index].1 {
            if self.is_false(self.clauses[index][self.watched[index].0]) {
                return Decision::False;
            } else if self.is_true(self.clauses[index][self.watched[index].0]) {
                return Decision::True;
            } else {
                return Decision::Undecided;
            }
        }

        // if a variable is false, you must find another
        if self.is_false(self.clauses[index][self.watched[index].0]) {

            for i in 0..self.clauses[index].len() {
                if i == self.watched[index].0 || i == self.watched[index].1 {
                    continue;
                }

                if !self.is_false(self.clauses[index][i]) {
                    
                    self.watched[index].0 = i;

                    // keep it and break
                    break;

                }
            }

        }

        if self.is_false(self.clauses[index][self.watched[index].1]) {

            for i in 0..self.clauses[index].len() {
                if i == self.watched[index].0 || i == self.watched[index].1 {
                    continue;
                }

                if !self.is_false(self.clauses[index][i]) {
                    
                    self.watched[index].1 = i;

                    // keep it and break
                    break;

                }
            }

        }

        // if both are still false then unsat
        if self.is_false(self.clauses[index][self.watched[index].0]) && self.is_false(self.clauses[index][self.watched[index].1]) {
            return Decision::False;
        } else if self.is_true(self.clauses[index][self.watched[index].0]) || self.is_true(self.clauses[index][self.watched[index].1]) {
            return Decision::True;
        } else if self.is_false(self.clauses[index][self.watched[index].0]) || self.is_false(self.clauses[index][self.watched[index].1]) {
            // clause is unit
            return Decision::Undecided;
        }
        // undecided but not unit
        Decision::Undecided
    }

    fn unit_prop_watched (&mut self) -> bool {
        loop {
            let mut found_unit = false;

            for index in 0..self.clauses.len() {

                match self.eval_watched(index) {
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

    pub fn solve_cdcl (&mut self) -> bool {

        // self.clean();
        self.unit_prop_watched();

        loop {
            // backtracking

            while self.not_satisfiable() {

                if self.dl == 0 {
                    return false;
                }

                let (learned_clause, dl) = self.analyse_conflict();
                
                self.backjump(dl);
                // add watch variables for the learned clause
                if learned_clause.len() == 1 {
                    
                    self.watched.push((0,0));
                } else {
                    self.watched.push((0,1))
                }
                self.clauses.push(learned_clause);

                self.unit_prop_watched();

            }

            // choose that variable
            if let Some(l) = self.choose_unassigned_literal() {
                self.dl += 1;
                self.decision_stack.push((l, None));
                self.insert(l);
                self.unit_prop_watched();
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

        let mut seen: HashSet<i32> = HashSet::new(); // seen variable indices (abs)
        let mut learnt: Vec<i32> = Vec::new();
        let mut counter = 0; // how many lits in conflict are from current dl
        let mut uip: i32 = 0; // the UIP literal (with sign)
        let mut idx = self.decision_stack.len();

        // optional debug
        // println!("[analyse_conflict] start conflict={:?} dl={}", conflict, self.dl);

        loop {
            // mark literals in current conflict clause
            for &lit in &conflict {
                let var = lit.abs();
                if !seen.contains(&var) {
                    seen.insert(var);

                    if let Some((dl, _)) = self.decision_level(var) {
                        if dl == self.dl {
                            counter += 1;
                        } else {
                            // keep literals from earlier levels for the learned clause
                            learnt.push(lit);
                        }
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

            if let Some((_, reason_opt)) = self.decision_level(uip.abs()) {
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
            } else {
                // UIP not found in decision stack (shouldn't happen)
                break;
            }
        }

        // 4️⃣ Build learned clause: literals from earlier levels + negation of UIP
        // negate UIP literal:
        learnt.push(-uip);

        // Optional: canonicalize learned clause (sort/dedup)
        learnt.sort();
        learnt.dedup();

        let backtrack_level = learnt
            .iter()
            .filter(|&&lit| lit.abs() != uip.abs())
            .filter_map(|&lit| self.decision_level(lit.abs()).map(|(dl, _)| dl))
            .max()
            .unwrap_or(0);

        // debug
        // println!("[analyse_conflict] learned={:?} backtrack={}", learnt, backtrack_level);

        (learnt, backtrack_level)
    }

    fn decision_level(&self, lit: i32) -> Option<(u32, Option<usize>)> {
        for (i, &(v, reason)) in self.decision_stack.iter().enumerate() {
            if v.abs() == lit.abs() {
                let dl = self.decision_stack[..=i].iter().filter(|&&(_, r)| r.is_none()).count() as u32;
                return Some((dl, reason));
            }
        }
        None  // literal not in decision stack
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