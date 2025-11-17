use std::collections::{HashMap, HashSet};

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
    // watched[index of clause] = (lit1 lit2)
    pub watched: Vec<(usize, usize)>,
    // map the variable to the
    // clauses watching it
    pub watchers: HashMap<i32, Vec<usize>>,
    
    // track unit clauses with their units
    unit_clauses: HashMap<i32, Vec<usize>>,
    
    // VSIDS heuristic (boost variables that appear often in conflicts)
    vsids_scores: Vec<f64>,
    vsids_increment: f64,
    vsids_decay: f64,
    phase_saving: Vec<bool>,
}

enum UnitOrNot {
    Undecided,
    False,
    Unit(i32),
    True,
}

impl Cnf {
    pub fn new(clauses: Vec<Vec<i32>>) -> Self {
        let mut watched: Vec<(usize, usize)> = vec![(0, 1); clauses.len()];

        let mut largest = 0;

        for i in 0..clauses.len() {
            if clauses[i].len() == 1 {
                watched[i].1 = 0;
            }

            for &lit in &clauses[i] {
                if largest < lit.abs() {
                    largest = lit.abs();
                }
            }
        }

        // initialise watchers
        let mut watchers: HashMap<i32, Vec<usize>> = HashMap::new();
        for (ci, clause) in clauses.iter().enumerate() {
            if clause.len() == 1 {
                let lit = clause[0];
                watchers.entry(lit).or_default().push(ci);
            } else if clause.len() >= 2 {
                let lit1 = clause[0];
                let lit2 = clause[1];
                watchers.entry(lit1).or_default().push(ci);
                watchers.entry(lit2).or_default().push(ci);
            }
        }

        let num_vars = largest as usize;

        Self {
            clauses,

            model: vec![None; num_vars],

            decision_stack: Vec::new(),

            dl: 0,

            watched,

            watchers,

            unit_clauses: HashMap::new(),
            
            vsids_scores: vec![0.0; num_vars],
            vsids_increment: 1.0,
            vsids_decay: 0.95,
            phase_saving: vec![true; num_vars],
        }
    }

    #[inline]
    fn insert(&mut self, lit: i32) {
        let var = lit.unsigned_abs() as usize;

        if lit > 0 {
            self.model[var - 1] = Some(true);
            self.phase_saving[var - 1] = true;
        } else {
            self.model[var - 1] = Some(false);
            self.phase_saving[var - 1] = false;
        }
    }

    #[inline]
    fn is_true(&self, lit: i32) -> bool {
        let var = lit.unsigned_abs() as usize;
        match self.model[var - 1] {
            Some(val) => (lit > 0 && val) || (lit < 0 && !val),
            None => false,
        }
    }

    #[inline]
    fn is_false(&self, lit: i32) -> bool {
        let var = lit.unsigned_abs() as usize;
        match self.model[var - 1] {
            Some(val) => (lit > 0 && !val) || (lit < 0 && val),
            None => false,
        }
    }

    #[inline]
    fn contains(&self, lit: i32) -> bool {
        let var = lit.unsigned_abs() as usize;
        self.model[var - 1].is_some()
    }

    fn eval_watched(&mut self, index: usize) -> UnitOrNot {
        // optimise later

        if self.watched[index].0 == self.watched[index].1 {
            if self.is_false(self.clauses[index][self.watched[index].0]) {
                return UnitOrNot::False;
            } else if self.is_true(self.clauses[index][self.watched[index].0]) {
                return UnitOrNot::True;
            } else {
                return UnitOrNot::Unit(self.clauses[index][self.watched[index].0]);
            }
        }

        let mut ended_at = 0;
        
        // if a variable is false, you must find another
        if self.is_false(self.clauses[index][self.watched[index].0]) {
            let mut found_replacement = false;
            let old_lit = self.clauses[index][self.watched[index].0];

            for i in 0..self.clauses[index].len() {
                if i == self.watched[index].0 || i == self.watched[index].1 {
                    continue;
                }

                if !self.is_false(self.clauses[index][i]) {
                    let new_lit = self.clauses[index][i];

                    // update watchers
                    if let Some(list) = self.watchers.get_mut(&old_lit) {
                        list.retain(|&ci| ci != index);
                        if list.is_empty() {
                            self.watchers.remove(&old_lit);
                        }
                    }
                    self.watchers.entry(new_lit).or_default().push(index);

                    self.watched[index].0 = i;
                    found_replacement = true;

                    ended_at = i;

                    // keep it and break
                    break;
                }
            }

            if found_replacement {
                return UnitOrNot::Undecided;
            }
        }

        // and again for the second literal
        if self.is_false(self.clauses[index][self.watched[index].1]) {
            let old_lit = self.clauses[index][self.watched[index].1];
            let mut found_replacement = false;

            for i in ended_at..self.clauses[index].len() {
                if i == self.watched[index].0 || i == self.watched[index].1 {
                    continue;
                }

                if !self.is_false(self.clauses[index][i]) {
                    let new_lit = self.clauses[index][i];

                    // update watchers
                    if let Some(list) = self.watchers.get_mut(&old_lit) {
                        list.retain(|&ci| ci != index);
                        if list.is_empty() {
                            self.watchers.remove(&old_lit);
                        }
                    }
                    self.watchers.entry(new_lit).or_default().push(index);

                    self.watched[index].1 = i;
                    found_replacement = true;

                    // keep it and break
                    break;
                }
            }

            if found_replacement {
                return UnitOrNot::Undecided;
            }
        }

        // if both are still false then unsat
        if self.is_false(self.clauses[index][self.watched[index].0])
            && self.is_false(self.clauses[index][self.watched[index].1])
        {
            return UnitOrNot::False;
        } else if self.is_true(self.clauses[index][self.watched[index].0])
            || self.is_true(self.clauses[index][self.watched[index].1])
        {
            return UnitOrNot::True;
        } else if self.is_false(self.clauses[index][self.watched[index].0]) {
            return UnitOrNot::Unit(self.clauses[index][self.watched[index].1]);
        } else if self.is_false(self.clauses[index][self.watched[index].1]) {
            return UnitOrNot::Unit(self.clauses[index][self.watched[index].0]);
        }

        // undecided but not unit
        UnitOrNot::Undecided
    }

    // return none if no conflict else the conflicting clause
    fn unit_prop_watched(&mut self) -> Option<usize> {
        // Use a work queue to track literals that have been assigned and need propagation
        let mut propagation_queue: Vec<i32> = Vec::new();

        // Use unit_clauses HashMap to track current unit clauses in this propagation
        self.unit_clauses.clear();

        // Initial scan: find all current unit clauses
        for index in 0..self.clauses.len() {
            match self.eval_watched(index) {
                UnitOrNot::True => continue,
                UnitOrNot::False => return Some(index),
                UnitOrNot::Undecided => continue,
                UnitOrNot::Unit(unit) => {
                    self.unit_clauses.entry(unit).or_default().push(index);
                }
            }
        }

        // Process all units from the unit_clauses HashMap
        // Take ownership using std::mem::take to avoid the clone
        let unit_map = std::mem::take(&mut self.unit_clauses);
        for (unit_lit, clause_indices) in unit_map {
            // Pick the first clause for this unit (arbitrary but valid)
            if let Some(&clause_idx) = clause_indices.first() {
                if !self.contains(unit_lit) {
                    self.insert(unit_lit);
                    self.decision_stack.push((unit_lit, Some(clause_idx)));
                    propagation_queue.push(unit_lit);
                }
            }
        }

        // Propagate assignments using the watchers HashMap
        while let Some(assigned_lit) = propagation_queue.pop() {
            let neg_lit = -assigned_lit;

            // Get clauses watching the negation of the assigned literal
            // We need to clone to avoid holding a reference during eval_watched
            let watching_clauses: Vec<usize> = match self.watchers.get(&neg_lit) {
                Some(clauses) => clauses.clone(),
                None => continue, // No clauses watching this literal
            };

            for &clause_idx in &watching_clauses {
                match self.eval_watched(clause_idx) {
                    UnitOrNot::True => continue,
                    UnitOrNot::False => return Some(clause_idx),
                    UnitOrNot::Undecided => continue,
                    UnitOrNot::Unit(unit) => {
                        if !self.contains(unit) {
                            self.insert(unit);
                            self.decision_stack.push((unit, Some(clause_idx)));
                            propagation_queue.push(unit);
                        }
                    }
                }
            }
        }

        None
    }

    pub fn choose_unassigned_literal(&self) -> Option<i32> {
        // Use VSIDS heuristic to choose the variable with highest activity
        let mut best_var = None;
        let mut best_score = -1.0;
        
        for var in 1..=self.vsids_scores.len() {
            let var_i32 = var as i32;
            if !self.contains(var_i32) {
                let idx = var - 1;
                if self.vsids_scores[idx] > best_score {
                    best_score = self.vsids_scores[idx];
                    best_var = Some(var_i32);
                }
            }
        }
        
        if let Some(var) = best_var {
            // Use phase saving for polarity
            let idx = (var - 1) as usize;
            let polarity = self.phase_saving[idx];
            return Some(if polarity { var } else { -var });
        }
        
        None
    }

    // VSIDS helper functions
    fn bump_vsids(&mut self, var: i32) {
        let idx = (var.abs() - 1) as usize;
        if idx < self.vsids_scores.len() {
            self.vsids_scores[idx] += self.vsids_increment;
            
            // Rescale if scores get too large
            if self.vsids_scores[idx] > 1e100 {
                self.rescale_vsids();
            }
        }
    }

    fn decay_vsids(&mut self) {
        self.vsids_increment /= self.vsids_decay;
    }

    fn rescale_vsids(&mut self) {
        for score in &mut self.vsids_scores {
            *score *= 1e-100;
        }
        self.vsids_increment *= 1e-100;
    }

    fn backjump(&mut self, dl: u32) {
        while dl < self.dl {
            if let Some((lit, reason)) = self.decision_stack.pop() {
                self.model[lit.unsigned_abs() as usize - 1] = None;
                if reason.is_none() {
                    self.dl -= 1;
                }
            }
        }
    }

    pub fn solve_cdcl(&mut self) -> bool {
        // self.clean();
        if self.unit_prop_watched().is_some() {
            return false;
        }

        loop {
            // backtracking

            while let Some(ci) = self.unit_prop_watched() {
                if self.dl == 0 {
                    return false;
                }

                let (learned_clause, dl) = self.analyse_conflict(ci);
                
                // Bump VSIDS scores for variables in learned clause
                self.bump_learned_clause(&learned_clause);

                self.backjump(dl);

                // Add the learned clause
                let new_ci = self.clauses.len();
                self.clauses.push(learned_clause.clone());

                // Add watch variables for the learned clause
                if learned_clause.len() == 1 {
                    self.watched.push((0, 0));
                    let lit = learned_clause[0];
                    self.watchers.entry(lit).or_default().push(new_ci);
                } else {
                    self.watched.push((0, 1));
                    let lit1 = learned_clause[0];
                    let lit2 = learned_clause[1];
                    self.watchers.entry(lit1).or_default().push(new_ci);
                    self.watchers.entry(lit2).or_default().push(new_ci);
                }

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

    fn analyse_conflict(&self, conflict_index: usize) -> (Vec<i32>, u32) {
        let mut conflict = self.clauses[conflict_index].clone();

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
                        if lit.abs() != v
                            && inserted.insert(lit) {
                                new_conflict.push(lit);
                            }
                    }

                    // add reason literals (except var v), avoid duplicates
                    for &lit in reason_clause {
                        if lit.abs() != v
                            && inserted.insert(lit) {
                                new_conflict.push(lit);
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
    
    fn bump_learned_clause(&mut self, clause: &[i32]) {
        // Bump activity for all variables in the learned clause
        for &lit in clause {
            self.bump_vsids(lit.abs());
        }
        
        // Decay all activities
        self.decay_vsids();
    }

    fn decision_level(&self, lit: i32) -> Option<(u32, Option<usize>)> {
        for (i, &(v, reason)) in self.decision_stack.iter().enumerate() {
            if v.abs() == lit.abs() {
                let dl = self.decision_stack[..=i]
                    .iter()
                    .filter(|&&(_, r)| r.is_none())
                    .count() as u32;
                return Some((dl, reason));
            }
        }
        None // literal not in decision stack
    }

    fn all_clauses_solved(&self) -> bool {
        // for all clauses
        self.clauses.iter().all(|clause| {
            // any var must be true
            clause.iter().any(|&lit| self.is_true(lit))
        })
    }
}