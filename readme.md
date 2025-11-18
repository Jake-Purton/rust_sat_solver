started out by implementing a dpll recursively

then you remove the copies by keeping track of chosen literals

then do vsids


input solver(s) sat: 61 avg. 0. unsat: 70 avg. 0. unknown: 0 killed: 0
"./opt3" sat: 61 avg. 0.2967 unsat: 68 avg. 1.3632 unknown: 2 killed: 0
"./opt3" better: 0 worse: 56 same: 75 inconsistencies: 0


input solver(s) sat: 61 avg. 0. unsat: 70 avg. 0. unknown: 0 killed: 0
"./watched_literals" sat: 61 avg. 0.3475 unsat: 68 avg. 1.3338 unknown: 2 killed: 0
"./watched_literals" better: 0 worse: 56 same: 75 inconsistencies: 0

input solver(s) sat: 61 avg. 0. unsat: 70 avg. 0. unknown: 0 killed: 0
"./opt4" sat: 61 avg. 0.4622 unsat: 69 avg. 1.4898 unknown: 1 killed: 0
"./opt4" better: 0 worse: 53 same: 78 inconsistencies: 0

input solver(s) sat: 61 avg. 0. unsat: 70 avg. 0. unknown: 0 killed: 0
"./opt5" sat: 61 avg. 0.3754 unsat: 70 avg. 1.5728 unknown: 0 killed: 0
"./opt5" better: 0 worse: 53 same: 78 inconsistencies: 0

input solver(s) sat: 61 avg. 0. unsat: 70 avg. 0. unknown: 0 killed: 0
"./opt6" sat: 61 avg. 0.2672 unsat: 68 avg. 1.197 unknown: 2 killed: 0
"./opt6" better: 0 worse: 53 same: 78 inconsistencies: 0



