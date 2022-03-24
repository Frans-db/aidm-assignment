% an implementation of the paper
% Lucas Kletzander et al. 
% “Exact methods for extended rotating workforce scheduling problems”. 
% In: Proceedings of the International Conference on Automated Planning and Scheduling. Vol. 29. 2019, pp. 519–527

% implemented by
% Frans de Boer ()
% Adarsh Denga ()

% Number of days in the schedule, usually 7 (1 week long schedules)
int: w = 7;

% number of groups (employees) in the problem
int: groups;
% number of shifts in the problem
int: numShifts;

% we create variables n for groups, and m for shifts to match the naming in the paper
int: n = groups;
int: m = numShifts;

% length of the schedule
int: nw = n * w;

% demand[s, d] = the demand for shift s on day d
array[1..m, 1..w] of int: demand;
% variable R as a substitute for demand to match the naming used in the paper
array[1..m, 1..w] of int: R = demand;

% minShift[s] = the minimum number of times this shift has to be worked in a row in a valid schedule
array[1..m] of int: minShift;
% maxShift[s] = the maximum number of times this shift has to be worked in a row in a valid schedule
array[1..m] of int: maxShift;
% the minimum number of days off in a row in a valid schedule
int: minOff;
% the maximum number of days off in a row in a valid schedule
int: maxOff;
% the minimum number of days of work (on any shift) in a row in a valid schedule
int: minOn;
% the maximum number of days of work (on any shift) in a row in a valid schedule
int: maxOn;

% ls and us variable to match description of ls in the paper:
% ls[s] = the minimum number of times this shift (including the 0 shift) has to be worked in a row in a valid schedule
array[int] of int: ls = [minOff] ++ minShift;
% us[s] = the maximum number of times this shift (including the 0 shift) has to be worked in a row in a valid schedule
array[int] of int: us = [maxOff] ++ maxShift;
% variable lw and uw as a substitute for minOn and maxOn to match the naming used in the paper
int: lw = minOn;
int: uw = maxOn;

% A and A_plus were created to match the constraints more accurately to the constraints in the paper
% list of shifts, excluding the 0 shift
array[1..m] of int: A = 1..m;
% list of shifts, including the 0 shift
% array[1..(m+1)] of int: A_plus = [0] ++ A;

% forbidden[s] = set of shifts that are not allowed to come after shift s
array[int] of set of int: forbidden;
% variable F as  a substitute for forbidden to match the naming used in the paper
array[int] of set of int: F = forbidden;
% forbidden3 is a list containing lists of length 3 in which each element is a shift. 
% the length 3 lists indicate a sequence of shifts that is not allowed in a valid schedule
array[int, 1..3] of int: forbidden3;

% list creation to make iteration easer (i in NW), and to match the constraints closer to the constraints in the paper
array[int] of int: W = 1..w;
array[int] of int: N = 1..n;
array[int] of int: NW = 1..nw;

% offset variable. used to shift the entire schedule
var 0..(w-1): o;
% schedule variable. T[i] = s, with s in A_plus. T[i] indicates which shift is done on day i+o
array[1..nw] of var 0..numShifts: T;

% viewpoint of this model:
% for each combination of day and employee, which task is assigned to it?

% modulo functions. used to get the correct index in any of the arrays
function 0..nw: modulo_nw(int: a) = if a <= 0 then a + nw else if a <= nw then a else 1 + (a mod (nw+1)) endif endif;
function var 0..m: modulo_m(int: a) = if a <= 0 then (a + m) else if a <= m then a else 1 + (a mod (m+1)) endif endif;
function var 0..w: modulo_w(int: a) = if a <= 0 then (a + w) else if a <= w then a else 1 + (a mod (w+1)) endif endif;
function var 0..w: modulo_w_var(var int: a) = if a <= 0 then (a + w) else if a <= w then a else 1 + (a mod (w+1)) endif endif;

% (1)
% ensure that the demand on each day is met.
% T[d + w*i] iterates over every w-th element and adds this to the total sum when the shift on this day is equal to s
% the total number of shifts s, done on day d (in any period w) has to then equal the demand of shift s on day d+o, 
% where the o allows our shifts to be offset by the value o
constraint forall(d in W, s in A)
              (sum(i in 0..(n-1))(T[modulo_nw(d + w*i)] == s) == R[modulo_m(s), modulo_w_var(d+o)]);
              
% (2)
% a second way to ensure the demand on each day is met.
% we expect that on a given day the number of employees who have the day off is equal to the number of employees,
% minus the number of employees working any shift that day
% this constraint counts the number of employees with day off (once again using T[d + w*i] to count day d in any time period)
% and then restricts this to be equal to the number of employees - the total demand
constraint implied_constraint( forall(d in W)
              (sum(i in 0..(n-1))(T[modulo_nw(d + w*i)] == 0) == n - sum(i in 1..m)(R[modulo_m(i), modulo_w_var(d+o)])) );        

% next 2 constraints break symmetries, and break some of the cyclicity in the schedule
% (3)
constraint symmetry_breaking_constraint(T[1] != 0);
% (4)
constraint symmetry_breaking_constraint(T[nw] == 0);
  

% (5)
% ensures the miminum number of shifts s are worked in a row
% only checks for the minimum length requirement when a new block just started
% 0 0 1 1 1 1 1
%     ^ starts checking here

% we made a slight modification to this constraint:
% the constraint would fail for i=1, because then T[1-11] = T[0] would give an index out of bounds error.
% to cirumvent this we check either T[i-1] != s OR i = 1, to make sure that the first element is also checked
% for the minimum length requirement
% this modification is added in the next 4 constraints
constraint forall(s in 0..m, i in NW)
              ((T[i] == s /\ (i = 1 \/ T[i-1] != s)) -> 
                  forall(j in 1..(ls[s+1]-1))
                      (T[modulo_nw(i+j)] == s));

% (6) 
% ensures that no more than the maximum number of shifts s are worked in a row
% only checks for the maximum length requirement when a new block just started
% for the sequence to be shorter than the maximum length any shift in the range
% us[s] (minimum length) and ls[s] (maximum length) has to be not equal to s
constraint forall(s in 0..m, i in NW)
              ((T[i] == s /\ (i = 1 \/ T[i-1] != s)) -> 
                  i + us[s+1] > nw \/ exists(j in ls[s+1]..us[s+1])(T[modulo_nw(i+j)] != s));

% (7)
% ensures the miminum number of shifts (for any s) are worked in a row
% in this case we can check that the sequence length is long enough by ensuring 
% there is no 0 shift in the range i, i+lw (mimimum sequence length)
constraint forall(i in NW)
              ((T[i] != 0 /\ (i = 1 \/ T[i-1] = 0)) -> 
                  forall(j in 1..(lw-1))
                      (T[modulo_nw(i+j)] != 0));

% (8)
% ensures that no more than the miminum number of shifts (for any s) are worked in a row
% this is checked by ensuring at least 1 shift in the range lw (minimum sequence length) 
% and uw (maximum sequence length) is equal to the 0 shift
constraint forall(i in NW)
              ((T[i] != 0 /\ (i = 1 \/ T[i-1] = 0)) -> 
                  i + uw > nw \/ exists(j in lw..uw)(T[modulo_nw(i+j)] == 0));

% (9)
% ensures no forbidden sequences (of length 2) exist in the schedule
% either the current shift is not equal to s, or the next shift is not equal to a shift
% that is not allowed to come after s (andy s_2 in F[s])
constraint forall(s in A, i in NW)(T[modulo_nw(i)] != s \/ not (T[modulo_nw(i+1)] in F[s]));

% (10)
% ensures no forbidden sequences (of length 3) exist in the schedule
% any block of shifts of length 3 in the schedule must have at least 1 shift that does
% not match with the sequence of forbidden shifts (this must hold true for every
% sequence of forbidden shifts)
constraint forall(x in 1..round((length(forbidden3) / 3)), i in NW)
              (exists(j in 1..3)(forbidden3[x, j] != T[modulo_nw(i + j - 1)]));


% (12)
% constraint copied from paper, binds o to 0 in some cases
constraint symmetry_breaking_constraint(
  forall(s in A, d in W)(R[modulo_m(s),modulo_w(d)] == R[modulo_m(s),modulo_w(d+1)]) -> o == 0
);

solve satisfy;


% array[1..nw] of string: out = [if x = 0 then "-" else show(x) endif | x in T];
output [show(o), "\n"];
output [join(", ", [if x = 0 then "-" else show(x) endif | x in fix(T)])];
% output [if x = 0 then "-" else show(x) endif  ++ ", " | x in fix(T)];