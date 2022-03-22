include "globals.mzn";

int: w = 7;

% Loaded data
int: groups;
int: n = groups;
int: nw = n * w;

int: numShifts;
int: m = numShifts;
int: mn = m * n;


array[1..m, 1..w] of int: demand;
array[1..m, 1..w] of int: R = demand;

array[1..m] of int: minShift;
array[1..m] of int: maxShift;
int: minOff;
int: maxOff;
int: minOn;
int: maxOn;

array[int] of int: ls = [minOff] ++ minShift;
array[int] of int: us = [maxOff] ++ maxShift;
int: lw = minOn;
int: uw = maxOn;

array[1..m] of int: A = 1..m;
% array[1..(m+1)] of int: A_plus = A ++ [0];

array[int] of set of int: forbidden;
array[int] of set of int: F = forbidden;
array[int, 1..3] of int: forbidden3;

array[int] of int: W = 1..w;
array[int] of int: N = 1..n;
array[int] of int: NW = 1..nw;
array[int] of int: MN = 1..mn;


array[1..(m+1), 1..n, 1..w] of var bool: T;

% viewpoint 2:
% on which days does each employee do each task

% constraints from paper:
% 1. demand on each day is met
% 2. blocks meet minimum length requirement
% 3. blocks meet maximum length requirement
% 4. no forbidden sequences

% same as before. employee 1 starts day 1 working, employee n sends with a free day
% constraint symmetry_breaking_constraint(T[1] != 1);
% constraint symmetry_breaking_constraint(T[(m+1)*(n-1) + 1] == w);



% demand on each day is met
constraint forall(d in 1..w, s in 1..m)(
              sum(e in 1..n)
                (T[s+1, e, d]) = R[s, d]);

% on each day each employee only does 1 shift
constraint forall(d in 1..w, e in 1..n) 
              (sum(s in 1..(m+1))(T[s, e, d]) = 1);
                    
% symmetry breaking constraints, also avoids cyclicity
% employee 1 does not start with a free day
constraint symmetry_breaking_constraint(not T[1, 1, 1]);
% employee n ends with a free day
constraint symmetry_breaking_constraint(T[1, n, w]);

% ensure blocks meet minimum length requirement
constraint forall(s in 1..(m+1), i in 1..n*w)(
  [T[s, e, d] | e in 1..n, d in 1..w][i] /\ (i = 1 \/ (not [T[s, e, d] | e in 1..n, d in 1..w][i-1])) ->
  forall(j in 1..(ls[s]-1))
      ([T[s, e, d] | e in 1..n, d in 1..w][i+j])
);  

% ensure blocks meet maximum length requirement
% TODO: First part of the or block?
constraint forall(s in 1..(m+1), i in 1..n*w)(
  [T[s, e, d] | e in 1..n, d in 1..w][i] /\ (i = 1 \/ (not [T[s, e, d] | e in 1..n, d in 1..w][i-1])) ->
  (i + us[s] > n*w \/ exists(j in ls[s]..us[s]) (not [T[s, e, d] | e in 1..n, d in 1..w][i+j]))
);  

% forbidden within an employee
constraint forall(s in 2..(m+1), e in 1..n, d in 1..(w-1))(
  (not T[s, e, d]) \/ forall(f in F[s-1])(not T[f+1, e, d+1])
);


% forbidden between employees
constraint forall(s in 2..(m+1), e in 1..(n-1))(
  (not T[s, e, 7]) \/ forall(f in F[s-1])(not T[f, e+1, 1])
);

% forbidden between first and last employee
constraint forall(s in 2..(m+1))(
  (not T[s, n, 7]) \/ forall(f in F[s-1])(not T[f, 1, 1])
);

% forbidden 3 ???

var int: freeWeekends = sum(e in 1..n)(T[1, e, 6] /\ T[1, e, 7]);
solve maximize freeWeekends;

output ["Schedule = \(T)\n", "Free Weekends = \(freeWeekends)\n"];