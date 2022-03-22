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
array[1..(m+1)] of int: A_plus = A ++ [0];

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
constraint forall(d in W, s in A)(
              sum(i in N)
                (T[s+1, i, d]) = R[s, d]);
                
% symmetry breaking constraints, also avoids cyclicity
% employee 1 does not start with a free day
constraint symmetry_breaking_constraint(not T[1, 1, 1]);
% employee n ends with a free day
constraint symmetry_breaking_constraint(not T[1, n, w]);
% constraint forall(d in W, s in A)
%               (sum(i in 0..(n-1))(T[d + w*i] == s) == R[s, d+o]);
% constraint implied_constraint( forall(d in W)
%               (sum(i in 0..(n-1))(T[d + w*i] == 0) == n - sum(i in 1..m)(R[i, d+o])) );        

% (3) and (4)
% constraint symmetry_breaking_constraint(T[1] != 0);
% constraint symmetry_breaking_constraint(T[nw] == 0);



% (5)
% constraint forall(s in A_plus)(true);
% constraint forall(s in A_plus, i in NW)
%               ((T[i] == s /\ (T[i-1] != s \/ i == 1)) -> 
%                   forall(j in 1..(ls[s+1]-1))
%                       (T[i+j] == s));

% (6) 
% constraint forall(s in A_plus, i in NW)
%               ((T[i] == s /\ (T[i-1] != s \/ i == 1)) -> 
%                   i + us[s+1] > nw \/ exists(j in ls[s+1]..us[s+1])(T[i+j] != s));

% (7)
% constraint implied_constraint( forall(i in NW)
%               ((T[i] != 0 /\ (T[i-1] == 0 \/ i == 1)) -> 
%                   forall(j in 1..(lw-1))
%                       (T[i+j] != 0)) );

% (8)
% constraint implied_constraint( forall(i in NW)
%               ((T[i] != 0 /\ (T[i-1] == 0 \/ i == 1)) -> 
%                   i + uw > nw \/ exists(j in lw..uw)(T[i+j] == 0)) );

% % (9)
% constraint forall(s in A, i in NW)(T[i] != s \/ not (T[i+1] in F[s]));

% % (10)
% constraint forall(x in 1..round((length(forbidden3) / 3)), i in NW)
%               (exists(j in 1..3)(forbidden3[x, j] != T[(i + j - 1) mod (nw+1)]));


% (12)
% constraint symmetry_breaking_constraint(
%   forall(s in A, d in W)(R[s,d] == R[s,d+1]) -> o == 0
% );

% var int: freeWeekends = sum(i in 1..n)(T[(w*i - o - 1)] == 0 /\ T[(w*i - 0)] == 0);
solve satisfy;

output ["Schedule = \(T)\n"];