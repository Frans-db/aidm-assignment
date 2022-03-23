include "globals.mzn";

int: w = 7;

% Loaded data
int: groups;
int: n = groups;
int: nw = n * w;

int: numShifts;
int: m = numShifts;

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

% VARIABLES FOR BLOCK BOUNDING
% r is the total demand for work shifts
int: r = sum(i in 1..m, j in 1..w) (R[i,j]);
% loww and upw definw lower and upper bounds for the number of work blocks
int: loww = ceil(r / uw);
int: upw = floor(r / lw);
% lowo and upo define the lower and upper bounds for the number of free blocks
int: lowo = ceil((nw - r) / maxOff);
int: upo = floor((nw - r) / maxOn);
% low and up define common bounds
int: low = max(loww, lowo);
int: up = min(upw, upo);

var 0..(w-1): o;
array[1..nw] of var 0..numShifts: T;

% viewpoint 1:
% for each day, which task is assigned to it

% (1) and (2)
constraint forall(d in W, s in A)
              (sum(i in 0..(n-1))(T[d + w*i] == s) == R[s, d+o]);
constraint implied_constraint( forall(d in W)
              (sum(i in 0..(n-1))(T[d + w*i] == 0) == n - sum(i in 1..m)(R[i, d+o])) );        

% (3) and (4)
constraint symmetry_breaking_constraint(T[1] != 0);
constraint symmetry_breaking_constraint(T[nw] == 0);

% custom
% constraint symmetry_breaking_constraint(
%   exists(s in A)(R[s, 1] > 0 /\ forall(j in 1..(ls[s]))(T[j] == s))
% );


% (5)
constraint forall(s in A_plus, i in NW)
              ((T[i] == s /\ (T[i-1] != s \/ i == 1)) -> 
                  forall(j in 1..(ls[s+1]-1))
                      (T[i+j] == s));

% (6) 
constraint forall(s in A_plus, i in NW)
              ((T[i] == s /\ (T[i-1] != s \/ i == 1)) -> 
                  i + us[s+1] > nw \/ exists(j in ls[s+1]..us[s+1])(T[i+j] != s));

% (7)
constraint implied_constraint( forall(i in NW)
              ((T[i] != 0 /\ (T[i-1] == 0 \/ i == 1)) -> 
                  forall(j in 1..(lw-1))
                      (T[i+j] != 0)) );

% (8)
constraint implied_constraint( forall(i in NW)
              ((T[i] != 0 /\ (T[i-1] == 0 \/ i == 1)) -> 
                  i + uw > nw \/ exists(j in lw..uw)(T[i+j] == 0)) );

% (9)
constraint forall(s in A, i in NW)(T[i] != s \/ not (T[i+1] in F[s]));

% (10)
constraint forall(x in 1..round((length(forbidden3) / 3)), i in NW)
              (exists(j in 1..3)(forbidden3[x, j] != T[(i + j - 1) mod (nw+1)]));

% (12)
constraint symmetry_breaking_constraint(
  forall(s in A, d in W)(R[s,d] == R[s,d+1]) -> o == 0
);

% --------------------------------------------------------------------------------------------

% *EXTENSIONS*

% **DETECTING INFEASIBLE ISNTANCES**

% ***INFEASIBLE WEEKLY FLUCTUATION***
% (13)
constraint forall(s in A, i in W)(
  forall(j in ((us[s + 1] + 1)..(2*ls[s + 1] + 1)), k in (j - ls[s + 1])..(ls[s + 1] - 1)) 
    (R[s, i+k] >= R[s, i] + R[s, i+j-1] - R[s, i+j])
);

% ***BOUNDING THE NUMBER OF BLOCKS***
% (15)
constraint low <= up;

solve satisfy;

output ["Schedule = \(T)\n"];