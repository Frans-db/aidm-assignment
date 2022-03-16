include "globals.mzn";

int: w = 7;

% Loaded data
int: groups;
int: numShifts;
% Variable renaming
int: n = groups;
int: m = numShifts;

array[1..m, 1..w] of int: demand;
array[1..m] of int: minShift;
array[1..m] of int: maxShift;
int: minOff;
int: maxOff;
int: minOn;
int: maxOn;

% Variable renaming
array[1..m, 1..w] of int: R = demand;
array[1..m] of int: A = 1..m;
array[1..(m+1)] of int: A_plus = A ++ [0];

array[int] of set of int: forbidden;
array[int] of set of int: F = forbidden;
array[int, int] of set of int: forbidden3;

int: nw = groups * w;

% Variables o and T
var 0..(w-1): o;
array[1..nw] of var 0..numShifts: T;

% Creating variables
array[int] of int: ls = [minOff] ++ minShift;
array[int] of int: us = [maxOff] ++ maxShift;
int: lw = minOn;
int: uw = maxOn;

array[int] of int: W = 1..w;
array[int] of int: N = 1..n;
array[int] of int: NW = 1..(nw);


% (1) and (2)
constraint forall(d in W, s in A)
              (sum(i in 0..(n-1))(T[d + w*i mod nw] == s) == R[s, d+o mod w]);
constraint implied_constraint(
  forall(d in W)
      (sum(i in 0..(n-1))(T[d + w*i mod nw] == 0) == n - sum(i in 1..m)(R[i, d+o mod w]))
);

% (3) and (4)
constraint symmetry_breaking_constraint(T[1] != 0);
constraint symmetry_breaking_constraint(T[groups*w] != 0);

% (5)
constraint forall(s in A_plus, i in NW)((T[i] == s /\ T[i-1 mod nw] != s) -> forall(j in 1..(ls[s+1]-1))(T[i+j] == s));
% constraint forall(i in NW, s in A_plus, j in 1..(ls[s+1] - 1))((T[i mod nw] == s /\ T[i-1 mod nw] != s) -> T[i+j mod nw] == s);
% constraint forall(i in 1..(groups*w), s in 0..numShifts, j in 1..(ls[s+1]-1))((T[i mod nw] == s) /\ T[i-1 md w]);

% (6) 
% constraint forall(s in 0..numShifts, i in 1..(n*w), j in ls[s+1]..us[s+1])(((i+us[s+1]) > (groups*w)) \/ ((T[i+j] != s) /\ (T[i mod nw] == s) /\ (T[i-1 mod w] != s)));

% (6) (frans)
constraint forall(s in A_plus, i in NW)((T[i] == s /\ T[i-1 mod nw] != s) -> (i+us[s+1] > nw \/ exists(j in ls[s+1]..us[s+1])(T[i+j mod nw] == s)));

% (7)
constraint forall(i in NW)((T[i] != 0 /\ T[i-1 mod nw] == 0) -> forall(j in 1..(lw-1))(T[i+j mod nw] != 0));

% (9) bad!
% constraint forall(s in A, i in NW)(T[i] != s \/ forall(fs in F)(has_element(s, fs) /\ has_element(T[i+1], fs)));

solve satisfy;

output ["T = \(T)\n"];