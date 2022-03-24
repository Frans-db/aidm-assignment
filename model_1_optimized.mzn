% an implementation of the paper
% Lucas Kletzander et al. 
% “Exact methods for extended rotating workforce scheduling problems”. 
% In: Proceedings of the International Conference on Automated Planning and Scheduling. Vol. 29. 2019, pp. 519–527

% implemented by
% Frans de Boer ()
% Adarsh Denga ()
% all code in this file is the same as in the file model_1.mzn thus no comments will be added here to avoid duplication
% any new/optimized parts will be commented

int: w = 7;

int: groups;
int: numShifts;
int: n = groups;
int: m = numShifts;
int: nw = n * w;
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
array[int] of set of int: forbidden;
array[int] of set of int: F = forbidden;
array[int, 1..3] of int: forbidden3;
array[int] of int: W = 1..w;
array[int] of int: N = 1..n;
array[int] of int: NW = 1..nw;
var 0..(w-1): o;
array[1..nw] of var 0..numShifts: T;

function 0..nw: modulo_nw(int: a) = if a <= 0 then a + nw else if a <= nw then a else 1 + (a mod (nw+1)) endif endif;
function 0..m: modulo_m(int: a) = if a <= 0 then (a + m) else if a <= m then a else 1 + (a mod (m+1)) endif endif;
function 0..w: modulo_w(int: a) = if a <= 0 then (a + w) else if a <= w then a else 1 + (a mod (w+1)) endif endif;
function var 0..w: modulo_w_var(var int: a) = if a <= 0 then (a + w) else if a <= w then a else 1 + (a mod (w+1)) endif endif;

constraint forall(d in W, s in A)
              (sum(i in 0..(n-1))(T[modulo_nw(d + w*i)] == s) == R[modulo_m(s), modulo_w_var(d+o)]);
              
constraint implied_constraint( forall(d in W)
              (sum(i in 0..(n-1))(T[modulo_nw(d + w*i)] == 0) == n - sum(i in 1..m)(R[modulo_m(i), modulo_w_var(d+o)])) );        

constraint symmetry_breaking_constraint(T[1] != 0);
constraint symmetry_breaking_constraint(T[nw] == 0);
  
constraint forall(s in 0..m, i in NW)
              ((T[i] == s /\ (i = 1 \/ T[i-1] != s)) -> 
                  forall(j in 1..(ls[s+1]-1))
                      (T[modulo_nw(i+j)] == s));

constraint forall(s in 0..m, i in NW)
              ((T[i] == s /\ (i = 1 \/ T[i-1] != s)) -> 
                  i + us[s+1] > nw \/ exists(j in ls[s+1]..us[s+1])(T[modulo_nw(i+j)] != s));

constraint forall(i in NW)
              ((T[i] != 0 /\ (i = 1 \/ T[i-1] = 0)) -> 
                  forall(j in 1..(lw-1))
                      (T[modulo_nw(i+j)] != 0));

constraint forall(i in NW)
              ((T[i] != 0 /\ (i = 1 \/ T[i-1] = 0)) -> 
                  i + uw > nw \/ exists(j in lw..uw)(T[modulo_nw(i+j)] == 0));

constraint forall(s in A, i in NW)(T[modulo_nw(i)] != s \/ not (T[modulo_nw(i+1)] in F[s]));

constraint forall(x in 1..round((length(forbidden3) / 3)), i in NW)
              (exists(j in 1..3)(forbidden3[x, j] != T[modulo_nw(i + j - 1)]));

constraint symmetry_breaking_constraint(
  forall(s in A, d in W)(R[modulo_m(s),modulo_w(d)] == R[modulo_m(s),modulo_w(d+1)]) -> o == 0
);

solve :: int_search(T, first_fail, indomain_min) satisfy;

output [show(o), "\n"];
output [join(", ", [if x = 0 then "-" else show(x) endif | x in fix(T)])];