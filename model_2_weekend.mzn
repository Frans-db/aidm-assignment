% Frans de Boer ()
% Adarsh Denga ()
% all code in this file is the same as in the file model_2.mzn thus no comments will be added here to avoid duplication
% the final parts (maximizing the objective) is new and is commented in this file
int: w = 7;
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
array[int] of set of int: forbidden;
array[int] of set of int: F = forbidden;
array[int, 1..3] of int: forbidden3;
array[int] of int: W = 1..w;
array[int] of int: N = 1..n;
array[int] of int: NW = 1..nw;
array[int] of int: MN = 1..mn;

array[1..(m+1), 1..n, 1..w] of var bool: T;

constraint forall(d in 1..w, s in 1..m)(
              sum(e in 1..n)
                (T[s+1, e, d]) = R[s, d]);

constraint forall(d in 1..w, e in 1..n) 
              (sum(s in 1..(m+1))(T[s, e, d]) = 1);
                    
constraint symmetry_breaking_constraint( not T[1, 1, 1] );
constraint symmetry_breaking_constraint( T[1, n, w] );

constraint forall(s in 1..(m+1), i in 1..n*w)(
  [T[s, e, d] | e in 1..n, d in 1..w][i] /\ (i = 1 \/ (not [T[s, e, d] | e in 1..n, d in 1..w][i-1])) ->
  forall(j in 1..(ls[s]-1))
      ([T[s, e, d] | e in 1..n, d in 1..w][i+j])
);  

constraint forall(s in 1..(m+1), i in 1..n*w)(
  [T[s, e, d] | e in 1..n, d in 1..w][i] /\ (i = 1 \/ (not [T[s, e, d] | e in 1..n, d in 1..w][i-1])) ->
  (i + us[s] > n*w \/ exists(j in ls[s]..us[s]) (not [T[s, e, d] | e in 1..n, d in 1..w][i+j]))
);  

constraint forall(i in 1..n*w)(
  (not [T[1, e, d] | e in 1..n, d in 1..w][i]) /\ (i = 1 \/ ([T[1, e, d] | e in 1..n, d in 1..w][i-1])) ->
  forall(j in 1..(lw-1))
      (not [T[1, e, d] | e in 1..n, d in 1..w][i+j])
);  

constraint forall(i in 1..n*w)(
  (not [T[1, e, d] | e in 1..n, d in 1..w][i]) /\ (i = 1 \/ ([T[1, e, d] | e in 1..n, d in 1..w][i-1])) ->
  (i + uw > n*w \/ exists(j in lw..uw) ([T[1, e, d] | e in 1..n, d in 1..w][i+j]))
);  

constraint forall(s in 2..(m+1), e in 1..n, d in 1..(w-1))(
  (not T[s, e, d]) \/ forall(f in F[s-1])(not T[f+1, e, d+1])
);

constraint forall(s in 2..(m+1), e in 1..(n-1))(
  (not T[s, e, 7]) \/ forall(f in F[s-1])(not T[f+1, e+1, 1])
);

constraint forall(s in 2..(m+1))(
  (not T[s, n, 7]) \/ forall(f in F[s-1])(not T[f+1, 1, 1])
);

constraint forall(x in 1..round((length(forbidden3) / 3)), e in 1..n, d in 1..(w-2))
            (exists(j in 0..2)
              (not T[forbidden3[x,j+1]+1, e, d+j]));

constraint forall(x in 1..round((length(forbidden3) / 3)), e in 1..(n-1))
            (((not T[forbidden3[x, 1]+1, e, 6]) \/ (not T[forbidden3[x, 2]+1, e, 7]) \/ (not T[forbidden3[x, 3]+1, e+1, 1])) /\
            ((not T[forbidden3[x, 1]+1, e, 7]) \/ (not T[forbidden3[x, 2]+1, e+1, 1]) \/ (not T[forbidden3[x, 3]+1, e+1, 2])));

constraint forall(x in 1..round((length(forbidden3) / 3)))
           (((not T[forbidden3[x, 1]+1, n, 6]) \/ (not T[forbidden3[x, 2]+1, n, 7]) \/ (not T[forbidden3[x, 3]+1, 1, 1])) /\
           ((not T[forbidden3[x, 1]+1, n, 7]) \/ (not T[forbidden3[x, 2]+1, 1, 1]) \/ (not T[forbidden3[x, 3]+1, 1, 2])));         

% formatted is the expected format of the outpout
array[1..n*w] of var 0..m: formatted;
% each employee shifts the index in the expected format by w. the day is then added to get to the correct index
constraint forall(s in 1..m+1, e in 1..n, d in 1..w)(T[s, e, d] -> formatted[(e-1)*w + d] = s-1);

% calculate the number of free weekends as the number of times
% shift 0 is true for an employee on both day 6 and 7
var int: freeWeekends = sum(e in 1..n)(T[1, e, 6] /\ T[1, e, 7]);
solve maximize freeWeekends;

output [join(", ", fix([if formatted[i] = 0 then "-" else show(formatted[i]) endif | i in 1..nw]))];
output ["\n", show(freeWeekends)];