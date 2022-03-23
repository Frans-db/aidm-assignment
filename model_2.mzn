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

array[int] of set of int: forbidden;
array[int] of set of int: F = forbidden;
array[int, 1..3] of int: forbidden3;

array[int] of int: W = 1..w;
array[int] of int: N = 1..n;
array[int] of int: NW = 1..nw;
array[int] of int: MN = 1..mn;

% the above code is exactly equal to the code in basic_model.mzn. to avoid duplication
% please refer to the explanations in that file


% schedule variable
% we decided to work from the viewpoint of the combination of a shift and an employee
% each s in 1..(m+1), e in 1..n has a list of boolean values (d in 1..w), which indicates
% on which day of the week the employee does a shift

% note: while writing this we realised instead of an array of boolean values it would have 
% been much more efficient to use a single integer in the range 1..w, this could be a good
% optimisation to implement later
array[1..(m+1), 1..n, 1..w] of var bool: T;

% viewpoint of this model:
% for each combination of shift and employee, on which day does the employee do the shift?
% due to the change in viewpoint constraints could not be directly copied from the paper,
% but the general idea for most constraints is still the same



% ensure that the demand on each day is met.
% same functionality as constraint 1 from the paper
constraint forall(d in 1..w, s in 1..m)(
              sum(e in 1..n)
                (T[s+1, e, d]) = R[s, d]);

% on any day an employee can only do 1 shift, so every T[s, e, d] can only be true for 1 s in 1..(m+1)
% this is achieved by summing over each shift an employee could do on a day, and restricting this to be equal to 1
constraint forall(d in 1..w, e in 1..n) 
              (sum(s in 1..(m+1))(T[s, e, d]) = 1);
                    
% same as in basic model?
% same functionality as constraint 3 in the paper
constraint not T[1, 1, 1];
% same functionality as constraint 4 in the paper
constraint T[1, n, w];

% the following 4 constraints make use of the following:
% the schedule is cyclic, so when the week ends from employee e, they start the next
% week on the shift of employee e+1 (and employee n starts on the shift of employee 1).
% this means that we can combine the schedules of each employee for a given shift to create 
% 1 long sequence for that shift, and check in this if the minimum and maximum length requirements are met
% example:
% F F F F T T T
% T T T F F F F
% =>
% F F F F T T T T T T F F F F
% the code [T[s, e, d] | e in 1..n, d in 1..w] achieves this functionality. A problem we ran into was being 
% unable to store this list in a variable for reuse, so the statement is called a total of 12 times in the following
% 4 constraints. an optimisation could be to make a lookup table beforehand and use this in all constraints

% same functionality as constraint 5 in the paper
constraint forall(s in 1..(m+1), i in 1..n*w)(
  [T[s, e, d] | e in 1..n, d in 1..w][i] /\ (i = 1 \/ (not [T[s, e, d] | e in 1..n, d in 1..w][i-1])) ->
  forall(j in 1..(ls[s]-1))
      ([T[s, e, d] | e in 1..n, d in 1..w][i+j])
);  

% ensure shift blocks meet maximum length requirement
% same functionality as constraint 6 in the paper
constraint forall(s in 1..(m+1), i in 1..n*w)(
  [T[s, e, d] | e in 1..n, d in 1..w][i] /\ (i = 1 \/ (not [T[s, e, d] | e in 1..n, d in 1..w][i-1])) ->
  (i + us[s] > n*w \/ exists(j in ls[s]..us[s]) (not [T[s, e, d] | e in 1..n, d in 1..w][i+j]))
);  

% ensure blocks meet minimum length requirement
% same functionality as constraint 7 in the paper
constraint forall(i in 1..n*w)(
  (not [T[1, e, d] | e in 1..n, d in 1..w][i]) /\ (i = 1 \/ ([T[1, e, d] | e in 1..n, d in 1..w][i-1])) ->
  forall(j in 1..(lw-1))
      (not [T[1, e, d] | e in 1..n, d in 1..w][i+j])
);  

% ensure blocks meet maximum length requirement
% same functionality as constraint 8 in the paper
constraint forall(i in 1..n*w)(
  (not [T[1, e, d] | e in 1..n, d in 1..w][i]) /\ (i = 1 \/ ([T[1, e, d] | e in 1..n, d in 1..w][i-1])) ->
  (i + uw > n*w \/ exists(j in lw..uw) ([T[1, e, d] | e in 1..n, d in 1..w][i+j]))
);  


% different variatons for the forbidden constraints are hardcoded
% this seems pretty inefficient, perhaps this could
% be something to optimise in the second part of the assignment
% the following 3 constraints have the same functionality as constraint 9 in the paper
% forbidden within an employee
constraint forall(s in 2..(m+1), e in 1..n, d in 1..(w-1))(
  (not T[s, e, d]) \/ forall(f in F[s-1])(not T[f+1, e, d+1])
);


% forbidden between employees
constraint forall(s in 2..(m+1), e in 1..(n-1))(
  (not T[s, e, 7]) \/ forall(f in F[s-1])(not T[f+1, e+1, 1])
);

% forbidden between first and last employee
constraint forall(s in 2..(m+1))(
  (not T[s, n, 7]) \/ forall(f in F[s-1])(not T[f+1, 1, 1])
);

% the following 3 constraints have the same functionality as constraint 10 in the paper
% forbidden 3 within employee
constraint forall(x in 1..round((length(forbidden3) / 3)), e in 1..n, d in 1..(w-2))
            (exists(j in 0..2)
              (not T[forbidden3[x,j+1]+1, e, d+j]));

% forbidden 3 between employees
constraint forall(x in 1..round((length(forbidden3) / 3)), e in 1..(n-1))
            (((not T[forbidden3[x, 1]+1, e, 6]) \/ (not T[forbidden3[x, 2]+1, e, 7]) \/ (not T[forbidden3[x, 3]+1, e+1, 1])) /\
            ((not T[forbidden3[x, 1]+1, e, 7]) \/ (not T[forbidden3[x, 2]+1, e+1, 1]) \/ (not T[forbidden3[x, 3]+1, e+1, 2])));

% forbidden 3 between first and last employee
constraint forall(x in 1..round((length(forbidden3) / 3)))
           (((not T[forbidden3[x, 1]+1, n, 6]) \/ (not T[forbidden3[x, 2]+1, n, 7]) \/ (not T[forbidden3[x, 3]+1, 1, 1])) /\
           ((not T[forbidden3[x, 1]+1, n, 7]) \/ (not T[forbidden3[x, 2]+1, 1, 1]) \/ (not T[forbidden3[x, 3]+1, 1, 2])));             

var int: freeWeekends = sum(e in 1..n)(T[1, e, 6] /\ T[1, e, 7]);
solve maximize freeWeekends;

output ["Schedule = \(T)\n", "Free Weekends = \(freeWeekends)\n"];