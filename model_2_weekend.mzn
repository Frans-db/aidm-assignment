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

% the above code is exactly equal to the code in model_1.mzn. to avoid duplication
% please refer to the explanations in that file


% schedule variable
% we decided to work from the viewpoint of the combination of a shift and an employee
% each s in 1..(m+1), e in 1..n has a list of boolean values (d in 1..w), which indicates
% on which day of the week the employee does a shift

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
                    
% next 2 constraints break symmetries, and break some of the cyclicity in the schedule
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

% the next 4 constraints have the same functionality as constraints 5-8 in the paper,
% and have already been explained in detail in the model_1

% same functionality as constraint 5 in the paper
% ensures the miminum number of shifts s are worked in a row
% it checks the combined list of shifts (explained above) for number of shifts worked in a row
constraint forall(s in 1..(m+1), i in 1..n*w)(
  [T[s, e, d] | e in 1..n, d in 1..w][i] /\ (i = 1 \/ (not [T[s, e, d] | e in 1..n, d in 1..w][i-1])) ->
  forall(j in 1..(ls[s]-1))
      ([T[s, e, d] | e in 1..n, d in 1..w][i+j])
);  

% same functionality as constraint 6 in the paper
% ensures that no more than the maximum number of shifts s are worked in a row
constraint forall(s in 1..(m+1), i in 1..n*w)(
  [T[s, e, d] | e in 1..n, d in 1..w][i] /\ (i = 1 \/ (not [T[s, e, d] | e in 1..n, d in 1..w][i-1])) ->
  (i + us[s] > n*w \/ exists(j in ls[s]..us[s]) (not [T[s, e, d] | e in 1..n, d in 1..w][i+j]))
);  

% same functionality as constraint 7 in the paper
% ensures the miminum number of shifts (for any s) are worked in a row
constraint forall(i in 1..n*w)(
  (not [T[1, e, d] | e in 1..n, d in 1..w][i]) /\ (i = 1 \/ ([T[1, e, d] | e in 1..n, d in 1..w][i-1])) ->
  forall(j in 1..(lw-1))
      (not [T[1, e, d] | e in 1..n, d in 1..w][i+j])
);  

% same functionality as constraint 8 in the paper
% ensures that no more than the miminum number of shifts (for any s) are worked in a row
constraint forall(i in 1..n*w)(
  (not [T[1, e, d] | e in 1..n, d in 1..w][i]) /\ (i = 1 \/ ([T[1, e, d] | e in 1..n, d in 1..w][i-1])) ->
  (i + uw > n*w \/ exists(j in lw..uw) ([T[1, e, d] | e in 1..n, d in 1..w][i+j]))
);  


% different variatons for the forbidden constraints are hardcoded
% this seems pretty inefficient, perhaps this could
% be something to optimise in the second part of the assignment

% the following 3 constraints have the same functionality as constraint 9 in the paper
% checks for a single employee if there is any forbidden 2 sequences
% index w is not checked, because for this the first index of the next employee has to be checked
constraint forall(s in 2..(m+1), e in 1..n, d in 1..(w-1))(
  (not T[s, e, d]) \/ forall(f in F[s-1])(not T[f+1, e, d+1])
);


% checks if the shift performed at day w for employee e, and the shift performed at day 1
% for employee e+1 are forbidden
% employee n is not checked, because they have to be checked with employee 1
constraint forall(s in 2..(m+1), e in 1..(n-1))(
  (not T[s, e, 7]) \/ forall(f in F[s-1])(not T[f+1, e+1, 1])
);

% same functionality as above, but now the last and first employee are checked
constraint forall(s in 2..(m+1))(
  (not T[s, n, 7]) \/ forall(f in F[s-1])(not T[f+1, 1, 1])
);

% the following 3 constraints have the same functionality as constraint 10 in the paper
% checks for a single employee if there is any forbidden 3 sequences
% index w-2 to index 2 are not checked, because for this we have to use shifts from the next employee
constraint forall(x in 1..round((length(forbidden3) / 3)), e in 1..n, d in 1..(w-2))
            (exists(j in 0..2)
              (not T[forbidden3[x,j+1]+1, e, d+j]));

% checks if the shift performed at day w-1, and day 2 for employee e, and the shift performed at day 1
% for employee e+1 are forbidden or
% if the shift performed at day w for employee e, and the shift performed at day 1 and day 2
% for employee e+1 are forbidden
% employee n is not checked, because they have to be checked with employee 1
constraint forall(x in 1..round((length(forbidden3) / 3)), e in 1..(n-1))
            (((not T[forbidden3[x, 1]+1, e, 6]) \/ (not T[forbidden3[x, 2]+1, e, 7]) \/ (not T[forbidden3[x, 3]+1, e+1, 1])) /\
            ((not T[forbidden3[x, 1]+1, e, 7]) \/ (not T[forbidden3[x, 2]+1, e+1, 1]) \/ (not T[forbidden3[x, 3]+1, e+1, 2])));

% checks if the shift performed at day w-1, and day 2 for employee m, and the shift performed at day 1
% for employee 1 are forbidden or
% if the shift performed at day w for employee m, and the shift performed at day 1 and day 2
% for employee 1 are forbidden
constraint forall(x in 1..round((length(forbidden3) / 3)))
           (((not T[forbidden3[x, 1]+1, n, 6]) \/ (not T[forbidden3[x, 2]+1, n, 7]) \/ (not T[forbidden3[x, 3]+1, 1, 1])) /\
           ((not T[forbidden3[x, 1]+1, n, 7]) \/ (not T[forbidden3[x, 2]+1, 1, 1]) \/ (not T[forbidden3[x, 3]+1, 1, 2])));             

% calculate the number of free weekends as the number of times
% shift 0 is true for an employee on both day 6 and 7
var int: freeWeekends = sum(e in 1..n)(T[1, e, 6] /\ T[1, e, 7]);
solve maximize freeWeekends;

output ["Schedule = \(T)\n"];
output [show(freeWeekends)];