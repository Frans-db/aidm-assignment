include "globals.mzn";

int: w = 7;

% Loaded data
int: groups;
int: numShifts;
array[1..numShifts, 1..w] of int: demand;
array[1..numShifts] of int: minShift;
array[1..numShifts] of int: maxShift;
int: minOff;
int: maxOff;
int: minOn;
int: maxOn;

array[int] of set of int: forbidden;
array[int, int] of set of int: forbidden3;

% Variables o and T
var 0..(w-1): o;
array[1..numShifts*w] of var 1..numShifts*7: T;


constraint forall(d in 1..w, s in 1..numShifts)(sum(i in 0..(groups - 1))(T[d+w*i mod numShifts*w]) == demand[s, d + o mod w]);

solve satisfy;

output ["T = \(demand[2, 1])\n"];