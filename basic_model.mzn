include "globals.mzn";

int: groups;
int: numShifts;
array[1..numShifts, 1..7] of int: demand;
array[1..numShifts] of int: minShift;
array[1..numShifts] of int: maxShift;
int: minOff;
int: maxOff;
int: minOn;
int: maxOn;

array[int] of set of int: forbidden;
array[int, int] of set of int: forbidden3;