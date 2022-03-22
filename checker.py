# python script to check validity of a solution
import json

# dzn
groups = 9
numShifts = 3
demand = [ 2, 2, 2, 2, 2, 2, 2,
           2, 2, 2, 3, 3, 3, 2,
           2, 2, 2, 2, 2, 2, 2 ]

minShift = [2, 2, 2]
maxShift = [7, 6, 4]
minOff = 2
maxOff = 4

minOn = 4
maxOn = 7

forbidden = [{}, {1}, {1,2}]
forbidden3 = []

# solution
T = [1, 1, 2, 2, 3, 3, 3, 
     0, 0, 1, 1, 1, 2, 2, 
     2, 0, 0, 3, 3, 3, 3, 
     0, 0, 1, 1, 1, 1, 1, 
     2, 2, 0, 0, 2, 2, 2, 
     3, 3, 3, 0, 0, 1, 1, 
     3, 3, 3, 3, 0, 0, 0, 
     1, 1, 2, 2, 2, 0, 0, 
     0, 2, 2, 2, 2, 0, 0]
filename = 'T.json'
if filename:
    # T = [0] * 9*7
    with open(filename, 'r') as f:
        data = json.load(f)
        print(len(data) / 7)

# split up forbidden 3
forbidden3 = [forbidden3[i:i+3] for i in range(0, len(forbidden3), 3)]

# check demands
# split schedule into weeks
week_schedule = [T[i:i+7] for i in range(0, len(T), 7)]
# create list for supplied workers per shift
supplied = []
for shift in range(numShifts):
    week_supply = [0] * 7
    supplied.append(week_supply)

for week in week_schedule:
    for day, task in enumerate(week):
        if task == 0:
            continue
        supplied[task-1][day] += 1

# split demand into weeks
week_demands = [demand[i:i+7] for i in range(0, len(demand), 7)]

for week_demand, week_supply in zip(week_demands, supplied):
    for day_demand, day_supply in zip(week_demand, week_supply):
        if day_supply < day_demand:
            print('Error: Supplied does not match demand')
            print(day_supply, day_demand)

# check min/max on

# check forbidden
for i, s in enumerate(T):
    if s == 0:
        continue
    f = forbidden[s-1]
    if T[(i+1) % len(T)] in f:
        print('Error: Forbidden constraint does not hold')
        print(f'{T[i]}, {T[(i+1) % len(T)]} (forbidden for {s}: {f})')

# check forbidden 3
for i, s in enumerate(T[:-2]):
    section = T[i:(i+3)]
    if section in forbidden3:
        print('Error: Forbidden 3 section')
        print(section)