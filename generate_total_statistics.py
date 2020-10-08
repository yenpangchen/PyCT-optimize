import os

class JumpOutOfLoop(Exception): pass

data = [['Project', 'Line Coverage', '# of SAT']]
for item in os.listdir('./project_statistics'):
    try:
        first_layer = True; data2 = [item]; num = 0
        for dirpath, _, _ in os.walk('./project_statistics/' + item):
            if first_layer:
                first_layer = False
                try:
                    with open(dirpath + '/inputs_and_coverage.txt', 'r') as f:
                        lines = f.read().splitlines()
                        data2.append(lines[-2].replace('Total line coverage ', ''))
                except:
                    raise JumpOutOfLoop()
                continue
            try:
                with open(dirpath + '/smt.csv', 'r') as f:
                    lines = f.read().splitlines()
                    num += int(lines[1].split(',')[1])
            except: pass
        data2.append(num)
        data.append(data2)
    except JumpOutOfLoop: pass

import csv
with open('./project_statistics/total_statistics.csv', 'w') as f:
    writer = csv.writer(f)
    writer.writerows(data)
