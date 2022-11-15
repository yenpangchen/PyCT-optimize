from  libct.concolic.float import ConcolicFloat
import time

a = 1

start = time.time()
for i in range(1000000):
    a = a+0.0

t1 = time.time()-start
start = time.time()

a = ConcolicFloat(1.0)
for i in range(1000000):
    a = a+0.0

t2 = time.time()-start
print("t1=%.2f, t2=%.2f, t2/t1=%.2f" % (t1, t2, t2/t1) )