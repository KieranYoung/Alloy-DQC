import sys
import random

nq = int(sys.argv[1])
ng = int(sys.argv[2])
maxq = int(sys.argv[3])

print(".v ", end="")
for i in range(1, nq+1):
    print(f"q{i}", end=("\n" if i == nq else ", "))

qbits = [i for i in range(1, nq+1)]

for _ in range(0, ng):
    gsize = random.randint(1, maxq)
    g = sorted(random.sample(qbits, gsize))
    print(f"t{gsize} ", end="")
    for i in range(0, gsize):
        print(f"q{g[i]}", end=("\n" if i == gsize-1 else ", "))



