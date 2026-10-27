import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import cover6 as C6, multi as MU, resid as RD
hm = C6.hm
for s in sys.argv[1:]:
    D = hm.parse(s)
    print(s, C6.classify(D), MU.info(D))
