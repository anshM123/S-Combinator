import sys, re
bad = 0; kinds = {}
for line in open(sys.argv[1]):
    if not line.startswith("P="): continue
    pairs = line.strip().split(" : ")[1].split()
    mp = {}
    for p in pairs:
        a, b = p.split(">")
        mp[a] = b
    # classify: constant? prefix u+w? suffix w+u?
    vals = set(mp.values())
    if len(vals) == 1: k = "const"
    elif all(mp[w].endswith(w) and mp[w][:len(mp[w])-len(w)] == mp[""] for w in mp): k = "prefix"
    elif all(mp[w].startswith(w) and mp[w][len(w):] == mp[""] for w in mp): k = "suffix"
    else: k = "OTHER"
    kinds[k] = kinds.get(k, 0) + 1
    if k == "OTHER": print(line.strip())
print(kinds)
