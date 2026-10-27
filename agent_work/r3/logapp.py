"""append stdin to agent_work/LOG.md, replacing @TS@ by the current local time HH:MM (R3 agent helper)"""
import sys, os, datetime
txt = sys.stdin.buffer.read().decode("utf-8")
ts = datetime.datetime.now().strftime("%H:%M")
p = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "LOG.md")
with open(p, "a", encoding="utf-8") as f:
    f.write(txt.replace("@TS@", ts))
print("appended at", ts)
