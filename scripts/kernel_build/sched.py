"""Throttled builder: `lake build <module>` one module per process, at most N at once, and no new
launch while lean processes use more than CAP GB of RSS or swap is in use.  Usage:
  python sched.py <listfile> <N> <CAP_GB> <logdir>
Each line of listfile is a module name; lines starting with # are ignored.  Exit code 1 if any
module failed.  Restartable: modules whose olean is newer than the source are skipped."""
import sys, subprocess, time, os, re
REPO = '/Users/js4814/LocalGithub/ThompsonEight'
mods = [l.strip() for l in open(sys.argv[1]) if l.strip() and not l.startswith('#')]
N = int(sys.argv[2]); CAP = float(sys.argv[3]) * 1024 * 1024; logdir = sys.argv[4]
os.makedirs(logdir, exist_ok=True)
def uptodate(m):
    src = os.path.join(REPO, m.replace('.', '/') + '.lean')
    ol = os.path.join(REPO, '.lake/build/lib/lean', m.replace('.', '/') + '.olean')
    return os.path.exists(ol) and os.path.getmtime(ol) >= os.path.getmtime(src)
def lean_rss_kb():
    out = subprocess.run(['ps', '-o', 'rss=,command=', '-ax'], capture_output=True, text=True).stdout
    tot = 0
    for line in out.splitlines():
        parts = line.split(None, 1)
        if len(parts) == 2 and re.search(r'/bin/lean |^lean ', parts[1]) and '--server' not in parts[1] and '--worker' not in parts[1]:
            tot += int(parts[0])
    return tot
def avail_gb():
    out = subprocess.run(['vm_stat'], capture_output=True, text=True).stdout
    pages = {}
    for line in out.splitlines():
        m = re.match(r'Pages (free|inactive|speculative):\s+(\d+)', line)
        if m: pages[m.group(1)] = int(m.group(2))
    return sum(pages.values()) * 16384 / 2**30
def swap_used_mb():
    out = subprocess.run(['sysctl', '-n', 'vm.swapusage'], capture_output=True, text=True).stdout
    m = re.search(r'used = ([\d.]+)M', out)
    return float(m.group(1)) if m else 0.0
FORCE = len(sys.argv) > 5 and sys.argv[5] == 'force'
pending = [m for m in mods if FORCE or not uptodate(m)]
print("%d modules, %d to build" % (len(mods), len(pending)), flush=True)
running = {}; failed = []; done = 0; t0 = time.time()
while pending or running:
    for m, (p, t) in list(running.items()):
        if p.poll() is not None:
            del running[m]; done += 1
            ok = p.returncode == 0
            if not ok: failed.append(m)
            print("%s %s (%.0fs) [%d/%d, %d failed] %s" % (time.strftime('%H:%M'), m, time.time() - t, done, len(pending) + done + len(running), len(failed), "ok" if ok else "FAILED"), flush=True)
    while pending and len(running) < N and avail_gb() > float(sys.argv[3]) and swap_used_mb() < 40000:
        m = pending.pop(0)
        log = open(os.path.join(logdir, m + '.log'), 'w')
        p = subprocess.Popen(['lake', 'build', m], cwd=REPO, stdout=log, stderr=subprocess.STDOUT)
        running[m] = (p, time.time())
        time.sleep(20)   # let the new worker's memory settle before judging the next launch
    if pending and not running:
        print("%s waiting: avail=%.1fGB swap=%.0fMB" % (time.strftime('%H:%M'), avail_gb(), swap_used_mb()), flush=True)
    time.sleep(10)
print("all done in %.0f min; failed: %s" % ((time.time() - t0) / 60, failed), flush=True)
sys.exit(1 if failed else 0)
