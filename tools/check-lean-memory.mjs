// Was a failed build killed for MEMORY? (check-lean's 'exit 137' rule, 2026-11-25.)
// On the public runner the checker runs in its own systemd scope with a memory limit; a build that
// grows to that limit and swaps until it dies used to come back as 'the build failed for a reason
// that is not an error in a project file' (exit 3), which the intake re-runs on the same runner,
// where it fails the same way (17005, 17148, 17212). The intake knows a memory ending as exit 137,
// so the checker says it itself when it can tell. Two signs, either one enough:
//   1. the scope's own kernel counter of out-of-memory kills (cgroup v2 memory.events, oom_kill)
//      went up while the build ran;
//   2. ONLY where no cgroup can be read (a seat's Mac, a test): the runtime's own line, at the start of a
//      line, said so. The build's output carries text the outside file controls (its own error wording,
//      anything it prints), so on the runner, where the counter exists, printed text never decides; and the
//      text sign never turns an error in a project file into a memory ending (red team, 2026-11-25 17:45Z).
import { readFileSync } from 'node:fs';
import { join } from 'node:path';

export const OOM_TEXT = /^(INTERNAL PANIC: out of memory|terminate called after throwing an instance of 'std::bad_alloc')/m;

// The oom_kill count of the cgroup this process is in, or null when it cannot be read.
export function oomKills(procCgroup = '/proc/self/cgroup', root = '/sys/fs/cgroup') {
  try {
    const line = readFileSync(procCgroup, 'utf8').split('\n').find((l) => l.startsWith('0::'));
    if (!line) return null;
    const m = /^oom_kill (\d+)$/m.exec(readFileSync(join(root, line.slice(3).trim(), 'memory.events'), 'utf8'));
    return m ? Number(m[1]) : null;
  } catch { return null; }
}

// True when the kernel counter was read before and after the build and went up.
export const counterRose = (killsBefore, killsAfter) => killsBefore !== null && killsAfter !== null && killsAfter > killsBefore;

// True when the build's failure was a memory death. Where the counter can be read it alone decides.
export function diedOfMemory({ output = '', killsBefore = null, killsAfter = null }) {
  if (killsBefore !== null && killsAfter !== null) return killsAfter > killsBefore;
  return OOM_TEXT.test(output);
}
