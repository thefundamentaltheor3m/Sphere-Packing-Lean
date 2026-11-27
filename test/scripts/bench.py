#!/usr/bin/env python3
"""Score a tactic on a file of `example`s whose proofs are replaced by the tactic.

    bench.py make   <src.lean> <out.lean> <tactic> <module to import>
    bench.py score  <out.lean> <log>                 # per `section` of <src.lean>
    bench.py corpus <corpus.lean> <out.lean> <log>   # per tag of test/IntegrabilityCorpus.lean
    bench.py mark   <corpus.lean> <out.lean> <log>   # rewrite the `status:` lines (idempotent)

`make` copies <src.lean>, replacing its imports by `import Mathlib` and the given module, and the
body of every `example … := by …` by the tactic; it records the line range of each example in
<out.lean>.ranges.json. <log> is the output of `lake env lean -DmaxErrors=100000 <out.lean>`.
An example passes if its range has no error and no `declaration uses sorry` warning.
See `run.sh` for the whole sequence.
"""
import collections, json, re, sys

TACTIC = 'endpoint_integrability'
ENTRY = r'(?=/- \[[A-Z]+-\d+\])'


def make(src, out, tac, imp):
    lines = open(src, encoding='utf-8').read().split('\n')
    res, ranges, section, i = ['import Mathlib', 'import ' + imp], [], '', 0
    while i < len(lines):
        line = lines[i]
        if line.startswith('import '):
            i += 1
            continue
        m = re.match(r'^section (\S+)', line)
        if m:
            section = m.group(1)
        if line.startswith('example'):
            j = i
            while ':=' not in lines[j]:
                j += 1
            start = len(res) + 1
            res.extend(lines[i:j + 1])
            k = j + 1
            while k < len(lines) and lines[k].strip() != '' and lines[k][0] in ' \t':
                k += 1
            if not lines[j].rstrip().endswith(':= by'):
                res[-1] = re.sub(r':=.*$', ':= by', res[-1])
            res.append('  ' + tac)
            ranges.append((start, len(res), section))
            i = k
            continue
        res.append(line)
        i += 1
    open(out, 'w', encoding='utf-8').write('\n'.join(res) + '\n')
    json.dump(ranges, open(out + '.ranges.json', 'w'))
    print(len(ranges), 'examples')


def diagnostics(log):
    """The diagnostics `(line, kind, message)` of a log."""
    text = open(log, encoding='utf-8').read()
    blocks = re.split(r'\n(?=\S+\.lean:\d+:\d+: (?:error|warning))', '\n' + text)
    found = []
    for b in blocks:
        m = re.match(r'\s*\S+\.lean:(\d+):\d+: (error|warning): (.*)', b, flags=re.S)
        if m:
            found.append((int(m.group(1)), m.group(2), m.group(3)))
    return [d for d in found if d[1] == 'error' or 'sorry' in d[2]]


def failures(out, log):
    """For each example, the diagnostics which make it fail."""
    ranges = json.load(open(out + '.ranges.json'))
    diag = diagnostics(log)
    return [(sec, [d for d in diag if a <= d[0] <= b]) for a, b, sec in ranges]


def score(out, log):
    total, passed = collections.Counter(), collections.Counter()
    for sec, bad in failures(out, log):
        total[sec] += 1
        passed[sec] += not bad
    print(f'passed {sum(passed.values())} of {sum(total.values())}')
    for sec in total:
        print(f'  {sec:42s} {passed[sec]:3d} / {total[sec]:3d}')


def entries(corpus):
    """The header of the corpus and its entries `(id, comment, rest)`."""
    parts = re.split(ENTRY, open(corpus, encoding='utf-8').read())
    res = []
    for p in parts[1:]:
        k = p.index('-/')
        res.append((re.match(r'/- \[([A-Z]+-\d+)\]', p).group(1), p[:k], p[k:]))
    return parts[0], res


def tag(comment, key):
    m = re.search(key + r':\s*([^\n]*)', comment)
    return m.group(1).strip() if m else '?'


def corpus(src, out, log):
    _, ents = entries(src)
    fails = failures(out, log)
    assert len(ents) == len(fails), (len(ents), len(fails))
    total, passed, ids = collections.Counter(), collections.Counter(), []
    for (eid, comment, _), (_, bad) in zip(ents, fails):
        keys = [('project', eid.split('-')[0])] + \
            [(k, tag(comment, k)) for k in ('integrand', 'domain', 'kind')]
        for k in keys:
            total[k] += 1
            passed[k] += not bad
        if not bad:
            ids.append(eid)
    print('passed', len(ids), 'of', len(ents))
    for grp in ('project', 'integrand', 'domain', 'kind'):
        print(' ', grp + ':', '; '.join(f'{k[1]} {passed[k]}/{total[k]}' for k in total if k[0] == grp))
    print('  passed ids:', ' '.join(ids))


def status(comment, bad):
    """The status of an entry which is not proved."""
    kind, domain, integrand = (tag(comment, k) for k in ('kind', 'domain', 'integrand'))
    if kind.startswith('domination'):
        return 'out of scope: a domination hypothesis, not an integrability goal'
    if 'ℝⁿ' in domain or 'product' in domain or 'abstract measure' in domain:
        return 'out of scope: not an integral over an interval of `ℝ`'
    if integrand.startswith('abstract'):
        return 'out of scope: abstract integrand; needs closure rules (`fun_prop`), not a leaf solver'
    msg = bad[0][2]
    cases = list(dict.fromkeys(re.findall(r'case (\w+)', msg)))
    why = 'goals left: ' + ', '.join(cases) if cases else \
        msg.split('\n')[0][:90].replace(TACTIC + ': ', '')
    return 'open: ' + why


def mark(src, out, log):
    head, ents = entries(src)
    fails = failures(out, log)
    assert len(ents) == len(fails), (len(ents), len(fails))
    counts, pieces = collections.Counter(), [head]
    for (_, comment, rest), (_, bad) in zip(ents, fails):
        comment = re.sub(r'\n   status:.*\Z', '', comment.rstrip(), flags=re.S)
        st = status(comment, bad) if bad else f'proved by `{TACTIC}`'
        counts[st.split(':')[0].split(' by')[0]] += 1
        body = '  sorry\n' if bad else f'  {TACTIC}\n'
        rest = re.sub(r'(:= by\n)  (?:sorry|' + TACTIC + r')\n', lambda m: m.group(1) + body, rest)
        pieces.append(f'{comment}\n   status: {st} {rest}')
    open(src, 'w', encoding='utf-8').write(''.join(pieces))
    print(dict(counts))


if __name__ == '__main__':
    {'make': make, 'score': score, 'corpus': corpus, 'mark': mark}[sys.argv[1]](*sys.argv[2:])
