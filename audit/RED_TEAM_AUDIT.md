# Adversarial Red-Team Audit: z_max(9) = 6 claim

(Output of the independent read-only red-team subagent. Saved by the coordinator; formatting lightly normalized, content unedited. Line refs are `tau_z9_unconditional.c` unless prefixed `vz:` for `verify_z9_all_Z.py`.)

**Bottom line:** the auditor did **not break** the core mathematical claim z_max(9)=6 for the actual tau=1..9, K=6 configuration. Every C certificate (`cert_deg`, `cert_prod`, `cert_p1`, `cert_taylor`, `cert_fallback`), modular helper, `__int128` Taylor guard, canonicalization rule, and the Python Z[x] Hensel verifier holds mathematically at K=6.

However the claim is **not unconditionally proved in the strict deterministic/formal sense**, and the codebase/docs contain real bugs, an unsound CLI boundary (K=0), a telemetry bug (`nodes_visited` undercounting), and several false/overclaimed statements:

1. **Unchecked K=0 unsoundness** (c:900): K=0 is permitted, yet `cert_dup_zero` prunes `x` assuming z_max(0)=1 <= K.
2. **Telemetry undercount in `nodes_visited`** (c:771-827, shared with tau_parallel.c:324-380): `collect_work` never increments `nodes_visited`, dropping 44 internal nodes for tau in {5,6,7} and 529 for tau in {8,9} (true tau=9 internal nodes = 7,767,649,524, not 7,767,648,995).
3. **Hash dependence + bogus collision-probability math:** internal dup/zero pruning (2 fixed-point evaluations) and survivor dedup (3 fixed-point evaluations) are not proved collision-free; paper/report probabilities (<1e-16, <1e-13, <1e-40) apply random-point/uniform-hash formulas to fixed points and drop Schwartz-Zippel degree factors (d <= 512).
4. **Reproducibility/verification gaps:** repro commands run only tau=9 (omit tau=1..8 on which `cert_dup_zero` relies); `-DALT_PRIMES` compared only 12 aggregate counters, not survivor polynomial sets; `fclose`/alloc errors unchecked in C; `verify_z9_all_Z.py` does not assert processed == lines or compare to C's `survivors_uniq`.
5. **Repository stats claims:** paper:49 claims "706 public theorems in 42 modules" (auditor counts 72 theorem/lemma declarations in 6 modules in this repo); README:63 claims "4 modules, 893 LOC" (actual 6 modules, 1,401 LOC); paper:150 misdescribes the verifier's prime selection and Cauchy bound.

## 1. Audit table

| Rule / Mechanism | Lines | Soundness argument (summary) | Verdict |
|---|---|---|---|
| Sign canonicalization (operand ordering) | 698-702, 707-710, 717-721, 731, 738-739, 796, 803-804 | Each gate stands for {±g_k}. Tracking signs s_m: for +/- rewriting flips +/- when s_i s_j=-1 and pulls out overall sign; swapping operands leaves + and * invariant and negates -, flipping s_k. sub with i=j gives 0 (excluded). Output sign irrelevant since Z(-f)=Z(f). Leaf unused_cnt==2 gives i<j via ctz; unused_cnt==1 gives i=min, j=max. | sound but subtle |
| Dead-gate / unused-count pruning & leaf cases | 692-693, 696-724, 726-734, 757-758, 788-799, 821-822 | In a minimal SLP every non-final gate is an operand of a later gate. After placing gate `depth`, rem_after=tau-1-depth gates remain with 2*rem_after operand slots, which must absorb next_cnt unused gates plus rem_after-1 future non-final gates: next_cnt <= rem_after+1. Equivalent to removed >= min_removed. By induction min_removed <= 2. At depth==tau-1, unused_cnt in {1,2} (0 only for tau=1). | sound but subtle |
| Lex-minimal topological ordering | 736, 740-741, 801, 805-806 | key=(op<<10)|(i<<5)|j injective for i,j<32. Swap adjacent independent gates, relabel wires, re-canonicalize signs: key[0..d-2] unchanged, key[d-1] strictly decreases, so lexicographic descent terminates. Last gate rightly excluded. | sound but subtle |
| Internal dup/zero hash pruning | 260-299, 743-751, 808-815 | Compares gate idx to 0, ±w_m (incl. 1, x). If equal, replacing it yields shorter SLP (certified by induction with K>=1). Lossless iff no 2-prime hash collision; points fixed, coefficients up to ~2^256, so collision-freeness is heuristic. | sound but subtle |
| Leaf dup/zero pruning | 635-640 | Sound if (a) all tau'<tau have z_max<=K (false if running tau=9 standalone without tau<=8), (b) K>=1 (unsound for K=0), (c) no hash collision. | sound but subtle (unsound at K=0) |
| Survivor hash dedup | 191-244, 685-686 | Sign-folded lex-min key of (r1,r2,r3) is exact for ±f. Gap: non-equivalent survivors colliding on all 3 hashes would be silently merged; ALT_PRIMES only compared aggregate counts. | sound but subtle |
| Degree upper bound | 255-256, 352-355, 470-472, 571-578 | Standard. uint16_t suffices for tau<=12. | obviously sound |
| Atomic product-factor mask (incl. 2A, constants) | 257-258, 301-309, 357-368, 473-482, 580-593 | Invariant: for nonzero g_k, Z(g_k) ⊆ ∪_{a in pmask} Z(g_a), each such g_a nonzero. Constants have no roots; Z(AB)=Z(A)∪Z(B); Z(2A)=Z(A). Bitmask/int widths fit. | sound but subtle |
| z_ub propagation | 253-254, 369-377, 545-553 | uint8 clamp at 255 can never spuriously satisfy <=K (K<=18). Tightening by zeros only when zeros<p and doubles==0. | sound but subtle |
| Mod-31 leaf fast path | 595-632 | uint8 sums <= 60 so sv in {0,31} iff ≡0; sub: equal iff ≡0; mul: field, zero/double formula correct. zeros<=K<31 forces fbar≠0. | sound but subtle |
| eval_gate_p1 | 311-378 | Exact dual-number rules mod 31, range invariant [0,30]. | sound but subtle |
| certify_slp_mod_p (p in {19,23,29}) | 452-565 | Array bounds ok (48 > p); value ranges fit uint8; last-gate shortcut valid. | sound but subtle |
| Taylor certificate | 380-448, 493-540, 561-563, 642-674 | TAYLOR_DEG=12, LIM=1e17: max convolution sum 1.2e35 << 2^127. PTS matches KNOWN_ROOTS mod p, all distinct. m>=1 and cm%p≠0 give h(r0)≢0 mod p, hence no other integer root ≡ r0. Comments (t^8, 8*LIM^2) are stale. Not formalized in Lean. | sound but subtle |
| Fallback primes {19,23,29} | 49-50, 677-682 | Primes > 18 >= K; header comment (l.8) falsely mentions {37,41,43}. | sound but subtle |
| Modular helpers (madd/msub/mmul/mod31_reduce) | 52-90 | No overflow for default or ALT primes; mod31_reduce valid for t<=30751, callers <=1800. | sound but subtle |
| Work splitting & prefix replay | 771-887, 935-944 | collect_work mirrors dfs pruning; replay reconstructs state; no leaf dropped or double counted. BUG: collect_work omits nodes_visited++ (telemetry only). | sound (search); unsound (nodes_visited count) |
| Thread safety & counter conservation | 141-145, 221-243, 567-687, 768-769, 844-887, 945-969 | Correct. Gaps: nthreads<=0 spawns 0 threads silently; alloc/fprintf/fclose errors unchecked. | sound but subtle |
| K / cert_bound interplay | 629, 644, 900, vz:191, vz:273-274 | K<19 forces zeros<p. BUG: K=0 allowed, and leaf dup prunes 1*x = x (1 root > 0). | unsound at K=0; sound for 1<=K<=18 |
| tau<=4 serial path | 918-934 | Fine. No CLI check on tau<1 or tau>MAX_TAU. | sound but subtle |
| Verifier: PRS & sqf_part | vz:70-167 | Exact integer arithmetic, asserted exact division. | obviously sound |
| Verifier: has_zero & x factors | vz:231-251, 274-281 | Correct. | obviously sound |
| Verifier: Cauchy bound, Hensel, target_mod | vz:197-222, 254-285 | Newton lifting valid even if p | lc(g); final exact check prevents spurious p-adic roots. | sound but subtle |
| Verifier: pool exceptions & processed==lines | vz:317-336, 375-417 | Exceptions propagate. Gap: no assert sum==n, no comparison to C's survivors_uniq. | unclear |

## 2. Adversarial hunt (summary)

1. Interplay lex + dead-gate + dup: no escape at tau=9 given tau=1..8 were also run (minimal-length program argument). Auditor ran a brute-force tau=1..4 comparison (847 polys at tau=4, 0 missing). Caveat: certifying z_max(9)<=6 requires tau=1..8 too.
2. cert_taylor wrongly certifying (m=0, m=1 with 31|cm, m>=12, int128 overflow, PTS mismatch): all rejected by explicit guards.
3. cert_prod / z_ub with zero constants, 2A, clamping: cannot poison.
4. Verifier Hensel when p | lc(g): still sound (verified empirically).
5. Real failure modes: K=0 CLI; nthreads<=0; deterministic hash collision (theoretical); silent truncated write / C-Python mismatch.

## 3. Unjustified claims / overclaims

1. paper:49 "706 public theorems in 42 modules" vs auditor count 72 / 6 modules in this repo.
2. README:63 "4 modules, 893 LOC" vs 6 modules, 1,401 LOC.
3. README:1,11,30 "up to tau = 15" vs table to tau=18.
4. paper:181-191, report:12,61-65,73, README:20,23: node count 7,767,648,995 "matching tau_parallel.c" - both omit prefix nodes; matching only confirms shared code.
5. report:114-115, paper:246-247, README:23: Schwartz-Zippel / birthday / <1e-40 claims invalid (fixed points, degree factors dropped, d up to 512 at leaves, P_i may divide the difference, ALT_PRIMES compared only counters).
6. paper:150: verifier prime selection / squarefree mod p / Cauchy bound wording does not match the code.
7. repro commands (paper:251-257, README:83-87, report:126-130) run only tau=9.
8. "unconditionally proved / 100% lossless" framing (paper:41,43,157; report:5,112; README:19): Prop. 2 (cert_taylor), cert_prod, canonicalizations, C/Python code, hash collision-freeness not formally proved.
9. Stale comments in C: line 8 primes {37,41,43}; lines 380-385 `t^8`, `8*LIM^2`.

## 4. Prioritized checklist

P0: eliminate/bound the hash-collision trust (exact identity checks or set-equality of ALT survivors); close C/Python boundary gaps (K>=1, tau range, nthreads>=1, write checks, assert processed==lines, compare to survivors_uniq, repro runs tau=1..9).
P1: fix nodes_visited; differential test against a clean exact enumerator for tau=1..5; formalize cert_taylor, cert_prod and the canonicalizations in Lean.
P2: correct paper/README/report/comment errors.
