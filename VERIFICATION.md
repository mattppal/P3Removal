# Verification record

Run **2026-09-07**, UTC. Lean sources at
`200deb9471e1c23af8fc82720e19606617591b6f`. Doc-only commits after that
SHA do not change Lean. Re-run `git rev-parse HEAD` for the SHA you
submit.

Verdict: **green**.

## Commands

```text
export PATH="${HOME}/.elan/bin:${PATH}"
./scripts/verify.sh
./scripts/verify-comparator.sh
ruby scripts/validate-formalization.rb
ruby test/validate_formalization_test.rb
./test/landrun_wrapper_test.sh
```

`lean --version` on this machine: `4.32.0`
(`8c9756b28d64dab099da31a4c09229a9e6a2ef35`).

## Results

| Check | Exit | Notes |
|---|---|---|
| `./scripts/verify.sh` | 0 | `lake build` + no `sorry`/`admit` in proof modules + no `TEMPLATE` |
| `./scripts/verify-comparator.sh` | 0 | `Your solution is okay!` NanoDa and Lean kernel accepted Solution |
| `ruby scripts/validate-formalization.rb` | 0 | `formalization.yaml contains no TEMPLATE values` |
| `ruby test/validate_formalization_test.rb` | 0 | 16 runs, 83 assertions |
| `./test/landrun_wrapper_test.sh` | 0 | wrapper contract passed |

Challenge `sorry` warnings are the three Palomar statement holes. Proof
modules `P3Removal/**` and `Solution.lean` contain no `sorry` or `admit`.

## Palomar surface

| Requirement | Evidence |
|---|---|
| Challenge imports Mathlib only | `Challenge.lean` line 1: `import Mathlib.Combinatorics.SimpleGraph.LapMatrix`. No `import P3Removal`. 113 lines, 3753 bytes (under the 300-line / 32 KiB warning and the 1000-line / 100 KiB hard limit). |
| Solution matches Challenge | Comparator compared `P3Removal.p3_removal_negative`, `p3_removal_positive`, `p3_removal`. Empty `definition_names`. |
| `lake-manifest.json` committed | Present at repo root. Package name `P3Removal`. Mathlib pin `81a5d257c8e410db227a6665ed08f64fea08e997` (`v4.32.0`). Every `rev` is a 40-character lowercase SHA. `docbuild/lake-manifest.json` is also committed. |
| Licence | `LICENSE` is Apache-2.0. `project.license` is `Apache-2.0`. |

## formalization.yaml versus PalomarTemplate v0.4

Checked by reading the template sentinels and this file.

| Field | Required | This project |
|---|---|---|
| `version` | `v0.4` | `v0.4` |
| `project.authors` | nonempty | `Matt Palmer` |
| `project.responsible_maintainers` | nonempty | `Matt Palmer` |
| `project.license` | `Apache-2.0` | `Apache-2.0` |
| `classification.arxiv` | 1–2 official ids | `math.CO` |
| `classification.msc2020` | 1–8 five-character ids | `05C50`, `15A42` |
| `sources[].relationship` | exactly `formalizes`, `adapts`, `independently-proves`, `background`, or `other` | `formalizes` |
| result origin | no `original-proof` when formalizing a published theorem | omitted; source is `formalizes` |
| `related_formalizations[].relationship` | exactly `builds-on`, `adapts`, `independent`, `supersedes`, or `other` | `independent` |
| `status.sorry_count` | unquoted nonnegative integer | `0` |
| `status.sorry_in_definitions` | unquoted nonnegative integer | `0` |
| `status.axioms` | Lean axiom names or `[]` | `propext`, `Quot.sound`, `Classical.choice` |
| `automation.methods[].method` | `manual`, `copilot`, `agent`, `autonomous`, or `other` | `autonomous` |
| `repository` | omit for an ordinary project | omitted |
| `TEMPLATE` sentinels | none | none |

`author_endorsement` is `not-contacted`. Source licence is `unknown`.

## `./scripts/verify.sh` log

```text
Mon Sep  7 07:08:49 PM UTC 2026
⚠ [2727/2735] Replayed P3Removal.RowCol
warning: P3Removal/RowCol.lean:80:4: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
⚠ [2732/2735] Replayed Challenge
warning: Challenge.lean:84:8: declaration uses `sorry`
warning: Challenge.lean:93:8: declaration uses `sorry`
warning: Challenge.lean:102:8: declaration uses `sorry`
Build completed successfully (2735 jobs).
formalization.yaml contains no TEMPLATE values
EXIT:0
```

## `./scripts/verify-comparator.sh` log

```text
Mon Sep  7 07:09:18 PM UTC 2026
From https://github.com/leanprover/lean4export
 * branch            4e7915201d3f9f04470d9eae002fa695f7cdc589 -> FETCH_HEAD
HEAD is now at 4e79152 chore: bump toolchain to v4.32.0 (#41)
From https://github.com/leanprover/comparator
 * branch            68a064109f01c08f47c8edc9f51d6a2bbffaa188 -> FETCH_HEAD
HEAD is now at 68a0641 Merge pull request #55 from leanprover/uppies
From https://github.com/robsimmons/nanoda_lib
 * branch            68d5ca9db226849b41a6fff59d796ff19d0a8840 -> FETCH_HEAD
HEAD is now at 68d5ca9 chore: even more misc. bounds checks
go: github.com/zouuup/landrun@v0.1.18-0.20260723122309-811cfff51cea requires go >= 1.24.0; switching to go1.26.8
Build completed successfully (15 jobs).
Build completed successfully (6 jobs).
    Finished `release` profile [optimized] target(s) in 0.03s
Current branch: HEAD
Using cache from origin: (some leanprover-community/mathlib4)
No files to download
Already decompressed 8639 file(s)
Building Challenge
⚠ [2724/2725] Replayed Challenge
warning: Challenge.lean:84:8: declaration uses `sorry`
warning: Challenge.lean:93:8: declaration uses `sorry`
warning: Challenge.lean:102:8: declaration uses `sorry`
Build completed successfully (2725 jobs).
Exporting #[Nat, String, String.mk, Char, Char.ofNat, List, Quot, Quot.mk, Quot.lift, Quot.ind, P3Removal.p3_removal_negative, P3Removal.p3_removal_positive, P3Removal.p3_removal, propext, Quot.sound, Classical.choice, Nat.add, Nat.sub, Nat.mul, Nat.pow, Nat.gcd, Nat.div, Nat.mod, Nat.beq, Nat.ble, Nat.land, Nat.lor, Nat.xor, Nat.shiftLeft, Nat.shiftRight, String.ofList] from Challenge
Building Solution
⚠ [2727/2732] Replayed P3Removal.RowCol
warning: P3Removal/RowCol.lean:80:4: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
Build completed successfully (2732 jobs).
Exporting #[Nat, String, String.mk, Char, Char.ofNat, List, Quot, Quot.mk, Quot.lift, Quot.ind, P3Removal.p3_removal_negative, P3Removal.p3_removal_positive, P3Removal.p3_removal, propext, Quot.sound, Classical.choice, Nat.add, Nat.sub, Nat.mul, Nat.pow, Nat.gcd, Nat.div, Nat.mod, Nat.beq, Nat.ble, Nat.land, Nat.lor, Nat.xor, Nat.shiftLeft, Nat.shiftRight, String.ofList] from Solution
Running nanoda kernel on solution
Nanoda kernel accepts the solution
Running Lean default kernel on solution.
Lean default kernel accepts the solution
Your solution is okay!
EXIT:0
```

Pins used by the Comparator script: lean4export
`4e7915201d3f9f04470d9eae002fa695f7cdc589`, comparator
`68a064109f01c08f47c8edc9f51d6a2bbffaa188`, nanoda
`68d5ca9db226849b41a6fff59d796ff19d0a8840`, landrun
`811cfff51ceaf3d9843708aa6d22e9b84ccac8b4`.
