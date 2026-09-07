# Submit this package to Palomar

Mechanical verification is green. See `VERIFICATION.md` and `NOVELTY.md`.
Palomar still needs a **public GitHub** repository. This workspace is not
that repository until you publish it.

Form: https://submit.palomar-registry.org/

Policy:
https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md

## 1. Publish to public GitHub

Authenticated GitHub user on this pass: `mattppal`
(https://github.com/mattppal). Suggested repository name: `P3Removal`.

```text
# On GitHub: New repository, public, empty (no README / licence / gitignore).
# Then, from this checkout:

git remote add github git@github.com:mattppal/P3Removal.git
git push -u github main
git rev-parse HEAD
```

Use HTTPS if you prefer:

```text
git remote add github https://github.com/mattppal/P3Removal.git
git push -u github main
git rev-parse HEAD
```

Do not submit an `origin.cursor.com` URL. Palomar intake wants
`owner/name` on public GitHub.

If you already created a different public repo, replace
`mattppal/P3Removal` with that `owner/name` and push `main` there.

## 2. Form fields

Fill the submission form with these values. Branch names and tags are
not accepted in place of the commit.

| Field | Value |
|---|---|
| Repository | `mattppal/P3Removal` (or the public `owner/name` you actually pushed) |
| Source commit | the full 40-character SHA from `git rev-parse HEAD` after the push |
| Selected project path | `.` |
| `formalization.yaml` path | `formalization.yaml` |
| Comparator configuration path | `comparator.json` |

The Lean proof that Comparator accepted is ancestor
`200deb9471e1c23af8fc82720e19606617591b6f`. Doc-only commits on top of it
do not change Lean. **Submit the SHA of the commit you pushed**, not an
older note.

Ordinary-layout files already in the root:

```text
lean-toolchain
lakefile.toml
lake-manifest.json
formalization.yaml
Challenge.lean
Solution.lean
comparator.json
LICENSE
```

## 3. Authorization

`formalization.yaml` lists **Matt Palmer** as author and responsible
maintainer. The submitter must be that person, or have approval from
that person. Repository write access alone is not authorship.

Author endorsement of Shengtong Zhang is recorded as `not-contacted`.

## 4. What Palomar will check

- Challenge compiles against Lean core and Mathlib only.
- Comparator: `P3Removal.p3_removal_negative`,
  `P3Removal.p3_removal_positive`, `P3Removal.p3_removal`.
- NanoDa replay (`enable_nanoda` is ignored by Palomar; they force it on).
- Apache-2.0 root licence.
- No `TEMPLATE` metadata.

Local rerun of those gates is in `VERIFICATION.md`. Editorial review
(notability, fidelity) is separate and can still reject a green
mechanical run.

## 5. After the form

Keep the public commit. A later correction must use a new commit; Palomar
will not re-register the same SHA on the same identifier.
