# Releasing QECLean

QECLean has two kinds of tag:

- **Library versions `v0.MINOR.PATCH`** — this document. A MINOR bump means a
  breaking API change (a declaration renamed, removed, or restated); a PATCH
  bump means proof-only, documentation, or performance changes. See
  [CHANGELOG.md](CHANGELOG.md).
- **Toolchain tags `v4.x`** (`v4.36.0-rc2`, …) — created automatically by
  `.github/workflows/create-release.yml` when `lean-toolchain` changes on
  `main`. Nothing to do by hand.

## Between releases

Every PR that changes the public API adds a line under `## [Unreleased]` in
`CHANGELOG.md`: under *Added*, *Changed*, or *Breaking* (old name → new name).
A breaking entry is what turns the next release into a MINOR bump.

## Cutting a release

1. On a branch, pick the version (`0.3.0` below) and set it in three places:
   - `lakefile.toml`: `version = "0.3.0"`;
   - `CITATION.cff`: `version: 0.3.0` and `date-released: "YYYY-MM-DD"`;
   - `CHANGELOG.md`: rename `## [Unreleased]` to `## [0.3.0] — YYYY-MM-DD`,
     add a fresh empty `## [Unreleased]` above it, note the toolchain and the
     mathlib revision (`jq -r '.packages[] | select(.name == "mathlib") | .rev'
     lake-manifest.json`), and update the compare links at the bottom.
2. Merge to `main` and wait for `Lean Action CI` to pass on the merge commit.
3. Tag that commit and push the tag:

   ```bash
   git tag -a v0.3.0 -m "QECLean v0.3.0"
   git push origin v0.3.0
   ```

4. `.github/workflows/release.yml` checks that the tag is on `main`, that the
   three versions agree, and that CI passed on the commit, then publishes a
   GitHub release whose notes are the changelog section. If CI was still
   running when the tag landed, re-run the workflow once it is green.
5. Downstream (`bb-distance-lean`, `mitten-distance-lean`): bump
   `rev = "v0.3.0"` in their `lakefile.toml`, then `lake update QEC`.

## Archival (DOI)

With the [Zenodo GitHub integration](https://docs.github.com/en/repositories/archiving-a-github-repository/referencing-and-citing-content)
enabled for `QECLean/QECLean`, every published release is archived with a DOI.
Zenodo reads `CITATION.cff` for the metadata. Enabling it is a one-time switch
on zenodo.org by an owner of the GitHub organization.
