# Release Management

1. Update version in `Cargo.toml` and set all dependencies to that version. Always start with a prerelease version `-pre.A` before doing a full release.
2. Tag the version `git tag vX.Y.Z` and `git push origin vX.Y.Z`.
3. Release crates
   1. libcrux-platform in `sys/platform`
   2. libcrux-hacl in `sys/hacl`
   3. libjade-sys in `sys/libjade`
   4. libcrux
