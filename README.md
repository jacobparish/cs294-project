# cs294-project

Authors: Jacob Parish, Yvette Ren.

## About

This is our project for [CS294](https://ucb-lean-course-sp26.github.io). Our initial goal was to prove the Kleene-Post theorem. This is completed: `exists_incomparable_turingDegrees` in `KleenePost.lean`.

Our secondary goal was to prove the [Friedberg-Muchnik theorem](https://en.wikipedia.org/wiki/Friedberg%E2%80%93Muchnik_theorem). This is still a work in progress (not included in the submission).

File structure:
- `OracleCode.lean` - codes for partial recursive functions with an oracle, including their encoding/decoding into natural numbers, and their evaluation.
- `Queries.lean` - oracle query tracking.
- `KleenePost.lean` - the Kleene-Post theorem.

## Building locally

Download cached build files:
```sh
lake exe cache get
```

Build the project:
```sh
lake build
```
