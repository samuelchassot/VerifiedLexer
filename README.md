# VerifiedLexer

## Verification
To verify the project, you need Stainless (https://github.com/epfl-lara/stainless.git).

To install it:
- clone https://github.com/epfl-lara/stainless.git
- run `sbt universal:stage`
- add `dirStainless/frontends/scalac/target/universal/stage/bin` to the PATH
- check that `stainless-scalac` is accessible

Then, run `src/verify.sh`

## Usage
To use the lexer, please see the `Main` object in `VerifiedLexer.scala` for examples. You can the run the scripts `.compile.sh` and `run.sh` to compile respectively run the lexer.
