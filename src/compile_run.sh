scalac -d compiled $(find /Users/samuel/EPFL/stainless/frontends/library/stainless/ -name "*.scala") VerifiedFunLexer.scala VerifiedDFA.scala ListUtils.scala --explain
scala -cp compiled MainTest