/** Author: Samuel Chassot
  */

import stainless.annotation._
import stainless.collection._
import stainless.equations._
import stainless.lang._
import stainless.proof.check
import scala.annotation.tailrec
import scala.collection.immutable.Range.BigInt.apply

object VerifiedExtendedLexer {
  import VerifiedFunLexer._

  sealed abstract class ExtendedToken[C]

  def lexExtended[C](
      rules: List[Rule[C]],
      input: List[C],
      tokenBuilder: SimpleToken[C] => ExtendedToken[C],
      tokenBuilderBack: ExtendedToken[C] => SimpleToken[C]
  ): (List[Token[C]], List[C]) = {} ensuring (res =>
    if (res._1.size > 0) res._2.size < input.size && !res._1.isEmpty
    else res._2 == input
  )

  def convertTokens(
      input: List[Token[C]],
      tokenBuilder: SimpleToken[C] => ExtendedToken[C],
      tokenBuilderBack: ExtendedToken[C] => SimpleToken[C]
  ): (List[ExtendedToken[C]], List[C])
}
