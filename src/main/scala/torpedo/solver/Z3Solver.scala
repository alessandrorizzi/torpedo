/**
  * Copyright (C) 2020  Alessandro M. Rizzi <alessandromaria.rizzi@polimi.it>
  *
  * This program is free software: you can redistribute it and/or modify
  * it under the terms of the GNU Affero General Public License as
  * published by the Free Software Foundation, either version 3 of the
  * License, or (at your option) any later version.
  *
  * This program is distributed in the hope that it will be useful,
  * but WITHOUT ANY WARRANTY; without even the implied warranty of
  * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  * GNU Affero General Public License for more details.
  *
  * You should have received a copy of the GNU Affero General Public License
  * along with this program.  If not, see <http://www.gnu.org/licenses/>.
  *
  */
package torpedo.solver

import torpedo.ltl.{AtomicFormula, Before, Conjunction, Disjunction, F, False, G, Implication, LtlFormula, NegatedAtomicFormula, Negation, Release, True, Until, X}
import torpedo.main.{ProofFailure, Result, Success}
import torpedo.topologicalproof.{Clause, TPClause}
import z3.scala.{Z3AST, Z3Context}

class Z3Solver(k : Int) extends Solver {

  class Z3SolverInstance(clauses : Seq[Clause], k : Int) extends SolverInstance {

    private val z3Ctx = new Z3Context();

    private val solver = z3Ctx.mkSolver();

    private def bvSize(k : Int) = k + 2;

    private def bvSort(k : Int) = z3Ctx.mkBVSort(bvSize(k));

    private def bvConstant(value : Int, k : Int) = z3Ctx.mkInt(value, bvSort(k));

    private def bitVector(name : String, k : Int) = z3Ctx.mkConst(name, bvSort(k));

    private def loopVector(k : Int) = bitVector("__loopVector__", k);

    private def getBit(bv : Z3AST, index : Z3AST) =  z3Ctx.mkExtract(0, 0, z3Ctx.mkBVLshr(bv, index));

    private def reverse(lhs : Z3AST, k : Int) : Z3AST =
      Range(0, bvSize(k)).map(x => z3Ctx.mkExtract(x, x, lhs)).reduce((x, y) => z3Ctx.mkConcat(x, y));

    private def untilNL(x : Z3AST, y : Z3AST, k : Int) =
      z3Ctx.mkBVOr(y, z3Ctx.mkBVAnd(x,
        z3Ctx.mkBVNot(reverse(z3Ctx.mkBVAdd(reverse(z3Ctx.mkBVOr(x, y), k), reverse(y, k)), k))));

    private def clauseHandler(index : Int) : Z3AST = z3Ctx.mkBoolConst("__clause__" + index);

    private def toConstraint(clause : Clause, index : Int, k : Int) : Z3AST =
      z3Ctx.mkImplies(clauseHandler(index),
        z3Ctx.mkEq(z3Ctx.mkExtract(0, 0, translate(clause.clause, k)), z3Ctx.mkInt(1 ,z3Ctx.mkBVSort(1))));

    private def loopConstraint(bvName : String, k : Int) : Z3AST = {
      val bv = bitVector(bvName, k);
      z3Ctx.mkEq(getBit(bv, loopVector(k)), z3Ctx.mkExtract(k+1, k+1, bv));
    }

    private def loopVectorConstraint(k : Int) : Seq[Z3AST] =
      Seq(z3Ctx.mkBVUge(loopVector(k), bvConstant(1, k)), z3Ctx.mkBVUle(loopVector(k), bvConstant(k, k)));

    private def bvSet(formula: LtlFormula) : Set[String] =
      formula match {
        case Negation(f) => bvSet(f);
        case Conjunction(formulae) => formulae.map(bvSet).reduce(_ ++ _);
        case Disjunction(formulae) => formulae.map(bvSet).reduce(_ ++ _);
        case Implication(lhs, rhs) => bvSet(lhs) ++ bvSet(rhs);
        case Before(lhs, rhs) => bvSet(lhs) ++ bvSet(rhs);
        case Release(lhs, rhs) => bvSet(lhs) ++ bvSet(rhs);
        case Until(lhs, rhs) => bvSet(lhs) ++ bvSet(rhs);
        case X(f) => bvSet(f);
        case G(f) => bvSet(f);
        case F(f) => bvSet(f);
        case True =>  Set();
        case False =>  Set();
        case NegatedAtomicFormula(atom) => bvSet(atom);
        case a : AtomicFormula => Set(a.toPLTLMup);
      }

    private def translate(formula: LtlFormula, k: Int) : Z3AST = {
      formula match {
        case Negation(f) => z3Ctx.mkBVNot(translate(f, k));
        case Conjunction(formulae) => translate(formulae, k).reduce((lhs, rhs) => z3Ctx.mkBVAnd(lhs, rhs));
        case Disjunction(formulae) => translate(formulae, k).reduce((lhs, rhs) => z3Ctx.mkBVOr(lhs, rhs));
        case Implication(lhs, rhs) => translate(!lhs | rhs, k);
        case Before(lhs, rhs) => translate(!Until(!lhs, rhs), k);
        case Release(lhs, rhs) => translate(!Until(!lhs, !rhs), k);
        case Until(lhs, rhs) =>
          val lhsZ3 = translate(lhs, k);
          val rhsZ3 = translate(rhs, k);
          val loopRhsZ3 = z3Ctx.mkConcat(getBit(untilNL(lhsZ3, rhsZ3, k), loopVector(k)), z3Ctx.mkExtract(k, 0, rhsZ3));
          untilNL(lhsZ3, loopRhsZ3, k);
        case X(f) =>
          val prefix = getBit(z3Ctx.mkBVLshr(translate(f, k), z3Ctx.mkInt(1, bvSort(k))), loopVector(k))
          z3Ctx.mkConcat(prefix, z3Ctx.mkExtract(k+1, 1, translate(f, k)));
        case G(f) => translate(!F(!f), k);
        case F(f) => translate(True U f, k);
        case True =>  bvConstant(-1, k);
        case False =>  bvConstant(0, k);
        case NegatedAtomicFormula(atom) => z3Ctx.mkBVNot(translate(atom, k));
        case a : AtomicFormula => bitVector(a.toPLTLMup, k);
      }
    }

    private def translate(formulae: Seq[LtlFormula], k: Int) : Seq[Z3AST] = formulae.map(f => translate(f, k));

    override def input: Seq[String] = computeFullClauses.map(_.toString());

    private def computeFullClauses : Seq[Z3AST] =
      loopVectorConstraint(k) ++ clauses.map(_.clause).map(bvSet).reduce(_ ++ _).toSeq.map(loopConstraint(_, k)) ++
        clauses.zipWithIndex.map(indexedClause => toConstraint(indexedClause._1, indexedClause._2, k));

    override def check(): SolverResult = {
      computeFullClauses.foreach(solver.assertCnstr);
      solver.checkAssumptions(clauses.indices.map(clauseHandler) : _*) match {
        case None => UNKNOWN;
        case Some(true) => SATISFIABLE;
        case Some(false) => UNSATISFIABLE;
      }
    }

    override def topologicalProof: Result[Seq[TPClause]] = {
      if (check() != UNSATISFIABLE) {
        ProofFailure;
      }
      else {
        val indices = solver.getUnsatCore().map(_.toString().split('_').last.toInt)
        Success(indices.map(clauses).map(_.tpClause));
      }
    }
  }

  override def check(clauses: Seq[Clause]) : SolverResult = new Z3SolverInstance(clauses, k).check();

  override def check(clauses: Seq[Clause], logFilename : Option[String]) : SolverResult =
    new Z3SolverInstance(clauses, k).check();

  override def create(clauses: Seq[Clause], logFilename : Option[String]) = new Z3SolverInstance(clauses, k);

}
