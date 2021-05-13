/**
  * Copyright (C) 2017  Alessandro M. Rizzi <alessandromaria.rizzi@polimi.it>
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
package torpedo.main

import torpedo.mc.{ModelChecker, NuSMV}
import torpedo.solver.{HybridPLTLMup, PLTLMup, Solver, Z3Solver}

sealed class Options(var solver : Solver, var modelChecker : ModelChecker, var trace : Option[String],
                     var input : Option[String], var log : Option[String], var output : Option[String],
                     var slice : Option[String]
                    ) {

  def processCommandLineArguments(args : List[String]) : Boolean =
    args match {
      case "-c" :: filename :: rest => trace = Some(filename); processCommandLineArguments(rest);
      case "-i" :: filename :: rest => input = Some(filename); processCommandLineArguments(rest);
      case "-l" :: filename :: rest => log = Some(filename); processCommandLineArguments(rest);
      case "-o" :: filename :: rest => output = Some(filename); processCommandLineArguments(rest);
      case "-s" :: "pltlmup" :: rest => solver = PLTLMup; processCommandLineArguments(rest);
      case "-s" :: "hybrid" :: rest => solver = HybridPLTLMup; processCommandLineArguments(rest);
      case "-s" :: "z3" :: k :: rest => solver = new Z3Solver(k.toInt); processCommandLineArguments(rest);
      case "-t" :: filename :: rest => slice = Some(filename); processCommandLineArguments(rest);
      case Nil => true;
      case any :: _ => println("Unrecognized option: " + any); false;
    }

}

case object DefaultOptions extends Options(HybridPLTLMup, NuSMV, None, None, None, None, None);



