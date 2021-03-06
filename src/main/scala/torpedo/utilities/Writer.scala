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
package torpedo.utilities

import java.io.{FileWriter, IOException}

import torpedo.main.{NoError, NoValue, WriteFailure}

object Writer {

  private def write(filename : String, append : Boolean, lines : Seq[String]) : NoValue = {
    try {
      val file = new FileWriter(filename, append);
      lines.foreach(line => file.write(line + "\n"));
      file.close();
      NoError;
    }
    catch {
      case _ : IOException => WriteFailure(filename);
    }
  }

  def write(filename : String, lines : Seq[String]) : NoValue = write(filename, append = false, lines);

  def append(filename : String, lines : Seq[String]) : NoValue = write(filename, append = true, lines);

}
