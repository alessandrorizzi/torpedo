# torpedo
Partial kripke structure LTL model checker

## Compile

Run `sbt assembly`.

## Launch

Install the required Docker containers running `./prepare.sh`
from the `docker` folder.

After compilation, 
run `java -jar target/scala-2.12/torpedo.jar analysis [options] <PKS XML file> <property file>` to check a property.

Possible options are:

* `-c <filename>`: write a trace violating the property to the given filename.
* `-i <filename prefix>`: write the input passed to the external solver in files with a given prefix.
* `-l <filename prefix>`: write the external solver output in files with a given prefix.
* `-o <filename>`: write the parts of the PKS needed for the property to hold to the given filename.
* `-s solver [bound]`: external solver to be used. Possible choices are `pltlmup`, `hybrid` and `z3`. The bound parameter is only allowed (and required) for `z3`.
* `-t <filename>`: write the parts of the PKS needed for the property to hold to the given filename as a PKS slice.

Run `java -jar target/scala-2.12/torpedo.jar recheck <PKS XML file> <PKS Slice file>` to
see if the proof contained in the slice file is still valid for the new PKS.
