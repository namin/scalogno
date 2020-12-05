scalogno
========

Scalogno as presented in APLAS'19 ([PDF](https://namin.seas.harvard.edu/files/namin/files/scalogno.pdf)).

- [2.1 Relations as Functions](src/test/scala/scalogno/core.scala#L274)
- [2.1 edge example](src/test/scala/scalogno/core.scala#L281)
- [2.1 path def example](src/main/scala/scalogno/core.scala#L189)
- [2.1 path example](src/test/scala/scalogno/core.scala#L289)
- [2.2 Higher-Order Relations as Higher-Order Functions](src/test/scala/scalogno/core.scala#L299)
- [2.2 reflexive transitive closure](src/test/scala/scalogno/core.scala#L318)
- [2.3 Object-Oriented Encapsulation](src/main/scala/scalogno/core.scala#L186)
- [2.3 example](src/test/scala/scalogno/core.scala#L272)
- [3.1 Designing Logic Engines for Meta-Programming (Fig 1)](src/main/scala/scalogno/engine.scala)
- [3.3 path rule def example](src/test/scala/scalogno/core.scala#L336)
- [3.3 path example](src/test/scala/scalogno/core.scala#L347)
- [3.4 Clause Reification as Controlled Side Effect](src/main/scala/scalogno/meta.scala#L62)

- [4 fib example](src/test/scala/scalogno/tabling.scala#L91)
- [4.2 Memoization with Symbolic State Transitions](src/main/scala/scalogno/tabling.scala)
- [4.3 Example: Tabled Graph Evaluation](src/test/scala/scalogno/tabling.scala#L133)
- [4.3 example](src/test/scala/scalogno/tabling.scala#L192)
- [4.4 Definite Clause Grammar (DFG)](src/test/scala/scalogno/tabling.scala#L6)
- [4.4 example](src/test/scala/scalogno/tabling.scala#L28)

Beyond APLAS:

- the [all](https://github.com/namin/scalogno/tree/all) branch adds an SMT solver as a backend, and combines it with tabling too. Work remains to refactor the combination into composable modules, and ... find a killer app beyond shortest paths. :)
