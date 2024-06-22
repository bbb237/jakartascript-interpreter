When you start sbt in the root directory of the repository and execute the `run` command with one of the files in `testjs` as input, the expression in the file will be parsed into a value of type `Expr` (i.e., the Scala representation of the JavaScript subset that we are considering). 
The parsed expression is then passed to your implementation of the interpreter (the function `eval` defined in `hw12.scala`). For instance, to run your interpreter on the file `testjs/test01_arith.js`, you can execute the following command from the command line:

```bash
$ sbt "run testjs/test01_arith.js"
```

Alternatively, if you are already inside of the sbt shell, execute:

```
sbt:hw12> run testjs/test01_arith.js
```

If you add the option `-d` as additional argument to the run command, you will see some useful debug output, such as the pretty printed AST representation of the parsed input expression.

Alternatively, you can run the interpreter directly from inside the IDE. To do so, right-click the file `hw12.scala` and select "More Run/Debug" and then "Modify Run Configuration". You can provide the command line arguments to the interpreter in the text field labeled "Program arguments". Enter e.g. "testjs/test01_arith.js" in this field and click "OK". When you now right-click on the file `hw12.scala` and select "Run 'hw12'", then the interpreter will be executed with the specified command line arguments.

I suggest that you run your implementation on the provided JavaScript files once all the unit tests are passing.

In general, I strongly advise you to write your own additional unit tests and JavaScript test files to further increase your confidence that your implementation of the interpreter is correct.


### Debugging

As the complexity of your interpreter code increases over the next homework assignments, you will sooner or later start to introduce debugging output in your interpreter. In particular, you will probably want to pretty print the Scala representation of JavaScript expressions. There are two ways to pretty print Scala values `e` of type `Expr`. Use

* ```println(e.prettyJS)``` to print an expression `e` in concrete JavaScript syntax
* ```println(e)``` to print an expression `e` as an abstract syntax tree represented as a Scala algebraic data type

One other useful feature that the parser provides for helping with debugging is that it decorates every expression of the parsed JavaScript input file with the position (i.e. line and column number) from which it originated in the input file. Given a value `e` of type `Expr`, you can access the source code line and number with `e.pos.line` and `e.pos.column`, respectively. 
