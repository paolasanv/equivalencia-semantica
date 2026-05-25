# Equivalencia semántica

## Semántica y Verificación 2026-2

### Por: Hazel Torres Nava, Leslie Paola Sánchez Victoria

En teoría de lenguajes de programación, las semánticas proporcionan mecanismos formales para describir el significado de los programas más allá de su estructura sintáctica. Dependiendo del enfoque --operacional, denotativo o axiomático-- se modelan distintos aspectos del comportamiento computacional, tales como la ejecución paso a paso, la interpretación matemática o las propiedades verificables del programa. En este contexto surge naturalmente la noción de equivalencia de programas: determinar bajo qué criterios dos programas pueden considerarse semánticamente indistinguibles.


Para introducir la noción de equivalencia de programas, se desarrolla la semántica del lenguaje de programación imperativo miniatura Comm [1]. Este lenguaje contiene construcciones básicas como asignaciones, composición secuencial, condicionales y ciclos while.

La sintaxis abstracta de Comm se define inductivamente como sigue. 

```text
<AExp> ::= <Nat>
    | <Id>
    | <AExpr> + <AExpr>
    | <AExpr> - <AExpr>
    | <AExpr> * <AExpr>

<BExp> ::= true
    | false
    | <BExp> and <BExp> 
    | not <BExp> 
    | <AExpr> < <AExpr>
    | <AExpr> = <AExpr>

<Comm> ::= skip
    | new <Id> := <Aexp> in <Comm>
    | print <AExp>
    | <Id> := <Aexp>
    | <Comm> ; <Comm>
    | if <BExp> then <Comm> else <Comm> end
    | while <BExp> do <Comm> end
```

El objetivo es demostrar la equivalencia entre distintos programas del lenguaje Comm utilizando las tres formas de especificar la semántica dinámica: semántica operacional, semántica denotativa y semántica axiomática.

Lo anterior se desarrolla con el apoyo del asistente de pruebas Rocq, que sirve como herramienta para la formalización y verificación de las semánticas antes mencionadas.




[1] A. Bauer. The programming languages zoo. Programming Languages Zoo. [Online]. Available: https://plzoo.andrej.com/language/comm.html