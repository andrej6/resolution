# Parser design specification:

The purpose of the parser is to read from an input file and construct corresponding ASTs.
The input file will contain propositional logic expressions, propositional logic 
expressions in Conjunctive Normal Form, and resolution clauses.

A propositional logic expression will comprise only atomic literals and propositional
logic operators.

A resolution clause represents a disjunction of literals and negations of literals 


## Text Representations of Clauses

In the text file, each clause will be represented using a text label, followed
by a list of literals enclosed in curly brackets, followed by a parenthesized list of 
labels. Each literal must be either a pure literal or a negation of a literal.




label: {Literal, Literal, ~Literal} (Label, Label)

