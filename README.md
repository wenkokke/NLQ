### Things that need to be in the paper

- While I could have taken an approach such as [citation needed],
  abstracting over connectives and proving properties in general based
  on properties of the connectives, I chose not to. The reason for
  this is that such systems are much more complex, and therefore
  harder to mutate. In addition, it is very hard for them to not
  become syntactically unwieldy. Perhaps if all this is over I'll look
  into adding a surface logic on top of such a system, as Gergo Érdi
  does in *Simply Typed Lambda Calculus in Agda, Without Shortcuts*.


### To-Do

- think of a name for the logic now called "subtractive";
- move the reifications for types and judgements into "subtractive";
- create a new logic which separates the two contexts (types and co-types);
- try to limit the structural rules for the types (not for the co-types).
