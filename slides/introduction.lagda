# Introduction

This is a difficult talk. We are going to talk about Agda. However,
Agda is code. And we all know from experience, talks where the slides
that are almost only code are either scary or boring or both. There's
never enough time to read and understand all the code in the slides,
and you'll also have the disadvantage that I'm talking while you're
trying to read.

Another thing is that what I'm talking about is "nothing new." I won't
be talking about new and interesting formalisms; I'll just be going
over a thing that most of you will have seen already. And I'll be
going over that... at length.

The description of this talk said I'd be explaining Agda first, and
then going into my talk, but life is short and so is this talk, so
I'll do both at the same time. My apologies to those who aren't here
yet because they figured they'd skip the first half.

Last disclaimer, I promise: This talk is a little bit more "applied
type theory" than it is "lexical semantics", because I won't be
talking about any lexical semantics today.

---

My goal for today will be to define two operators `✓` and `*` which
denote grammaticality and ungrammaticality, respectively. As opposed
to being based in native speaker competence, my operators will be
based on some given type-logical grammar. Any given type-logical
grammar.

The idea of these operators is that you can use them while writing a
paper, to make statements about a sentence's grammaticality, and while
compiling your paper, Agda will automatically check if your theory
agrees with what you've stated. So, for instance:

```
✓ "mary found a unicorn"
```

This being a semantics workshop, if we have time after that, we will
go into extending `✓` and defining `#`, to denote semantic well- or
ill-formedness.[^pound]


[^pound]: Right now, what `#` does is make a statement about whether
    or not your theory derives the *right* semantics. You can do
    this by: 1) giving me a list of all allowed interpretations
    in Agda; 2) giving me a model and a list of truth-values; 3)
    giving me a sentence which should have the same meaning.

    This isn't really what `#` is supposed to mean, though. So,
    for future work I'm thinking of extending this to a function
    which tries to inject {e,t}-typed lambda terms into a more
    strictly typed lambda calculus, and report on whether or not
    that works.

    For that, obviously, you would need to formalise your theory
    of semantics in Agda as well.
