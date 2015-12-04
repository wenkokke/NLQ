####1
Today we're going to talk about the way that type theory can be used
in natural language processing. This is usually called "categorial
grammar" or "type-logical grammar". Now, since this topic isn't really
a part of the CS programme here in Utrecht, I'm gonna start now out by
giving you a quick introduction to the field... now!

---

####2
Okay, so the part of NLP that we're going to discuss is called NLU for
natural language understanding. And behind me, you can see what I've
titled an "abstract natural language understanding pipeline". Now, an
NLU pipeline is a function from sentences, which are strings, into
formulas in _higher-order_ logic -- and, we'll get into defining what
that means in a minute. Natural language understanding is a whole
bunch of work, so it's generally subdivided into some smaller, more
manageable problems -- morphological or word-form analysis, lexical
analysis, etc. To the left you see these phases, or functions. And to
the right you see what they do.

The morphological function lemmatises words -- that means, get's them
in some sort of base form, like with see-saw -- and adds some
information. For instance, foxes is reduced to the base form fox, and
we add the marker PL to show that we mean the plural.
The lexical function just looks up the part-of-speech tags -- or types
-- of the words. For instance, Mary is an NP -- a noun phrase -- and
see is a transitive verb -- meaning a verb with two arguments.

Then, interesting things start to happen. The syntactic function takes
the string of words (and information) and turns it into a tree -- or
parse tree, which is sort of like an abstract syntax tree for natural
language.
And the semantic function takes this tree, and compiles it to some
expression in higher order logic.
The eh, pragmatic function is listed here for completeness, but we
can't really list an output here, since pragmatics is all about using
contextual information -- body language, intonation, conversational
history and stuff... and we don't have any of that.

Now, the part of this pipeline that we're going to address today --
and that type theory is especially suited at dealing with -- is the
semantic phase. Ideally, we'd want to cover the syntactic phase as
well -- without parsing we can hardly call our field grammar -- and we
might come back to that near the end of the talk. But the current
state of affair in the field is that in most publications, people are
preoccupied with accepting the right parse trees, and translating them
to the right semantics. And that's what we'll be doing today.

Now sometimes we might simplify things somewhat. For instance, we
might forget about that whole "past" marker up there, since it's
rather trivial to insert. Other times we may make gross
oversimplifications. But don't worry, there'll be a pedagogical reason
for that, and at the end of this talk we should have a clear
understanding of how the semantic phase can be implemented, and of
some things it can and cannot do.

Oh. It might be worthwhile to spend just a second talking about that
sentence meaning right there, while it's still on screen. Because it's
all complicated-looking. So what it says is "there is a p", and
that `p` is a predicate or a (characteristic function of a) set,
"there is a p, such that for all x for which p(x)", which you can read
as "for all x in that set", "x is a fox, and in the past Mary saw
x". So there's a set of things, and they're foxes, and Mary saw
them.

It's not that simple, right, because this doesn't guarantee that she
saw two or more foxes -- and you would be kinda upset if I said
this, knowing that she saw exactly zero foxes. And this would also be
true if Mary saw all foxes in p, but she saw them at different events
in the past. But all in all, it's pretty good.

---

####3
Okay, so the first thing we're going to do is to give a definition of
"higher-order logic". What you see behind me is the simply-typed
lambda calculus. Pretty much the simplest possible type system, so I
hope you've all seen this before. A set of types as the antecedent,
variables are things that are in that set, and you have two rules for
lambda abstraction and function application.

Now, linguists usually make two changes to this calculus. First,
there's only two basic types: **e** and and **t**, for *entity* and
*truth-value* or boolean. Secondly, they assume that any logical
constant they need is available as a constant in this language. So,
for instance, implication (written as a horseshoe here) is available
as a function from **tttt**. It's important to see here that both the
universal quantifier and the existential quantifier are there, with a
whole bunch of types. They're **(et)t**, **((et)t)t**, etc. Any form
of **(xt)t**. So we're basically pretending to have polymorphic types
here.

Oh, and while we should technically write sometime like "the constant
'forall' applied to a lambda abstraction", we're just gonna ignore
that, and use the traditional notation from logic.

---

####4
Now, we can use this calculus as it is to express the meanings of our
example sentence -- and, yes, this is a little short and hard to read,
but there's no way the full thing would fit on a slide. It's just
important to note that the antecedent is, in order, "mary saw
foxes" everywhere. We've just put the words in the sentence in the
antecedent, basically the same as assuming that we some sort of
meanings for these words.
Then below the proof, I'm showing just the end sequent in full. So we
can see that, given the antecedent or sentence "mary saw foxes", we
can get the meaning `((saw foxes) mary)`, which is what we
want. Kinda. It's good enough for now, at least.

---

But because this is just lambda calculus, we can also pick the words
the other way around. We just choose to apply 'saw' to 'mary' first,
then to 'foxes'.

---

Or we can just choose to apply it to 'mary' twice.

---

Or forget about 'mary' altogether.

So clearly, we can use the lambda calculus to express the meanings
that we're after. But we also said something about "only accepting the
right trees, and assigning the right meanings to those trees", and
this is where lambda calculus isn't really enough anymore.

So what we're gonna do is this: we're gonna keep this in mind as
"perfectly fine as our semantic calculus", but we're going to look for
a new calculus. And in this new calculus, when we put our sentence or
syntax tree in the antecedent, we only want to be able to derive the
*right* meaning.

Now, a lot of the problems we have with our semantic calculus had to
do with the fact that our antecedent was implicitly a set. We can't
enforce an order on the words; we can refer to a word any number of
times we want; and we can forget about them. So what I'm gonna do is
make all of the set structure explicit, and work from there.

---

####5
First we're gonna need some new thing to be our antecedent, since
we're rejecting sets and all. So we're going to define the structure
you see behind me: it can be empty, it can be just a type, and we have
this binary operator, the product, which can build a new structure out
of two structures. So basically what we have here is a possibly empty
binary tree.

---

Second, we just copy over the rules we had before, with a few little
changes. Instead of having an axiom where we have to show that our A
is in the antecedent, we just have the identity. And then in the
application rule -- and any binary rule -- we split the
antecedent. This is all pretty common; Gentzen does it.

---

And third, we add five new rules. And these rules pretty much add back
the structure of a set. We have contraction, which allows us to copy
things -- use them more then once. We have weakening, which allows us
to forget about things. And then we have the three rules below -- unit
elimination, commutativity and associativity. All together, they say
that our structure can be empty, and order doesn't matter.

It's somewhat easy to see -- though we're not going to get into the
proof -- that this calculus is equivalent to the previous one! I mean,
all the structure of a set is there, right?

---

####6
But in this new calculus, we can see that all the examples we just
showed, are in fact *different* -- I've added some colour so that you
can see what's going on; red is mary, green is foxes. And when we look
--

---

---

---


good news! -- the
examples that we considered wrong use *more* structural rules. And our
the right meaning uses only one structural rule -- commutativity --
and when we examine more examples, we find that it uses it in very
consistent places.

So this is what we're gonna do: we're gonna throw out all the
structural rules, and then create a... eh, it's best if you just see.

---

So we've changed some things. First off, simple things. We moved away
from using **e** and **t** as types. Those have a semantic feel to
it. We've moved to using 'sentence', 'noun' and 'noun phrase' as
atomic types. And we've remove the ability for the structure to be
empty -- that doesn't make any sense anymore.

Then, big changes! We've thrown out *all* structural rules! But as we
saw some slides back, our correct answer still needed an application
of commutativity when we used only one implication! So what we've
done, is we've made *two* implications. They're pronounced "under" and
"over", and the mnemonic is that the argument type is always *under*
the slash. And so we get *two* copies of the rules for introduction
and elimination; with one, the implication takes its argument from the
left, and with the other from the right!

---

####8
And with this calculus, we can *only* derive the example that we
thought of as correct!

But what meaning will we ascribe to this? I mean, this isn't lambda
calculus anymore. And this new calculus is all about *sentence*
structure... so how can we pretend that we can express semantics in
this restricted calculus?

---

####9

So we're going to add one last element to the mix: we're going to
translate this syntactic calculus back to our semantic calculus! And
through that translation, we'll get a meaning for the sentence
structure... and then we can just fill in the word meanings using the
regular lambda calculus!

So in the box, you see the translation on types -- the translation
function is written *asterisk*, by the way. Sentences become truth
values, nouns become predicates, and noun phrases become entities. And
then both implications -- no surprises there -- translate back to
regular implication.

And if you look at the proofs -- they're all straight forward
too. Axiom to axiom, introduction to introduction, elimination to
elimination. But in the case of *one* of the implications, you see
the commutativity sneak back in! We've just managed to restrict it to
exactly the case we need.

---

####10
And now, with this translation, we can assign a meaning to our
sentence again. And now we only get the meaning we want!

---

####11
And all that you've seen up to here is due to Lambek. The entire setup
is known as categorial grammar, and the syntactic calculus is known as
non-associative Lambek calculus -- because Lambek, in his first
publication on this, left associativity in. It's not entirely as he
presented it, though, for he used sequent calculus, which has all
kinds of nice properties. But this is where we deviate from his work.

---

####12
And move on to some more recent work, by Belnap, Gore and Michael --
who is hopefully sitting right there...

So I mentioned Lambek originally used a sequent calculus. But we're
going to use a display calculus. Which generalises the sequent
calculus, and has some nice advantages over it. The most important
aspect of display calculus is that *if* something is a display
calculus (there's 7 easily checkable and one slightly less easily
checkable properties that your inference rules have to obey, but we're
not going to go into that) then there is a generic proof of cut
elimination. This is important, because if you don't have the cut
rule, you're not dealing with a logic (which is supposed to be a
reflexive, transitive relation) and if you *do* have it, but cannot
eliminate it, then there's usually something wrong with your
logic... or at least, you lose the second nice property, which is...

...that in a sequent calculus, every logical rule is supposed to
eliminate a connective. And so, by taking the desired end sequent, and
attempting to apply every rule on it (naive backward-chaining search),
you're guaranteed that either you'll run out of rules to apply, or
you'll run out of connectives. So you have very easy to implement,
decidable *and* complete proof search!

We didn't really have that with the system we introduced before! Or at
least, not this easily!

And last, it's known that sequent calculus proofs don't map one-to-one
to natural deduction proofs (the thing we were doing before). In fact,
it's more of a many-to-one thing. So there's some unwanted ambiguity
in such systems. In display calculus, however, you can use some very
nice techniques, developed for the Lambek-Grishin calculus by
Bastenhof and Moortgat, to restrict this. We're not really going to go
into this in this talk though, because it's not necessary to discuss
my work, and -- when removed --- simplifies the presentation of my
logical system a lot. If you want to see it, check my thesis.

---

So finally, there it is, the display calculus version. One of the
requirements of display calculus is that every logical connective also
has a structural equivalent, and that *both sides* of the turnstile
are contexts (that's a weird thing in intuitionistic logic anyway). So
we've added "under" and "over" as structural connectives as well. And
we add these dots so that we can distinguish between the two.

The reason we're splitting into two contexts -- positive and negative
-- is... difficult[^todo]. So if we have some time near the end, I can get
into that. But for now, simply said, it's to keep all the formulas on
the right side of the turnstile.

[^todo]: Perhaps *some* explanation of display calculus would be in order?

---

At any rate, we now have two left rules, which eliminate implications,
and two right rules, which communicate between the logical and the
structural versions of the implications.

---

And last we have residuation rules, which describe the relationship between
the implications and the product. Note that these are *structural*
rules, there's no formulas in them. So apparently, this is some
structure which was still hidden in the natural deduction version of
this logic.

Now these are rules that can be used two ways. So if you're worried
that perhaps these will make our proof search algorithm "just try
everything" fail, you're right. But they cause *loops*, meaning we
return to the exact same sequent we'd visited before. So we can simply
insert a check for loops, and our algorithm will work again.

---

####13
And so, back to our running example. It looks pretty foreign, and we
don't really know what semantics to assign it right away, whereas the
previous one was obvious. Because lambda calculus is natural deduction
system, and we switched away from that. So we could translate this
into our previous semantic calculus. In fact, the two are
equivalent. But we're not gonna do that. We're gonna do what we did
before: translate it to our semantic calculus, in order to get a meaning.

---

####14
Now this is where the split between positive and negative comes in
handy: we're going to translate positive structures as structures, and
negative structures as types. Everything pretty much maps as expected
-- products to products, implications to implications, etc. The only
problem is that negative contexts can *contain* positive contexts, so
we're going to map those to product *types*. We should extend our
semantic calculus to deal with products, but I don't want to bore you,
and since we're not going to actually see this happen, it's not really
worth the effort.

---

Anyway, the left rules are the most complicated, so let's get them out
of the way. It translates to this jumbled mess. You'll see the result
in a second.

---

But the right rules simply translate to the identity, as we identify
the structural and logical versions of implication in the translation.

---

And the residuation rules translate to implication elimination --
albeit a somewhat restricted form -- and introduction.

---

And the same for the second pair of residuation rules. And again, you
see the commutativity sneak back in!

---

####15
And using this translation, we can assign the following semantics to
our derivation. Note that I've put the translated proof up there, for
your benefit.

---

But fortunately, this proof can be reduced. So if we normalise it, we
end up with the following familiar proof!

---

####16
Okay. Let's take a step back. We have a semantic calculus, a syntactic
calculus, a decidable algorithm for proof search in the syntactic
calculus, and a translation from the syntactic calculus to the
semantic.

That means we have enough to actually build our semantic function!

But a natural question is, how far can we get with the semantic
function we have now... We have functions, and we can apply adjacent
functions. So if it's all adjacent composition, then we should be able
to treat all of natural language...

---

####17
Now there's tons of examples that people talk about when they want to
argue that it's not just adjacent composition. Here's a few. In "I
walked the dog" the word 'I' seems to be some way of referring to the
speaker. So if I said it, it'd refer to me. If you said it, it'd refer
to you.

---

Or -- I'm not a huge fan of dogs -- if I said "I walked the damned
dog", the 'damned' doesn't really seem to interact with the sentence
at all. It conveys some sort of side-meaning that you hate the stupid
dog, but... okay, an easy way to see how this doesn't affect the
meaning. Imagine you're a dog person -- or if you're a dog person, eh,
good on you, anyway -- imagine you like the dog, and I say "There. I
walked the damned dog." You can't go "No, you didn't. The dog is nice!"

---

Or a last, simpler example. If you say "John left. He was whistling."
then the 'he' can refer back to John, but if we put them the other way
around, 'he' -- obviously -- cannot refer to John. So there's some
sort of ordering constraint here.

But we're functional programmers. And we're using the lambda
calculus. This is our turf. So it should be easy to see that we can
add one little thing... to take care of all these phenomena.

Monads.

---

'I' then obviously is a reader monad.

---

And 'damned' is a writer monad.

---

And references, pronouns and the like, give you exactly this behaviour
if you implement them using a state monad.

Now, I'm not going to go to the length of implementing this. Instead
I'm going to give you one of the few examples where this cannot be
used. It's known as quantifier raising, and we've seen it before.

---

####18
Our running example! Mary saw foxes! For this entire time, we've
treated foxes like an entity, and that was ridiculous. Pretending
there was a single entity, somewhere out there in the world, that
represented exactly that set of foxes that Mary saw! The problem here
is that the meaning of 'foxes' is all over the place. Basically
everything up to the conjunction is in the meaning of 'foxes', and the
'x' nested all the way to the right is too. Let's get a little bit of
a simpler example here, though.

---

So "John loves everyone". It's a little bit easier to see the need for
the universal quantifier here. I mean, it's right there in the word
*every*one.

So somehow, that every moves up to put that quantifier in place, and
then moves back down to put the variable x in place.

Now, some of you may know of continuations, and the continuation
monad. Basically, it's a monad in which an expression can bind the
context around it. So in this case, 'everyone' could grab the 'john
loves _' around it, wrap the quantifier around it, and insert the
variable. And this is a wonderful solution. But it has a few
problems. And it's main problem is that it's all implemented in the
lambda calculus, and so it's strongly normalising... but in language,
we find...

---

####19
...scope ambiguity! What this means is that if we have multiple
quantifiers in our sentence, then the meaning of that sentence becomes
ambiguous, and precisely ambiguous due to the order in which the
quantifiers take scope.

Take this sentence for example. "A professor talked to every student."
Now this can mean that there is a professor, and that *one* professor
talked to *every* student. That's the first meaning. The second
meaning is that for *every* student, there is a professor who talked
to them.

Now, if you were to try this through the continuation monad, you would
have to separately introduce some means of non-determinism into the
calculus. Now, the original Lambek calculus had a means for this: it
allowed you to give a word multiple definitions, and so you could
define *every transitive verb* in two ways, one which gave you the
surface scope, and one which gave you the inverse scope. And you'd
also have to define *ditransitive verbs* -- verbs with three arguments
-- in *three* different ways. But even if you did that -- and at that
point you're already doing something that isn't very elegant. Even if
you did that, you can only control in which *order* the quantifiers
raise. You cannot control where they raise to. In fact, in the
standard continuation monad, you always bind the context of an
expression all the way up to the top. But in natural language, we
find...

---

####20
...scope *islands*. That means, certain nodes in the syntax tree that
you simply cannot move past. For instance, take "Mary said everyone
left". The meaning that we want is "mary said _" and then nested in
there something that's a sentence.
But if we allowed everyone to take scope all the way at the top, we'd
get the meaning to the right. And that meaning is ridiculous. Instead
of meaning that there was a single speech act, in which Mary said that
"everyone left", we'd get a separate speech act for *everyone*. "Mary
said Bill left, Mary said Sue left, Mary said Alice left, Mary
said..." etc. Mary'd be doing a whole to more saying, is what I mean.

---

####21
So we've talked about the continuation monad while we were going over
the data, but there's a number of different things we can do. Since
we can give words multiple meanings, we can give quantifiers a whole
bunch of different types. For instance, that first type takes scope as
a subject. The second one as a direct object. But then we'd need one
for indirect object. And two for objects which are also under a
prepositional phrase, and *many more*. So really, that's... not an
option.

Secondly, we have continuation monads. Now this approach was advocated
by Barker for a while. But as we've seen, it has too many limitation.

Lastly, there's a thing called a delimited continuation. These are
continuations that are delimitable -- duh. So what you can do is wrap
your expression in a so-called reset operation, and then when you try
to grab the context, it will only grab the context up to the nearest
reset operation. Now, these are awesome. But they would be at least as
inelegant as my solution. And probably far more so. First of all,
they're still mostly implemented in the lambda calculus, so you have
the problem of having to find a way to introduce ambiguity. And
secondly, they don't actually form a monad. They form what is known as
an indexed monad, which is a monad with *three* parameters instead of
one. What the other two are will be a lot clearer later on, but the
least you can take from this is that we'd *have to* make *some*
changes to the syntactic calculus...

...and in fact, the solution that we end up choosing is very similar
to what this would look like.

---

####22
