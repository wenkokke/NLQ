# Questions for Moortgat

## June 13th

  * How does one define an AB or Lambek grammar for aⁿbⁿ? Solved.

  * The Lambek calculus needs linear logic's & in order to get rid
    of all that silly "ambiguous definitions" machinery. Which means
    we also need to add & back into our linear logic fragment.


## March 26th

  * What is the gain from also having a structural box operator without
    any residuation rules? Perhaps investigate axioma for cut specified
    to diamond (or box).

  * How would one relate work in LG with the work in the corner working
    with constants (e.g. B and C) in Barker and Shan's NL_CL.

  * Create an axiomatisation for Baker and Shan's NL_CL in Agda.

  * Look at the types for quantifiers and see if there actually is a problem.

  * Because in the structured version of **LG** there are many proofs
    for every proof in **RM**, due to the gradient from unstructured to
    maximally structured translations of formulas, I am wondering what
    the benefit is of using **LG**. Does it net you better proof
    search? I hardly think so. All I can see is that it forces some
    residuation to take place before some introductions, but I think
    that **RM** already offers such guarantees, as you can hardly
    residuate an operator you have not introduced yet. *That's
    true. Not really a problem, though.*

  * Jeroen's code uses iterative deepening depth-first search to find
    proofs in **LG**, and I cannot find a piece of code responsible for
    determining the maximum search depth. Is there an algorithm which
    can be used to determine the maximum proof size, given a sequent?
    If not, it should be noted that Jeroen's code does not guarantee
    that there aren't any proofs for a certain sequent of a deeper
    depth. *Yes. Perhaps it doesn't.*

  * Should I submit my TYTLES paper anonymously? *Yes. Probably. And
    submit to the student session as well. And send an email asking if
    that's okay.*

  * What would be the preferred way of describing LG in a brief manner?


## March 17th

  * As mentioned in Bastenhof's thesis, in the presence of $A_{I+IV}$
    or $C_{I+IV}$ the four negations collapse into two and, in the
    presence of both $A_{I+IV}$ *and* $C_{I+IV}$ they collapse into
    one negation. Does this imply that classically negation and
    co-negation are equivalent?

    *Uhm...?*

  * Another point of note is that, when defined in terms of left and
    right (co-)implication, the negations can automatically interact
    with the postulated Grishin laws. However, when they are axiomatic
    operators instead, they cannot. Is it desirable to also postulate
    their interactions through the Grishin laws from a linguistic
    perspective -- if they are desirable from a linguistic perspective
    at all?

    *If they are desirable from a linguistic perspective at all then
    yes.*

  * How would one neatly add the units into the focused system **LG**?
    The suggested laws (see below) would work just fine for the
    residuation-monotonicity system, but when one involves structures
    as well, one needs to add the axioms at both levels, resulting in
    the adoption of not eight but *sixteen* axioms. In addition, the
    destructuring laws for units would have to be derived by throwing
    the unit out at a structural level, and then reintroducing it at a
    formula level.

    *The idea is to add the rules at a structural level, and then add
    structural rules for converting to logical rules. The inverse
    rules should follow from transitivity.*

## March 12th

  * *Symmetric Categorial Grammar* mentions a proof of transitivity for
    the Lambek Grishin calculus. However, this proof depends on an
    axiomatisation of LG. The questions that arise from this are:

      - Does this proof of transitivity still work with the new
        axiomatisation? (In the first case, where the cut formula with
        a connective $\#$ is introduced by a *logical* rule, it is no
        longer necessarily introduced directly by applications of
        $\#^L$ and $\#^R$. I'm guessing that I would need to use
        origin views, in the way that the residuation-monotonicity
        calculus does.)

        *It probably does. However, the proof becomes more complex,
        since it will now also require constructing a view in the
        "easy" case where the cut formula was introduced by a left and
        a right rule.*

      - Why was this change required? Especially since I believe that
        the polarity restriction that is put upon unfocusing is
        already maintained by the old left and right rules.

        *Yes. The change was made such that the logical calculus would
         only generate normal forms under CPS translation to linear logic.*

      - Does this proof of transitivity still work with the polarised
        axiomatisation? The proofs don't work "out of the box", so to
        speak.

        *It does not. It is also not entirely clear if Bastenhof has
        proved that **fLG** allows for cut elimination.*


  * Is there a normalisation procedure for LG (for either the focused,
    Goré-style calculus or the residuation-monotonicity calculus) to
    the focused, polarised, Goré-style calculus. This basically
    implies proving that:

    $$X \vdash [     A ]     \to Negative (A)$$
    $$X \vdash \cdot A \cdot \to Negative (A)$$
    $$[     A ]     \vdash X \to Positive (A)$$
    $$\cdot A \cdot \vdash X \to Positive (A)$$

    Or at least that for any proof of a judgement that *already*
    follows these polarities, there is a proof that maintains those
    requirements throughout.
    Or perhaps there is some normalisation to be done on types?
    However, it is very weird to put constraints on the types, and
    expect the systems to be equivalent, because it is easy to
    construct a judgement for which the above properties don't hold:

    $$\cdot \Diamond A \cdot \vdash \cdot \Diamond A \cdot$$

    So approaching this from a top-level certainly cannot be the
    answer.

    *A normalisation procedure from **LG** to **fLG** wouldn't
     necessarily make sense, because the restrictions in **fLG** are
     put on the *types*. Therefore, a normalisation procedure would
     have to alter/normalise the types and would, thereby, no longer
     be type-preserving. It remains to be seen whether or not **LG**
     and **fLG** are equally expressive when using only the structural
     judgements, but it should be relatively easy to show that there
     are focused judgements for which a proof exists in **LG** but not
     in **fLG**.*

  * How do the negations $_0\cdot$, $\cdot^0$, $_1\cdot$ and $\cdot^1$
    relate to regular negation in classical logic?

    *The negations $_0\cdot$ and $\cdot^0$ are defined in terms of
     left and right implication and a unit **0**. The co-negations
     $_1\cdot$ and $\cdot^1$ are defined in terms of left and right
     subtraction and a unit **1**. In the presence of either both the
     *I* and the *IV* Grishin commutativity laws or both the *I* and
     the *IV* Grishin associativity laws they collapse into two
     negations, and in the presence of all of these laws into one
     (which is odd, isnt' it---remember to ask about that this week).*

    *Another point to note here is that this approach requires units
     to be present in the logic, which is undesirable from a
     linguistic perspective (Bastenhof's thesis has a motivating
     example for this). This means that the (co-)negations are
     postulated instead.*

  * How do the Lambek systems which allow empty contexts work in the
    setting of Goré-style axiomatisations? Do we just add a series of
    axioms such as:

    $$X \vdash Y \leftrightarrow \mathbf{1} \otimes X \vdash Y$$
    $$X \vdash Y \leftrightarrow X \otimes \mathbf{1} \vdash Y$$
    $$X \vdash Y \leftrightarrow X \vdash \mathbf{0} \oplus Y$$
    $$X \vdash Y \leftrightarrow X \vdash Y \oplus \mathbf{0}$$

    How do these units relate to the negations discussed above?

    *As mentioned above, these units can be used to define the
    negations (in terms of left and right (co-)implication). The
    suggested axioms would also be enough to successfully add these
    negations to the residuation-monotonicity system for
    **LG**. However, they seem cumbersome for the focused systems for
    **LG** and **fLG**.*

  * It seems that the Grishin interaction principles are not even
    derivable (potentially not even admissible) in classical
    subtractive logic. What is the idea behind these interaction
    principles?

    *The principles for simultaneous (co-)residuation become derivable
     (apparently) when you allows both units and the law of the
     excluded middle. The details of this can be found in (the
     translated version of) Grishin's paper*


## Module structure

There are two axes along which I classify my logics. The first of
these is the axis of structure. In this axis, the different logics are
based upon the presence and absence of three axioms: *contraction*,
*weakening* and *exchange*. These axioms give us---respectively---the
ability to duplicate information, to forget information and to reorder
the values in our context.

This last axiom (of exchange) can be further taken apart into
*commutativity* and *associativity* of the context building
operator---usually `_,_`.

Usually the axis is presented as follows:

                        unrestricted
                           / || \
          (no contraction)/  ||  \(no weakening)
                         /   ||   \
                   affine    ||    relevant
                         \   ||   /
            (no weakening)\  ||  /(no contraction)
                           \ || /
                           linear
                           / || \
        (no commutativity)/  ||  \(no associativity)
                         /   ||   \
          non-commutative    ||    non-associative
                         \   ||   /
        (no associativity)\  ||  /(no commutativity)
                           \ || /
                           ordered

While there are technically other possibilities (by dropping exchange
before contraction and weakening) the presented logics are most
thoroughly studied.
However, for this paper, we will *only* deal with logics in the
*unrestricted*, *linear* and *ordered* categories.

The second axis is roughly spun by *intuitionistic* versus *classical*
logics.
