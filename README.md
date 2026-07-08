# Formalizing The Groupoid Model in Martin-Löf Type Theory

> Work in Progress: This project is currently under active development.

### Overview
The idea behind this code is to formalize the groupoid construction in the Martin-Löf identity type using Agda. A crucial aspect of this implementation is the use of the {-# OPTIONS --without-K #-} flag. This flag disables the Uniqueness of Identity Proofs (UIP) in Agda's kernel, allowing us to work naturally with the relevance of proofs, meaning multiple distinct proofs of identity can exist without collapsing into one.

### Induction Principle and Proof Styles
In type theory, it is common to describe a type by formation, introduction, induction, and computation rules. The induction rule (also known as the jRule or path induction in homotopy type theory) tells us what we need to give to produce the wanted type. The homotopy invariance tells us that, if we want to prove that a property C about x and y holds, it suffices to show (construct an evidence) for the case that x and y are equal and for the reflexive path (the constant path).

One key pedagogical aspect of this project is that it explicitly contrasts two different proof styles to show how path induction operates:
-   The Purist Approach: Dealing directly with the induction principle (the jRule) in the proofs. This demonstrates the true complexity and verbosity of building paths manually in type theory.
-   The Native Approach: Using Agda's built-in pattern matching mechanisms. This highlights how modern programming languages hide the underlying complexity to provide elegant and readable proofs.

### Groupoid Structure
A groupoid is a category in which every morphism has an inverse. To prove that the identity type has the same structure as a groupoid, we need to show that symmetry, transitivity, and associativity hold.
However, inspired by Hofmann and Streicher's model, this formalization goes a step further. Because we are working in a system without proof irrelevance, the proofs themselves become mathematical objects. Therefore, this repository also constructs "proofs about proofs" (paths between paths). It includes formalizations showing that the inverse of an inverse is the original path (sym-sym), and the cancellation of inverses (trans-right-inv, trans-left-inv).

### The Role of Proof Assistants (Bridging Math and Computation)
Why does this technology matter? The use of proof assistants like Agda suggests a profound change in how mathematics can be done, realizing Per Martin-Löf's dream of eliminating the barrier between constructive mathematics and computer programming.

In this framework, a theorem is a type, and proving it means constructing a term that inhabits this type. Because of the relevance of proofs, the specific inhabitant matters, transforming the proof itself into a first-class mathematical object that can be computed and inspected. Historically, the development of mathematics was largely driven by physics, which frequently demanded the creation of new mathematical tools to solve real-world problems. Today, however, computer science is demonstrating a different kind of influence. Through proof assistants and type theory, the intersection of computing and mathematics is doing more than just providing new problem-solving tools; it has the potential to reshape the very foundational concepts of how mathematics is formalized and understood.
