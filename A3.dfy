ghost function reverse_sequence<T>(s: seq<T>): seq<T> {
    if |s| == 0 then [] else reverse_sequence(s[1..]) + [s[0]]
}

class Stack<T(0)> {

    ghost var Elements: seq<T>
    ghost const max: nat
    ghost var Repr: set<object>

    var size: nat
    var stack: array<T>

    ghost predicate Valid()
        reads this, Repr
        ensures Valid() ==> this in Repr && |Elements| <= max
    {
        // Preventing aliasing
        this in Repr &&
        stack in Repr &&
        // Abstraction relation
        |Elements| <= max &&
        |Elements| == size &&
        max == stack.Length &&
        reverse_sequence(Elements) == stack[..size]
    }

    constructor (max: nat)
        ensures Valid() && fresh(Repr)
        ensures Elements == [] && this.max == max
    {
        this.max := max;
        Elements := [];
        stack := new T[max];
        size := 0;
        Repr := {this, stack};
    }
       
    predicate IsEmpty() 
        requires Valid()
        reads Repr
        ensures Valid()
        ensures IsEmpty() <==> |Elements| == 0
        ensures !IsEmpty() <==> |Elements| != 0
    {
        size == 0
    }

    method Push(v: T)
        requires Valid() && |Elements| < max
        modifies Repr
        ensures Valid() && fresh(Repr - old(Repr))
        ensures Elements == [v] + old(Elements)
        ensures |Elements| == old(|Elements|) + 1
    {
        stack[size] := v;
        size := size + 1;
        Elements := [v] + Elements;
    }

    method Pop() returns (v: T)
        requires Valid()
        requires !IsEmpty()
        modifies Repr
        ensures Valid() && fresh(Repr - old(Repr))
        ensures Elements == old(Elements[1..])
        ensures |Elements| == old(|Elements|) - 1
        ensures v == old(Elements[0])
    {
        size := size - 1;
        v := stack[size];
        Elements := Elements[1..];
    }
}

class Queue<T(0)> {

    // abstract state
    ghost var Elements: seq<T>
    ghost const max: nat
    ghost var Repr: set<object>

    // concrete state
    var stack1: Stack<T>
    var stack2: Stack<T>

    ghost predicate Valid()
        reads this, Repr
        ensures Valid() ==> this in Repr && |Elements| <= max
    {
        // Aliasing
        this in Repr &&
        (
            stack1 in Repr &&
            stack1.Repr <= Repr &&
            this !in stack1.Repr
        ) &&
        (
            stack2 in Repr &&
            stack2.Repr <= Repr &&
            this !in stack2.Repr
        ) &&
        stack1.Valid() && stack2.Valid() &&
        stack1.Repr !! stack2.Repr &&
        // Abstract relation
        |Elements| <= max &&
        Elements == stack1.Elements + reverse_sequence(stack2.Elements) &&
        |Elements| == |stack1.Elements| + |stack2.Elements| &&
        max == stack1.max &&
        max == stack2.max
    }


    constructor (max: nat)
        ensures Valid() && fresh(Repr)
        ensures Elements == [] && this.max == max
    {
        Elements := [];
        this.max := max;
        stack1 := new Stack<T>(max);
        stack2 := new Stack<T>(max);
        new;
        Repr := {this, stack1, stack2} + stack1.Repr + stack2.Repr;
    }

    method Add(v: T)
        requires Valid() && |Elements| < max
        modifies Repr
        ensures Valid() && fresh(Repr - old(Repr))
        ensures Elements == [v] + old(Elements)
    {
        Elements := [v] + Elements;
        stack1.Push(v);
        Repr := Repr + stack1.Repr;
    }
    
    method Remove() returns (v:T)
        requires Valid() && |Elements| > 0
        modifies Repr
        ensures Valid() && fresh(Repr - old(Repr))
        ensures Elements == old(Elements[..|Elements|-1])
        ensures v == old(Elements[|Elements|- 1])
    {
        assert Elements == old(Elements);
        if stack2.IsEmpty() {
            var temp: T;
            ghost var test: T;
            while !stack1.IsEmpty()
                decreases |stack1.Elements|
                invariant |Elements| == old(|Elements|)
                invariant |stack2.Elements| <= |Elements|
                invariant Elements == old(Elements)[|stack2.Elements|..] + old(Elements)[..|stack2.Elements|]
                invariant Elements == stack1.Elements + reverse_sequence(stack2.Elements)
                invariant Valid()
                invariant fresh(Repr - old(Repr))
                invariant stack1.IsEmpty() ==> Elements == reverse_sequence(stack2.Elements) && !stack2.IsEmpty()
            {
                temp := stack1.Pop();
                stack2.Push(temp);
                Elements := Elements[1..] + [Elements[0]];
                Repr := Repr + stack1.Repr + stack2.Repr;
            }
        }
            assert Elements == old(Elements);
            assert Elements == stack1.Elements + reverse_sequence(stack2.Elements);
            v := stack2.Pop();
            assert v == old(Elements[|Elements|- 1]);
            Repr := Repr + stack2.Repr + stack1.Repr;
    }
}