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
        requires Valid() && !IsEmpty()
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
        requires |stack1.Elements| + |stack2.Elements| > 0
        modifies Repr
        ensures Valid() && fresh(Repr - old(Repr))
        ensures Elements == old(Elements[..|Elements|-1])
        ensures v == old(Elements[|Elements|- 1])
    {
        if stack2.IsEmpty() {
            var temp: T;
            while !stack1.IsEmpty()
                decreases |stack1.Elements|
                invariant Elements == old(Elements)
                invariant Elements == stack1.Elements + reverse_sequence(stack2.Elements)
                invariant Valid()
                invariant fresh(Repr - old(Repr))
            {
                temp := stack1.Pop();
                stack2.Push(temp);
                Repr := Repr + stack1.Repr + stack2.Repr;
            }
        }
        v := stack2.Pop();

        Elements := Elements[..|Elements| - 1];
        Repr := Repr + stack2.Repr + stack1.Repr;
    }
}

method Main() {
    var t: nat;

    t := 10;



    var s1 := new Stack<int>(5);
    s1.Push(1);
    s1.Push(2);
    s1.Push(3);


    var check: seq<int> := [1,2,3];
    var check2: seq<int> := [3,2,1];

    assert s1.Elements == reverse_sequence(check);
    assert s1.Elements == check2;

    var len := 3;
    // while len != 0
    // invariant s1.Repr == old(s1.Repr)
    // {
    //     var b := s1.Pop();
    //     print("5");
    //     len := len - 1;
    // }


    var a := new Stack<int>(5);
    assert a.IsEmpty() == true;
    a.Push(5);
    assert a.IsEmpty() == false;
    a.Push(10);
    assert a.IsEmpty() == false;
    a.Push(15);

    var v1 := a.Pop();
    assert v1 == 15;
    var v2 := a.Pop();
    assert v2 == 10;
    var v3 := a.Pop();
    assert v3 == 5;

    a.Push(6);
    var v4 := a.Pop();
    assert a.IsEmpty() == true;
    assert v4 == 6;
}
