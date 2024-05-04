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
        this in Repr && stack in Repr &&
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
    // {
    //     if stack2.IsEmpty() {
    //         var temp: T;
    //         assert stack1.Repr !! stack2.Repr;
    //         while !stack1.IsEmpty()
    //             decreases |stack1.Elements|
    //             invariant stack1.Valid() && stack2.Valid() // This fixes the !stack1.IsEmpty() not meeting preconditions in loop gaurd
    //             // Why does this happen?? Queue.Valid() includes stack1.Valid() and stack2.Valid() and the IsEmpty() requires and ensures Valid() for stack

    //             invariant Elements == old(Elements) // Adding this resolves modifies clause error with v := stack2.Pop();
    //             invariant |Elements| == |stack1.Elements| + |stack2.Elements| // Adding this resolves modifies clause error with v := stack2.Pop();
    //             invariant Elements == stack1.Elements + reverse_sequence(stack2.Elements) // Adding this resolves modifies clause error with v := stack2.Pop();
    //             // invariant stack1.Valid() && stack2.Valid() // Having these in there might violate modifies clause with v := stack2.Pop()???
    //         {
    //             // assert stack1.Repr !! stack2.Repr; // This is not holding for some reason
    //             temp := stack1.Pop(); // With code currently, these are not holding - violate context's modifies clause
    //             Repr := Repr + stack1.Repr;
    //             stack2.Push(temp); // With code currently, these are not holding - violate context's modifies clause
    //             Repr := Repr + stack2.Repr;
    //         }
    //     }
    //     v := stack2.Pop();

    //     Elements := Elements[..|Elements| - 1];
    //     Repr := Repr + stack2.Repr + stack1.Repr;
    // }
}

// method Main() {
//     var check := new Queue<int>(5);

//     assert |check.Elements| == 0;

//     check.Add(5);
//     check.Add(10);
//     check.Add(10);
//     check.Add(10);
//     check.Add(10);

//     var r1 := check.Remove();
//     assert r1 == 5;

//     check.Add(10);

//     var r2 := check.Remove();
//     assert r2 == 10;

// }

method Main() {
    var check: seq<int>;

    check := [1,2];

    assert check == [1,2];

    assert check == [1,2];
    var check1 := reverse_sequence(check);
    assert check1 == [2,1];

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
