class Stack<T(0)> {

    constructor (max: nat)
       
    predicate IsEmpty() 

    method Push(v: T)

    method Pop() returns (v: T)
}

class Queue<T(0)> {

    constructor (max: nat)

    method Add(v: T)
    
    method Remove() returns (v:T)
}