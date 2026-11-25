/**
 * Reliable Software
 * Masters Course on CSE
 * Department of Informatics
 * Faculty of Sciences
 * University of Lisbon
 * October, 2024
 * Antonia Lopes
 *
 * A property-based specification of a bank account with statement.
 *
 * The observers are Balance() and Statement(). 
 * They are pure functions, so that is
 * how they are defined (instead of being defined as methods)
 * The contracts of all methods are based on this function.
 * An abstract representation frame is used in order to 
 * not expose any representation details.
 *
 * The invariant is captured in predicate Valid().
 * Constructors establish the invariant.
 * All methods require the invariant and reestablish it in the end.
 */
 
 class BankAccountWithStatement {
    var balance: int 
    var transactions: array<int>
    var size: nat
    ghost var Repr: set<object>

    ghost predicate Valid ()
        reads this, Repr
    {
        this in Repr && transactions in Repr
        && transactions.Length >= 10
        && size <= transactions.Length
        && balance == sum(transactions[..size])    
        && balance >= 0
    }

    constructor ()
        ensures Valid() && fresh(Repr) 
        ensures Balance() == 0
        ensures Statement() == []
    {
        transactions, size := new int[10], 0;
        balance := 0;
        Repr := {this, transactions}; 
    }

    //observers

    function Balance () : int
        reads Repr
        requires Valid()
    { balance }

    function Statement () : seq<int>
        reads Repr
        requires Valid()
    {
        transactions[..size]
    }

    //mutators

    method Deposit (amount: nat)
        requires Valid()
        modifies Repr
        ensures Valid() && fresh (Repr - old(Repr))
        ensures Balance() == old(Balance()) + amount
        ensures Statement() == old(Statement()) + [amount]
    {
        if (size == transactions.Length){ 
            // resize
            var a := new int[2 * transactions.Length + 1];
            var i := 0;
            //this would be much simpler but did not work as the verifier got stuck
            //forall i | 0 <= i < size { a[i] := transactions[i]; }
            while (i < size)
                invariant Valid() &&  0 <= i <= size < a.Length
                invariant a[..i] == transactions[..i]
                invariant sum(a[..i]) == sum(transactions[..i])
                invariant balance == old(balance) &&  Repr == old(Repr)
                invariant transactions[..size] == old(transactions[..size])  
            {
                a[i] := transactions[i];
                i := i+1; 
            }
            transactions := a;
            Repr := Repr + {a};
        }
        transactions[size] := amount;
        size := size + 1;
        seqLengthMinusOne(transactions[..], size);
        balance := balance + amount;
    }
    lemma seqLengthMinusOne (s: seq<int>, n: nat)
        requires 0 < n <= |s|
        ensures s[..n - 1] == s[..n][..|s[..n]| - 1]
    {}

    method Withdraw (amount: nat)
        modifies Repr
        requires Valid()
        requires amount <= Balance()
        ensures Valid() && fresh(Repr-old(Repr))
        ensures Balance() == old(Balance()) - amount
        ensures Statement() == old(Statement()) + [0-amount]
    {
        if (size == transactions.Length){ 
            // resize
            var a := new int[2 * transactions.Length + 1];
            var i := 0;
            while (i < size)
                invariant Valid() && 0 <= i <= size < a.Length
                invariant a[..i] == transactions[..i]
                invariant sum(a[..i]) == sum(transactions[..i])
                invariant balance == old(balance) &&  Repr == old(Repr)
                invariant transactions[..size] == old(transactions[..size])  
            {
                a[i] := transactions[i];
                i := i+1; 
            }
            transactions := a;
            Repr := Repr + {a};
        } 
        transactions[size] := 0 - amount;
        size := size + 1;
        seqLengthMinusOne(transactions[..], size);
        balance := balance - amount;
    }

    // A method to return the statement as an array
    // just in case we want also to have this option
    method StatementM () returns (a: array<int>)
        requires Valid()
        ensures Valid() && fresh(a)
        ensures a[..] == Statement()
    {
        a := new int[size];
        forall i | 0 <= i < size { a[i] := transactions[i]; }
    }
}

//auxiliary function to sum the elements of a sequence
function sum (s: seq<int>) : int
{
        if s == [] then 0 else sum(s[..|s| - 1]) + s[|s| - 1]
}
