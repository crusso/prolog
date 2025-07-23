import Array "mo:base/Array";
import Buffer "mo:base/Buffer";
import HashMap "mo:base/HashMap";
import Iter "mo:base/Iter";
import Text "mo:base/Text";
import Option "mo:base/Option";
import Debug "mo:base/Debug";
import Nat "mo:base/Nat";

actor PrologInterpreter {
    
    // Define Prolog terms
    public type Term = {
        #Variable: Text;
        #Atom: Text;
        #Compound: {
            functor: Text;
            args: [Term];
        };
    };
    
    // Define Prolog clauses (facts and rules)
    public type Clause = {
        head: Term;
        body: ?[Term]; // None for facts, Some([terms]) for rules
    };
    
    // Substitution map for unification
    public type Substitution = HashMap.HashMap<Text, Term>;
    
    // Knowledge base
    private var kb: Buffer.Buffer<Clause> = Buffer.Buffer<Clause>(0);
    
    // Helper function to create a new substitution
    private func newSubstitution(): Substitution {
        HashMap.HashMap<Text, Term>(0, Text.equal, Text.hash)
    };
    
    // Apply substitution to a term
    private func applySubstitution(term: Term, sub: Substitution): Term {
        switch (term) {
            case (#Variable(name)) {
                switch (sub.get(name)) {
                    case (?value) { applySubstitution(value, sub) };
                    case null { term };
                }
            };
            case (#Atom(_)) { term };
            case (#Compound({functor; args})) {
                #Compound({
                    functor = functor;
                    args = Array.map<Term, Term>(args, func(arg) = applySubstitution(arg, sub));
                })
            };
        }
    };
    
    // Check if a variable occurs in a term (occurs check)
    private func occursCheck(varName: Text, term: Term): Bool {
        switch (term) {
            case (#Variable(name)) { varName == name };
            case (#Atom(_)) { false };
            case (#Compound({args})) {
                Array.foldLeft<Term, Bool>(args, false, func(acc, arg) = acc or occursCheck(varName, arg))
            };
        }
    };
    
    // Unify two terms
    private func unify(term1: Term, term2: Term, sub: Substitution): ?Substitution {
        let t1 = applySubstitution(term1, sub);
        let t2 = applySubstitution(term2, sub);
        
        switch (t1, t2) {
            case (#Variable(name1), #Variable(name2)) {
                if (name1 == name2) { ?sub }
                else {
                    sub.put(name1, t2);
                    ?sub
                }
            };
            case (#Variable(name), other) {
                if (occursCheck(name, other)) { null }
                else {
                    sub.put(name, other);
                    ?sub
                }
            };
            case (other, #Variable(name)) {
                if (occursCheck(name, other)) { null }
                else {
                    sub.put(name, other);
                    ?sub
                }
            };
            case (#Atom(a1), #Atom(a2)) {
                if (a1 == a2) { ?sub } else { null }
            };
            case (#Compound({functor = f1; args = args1}), #Compound({functor = f2; args = args2})) {
                if (f1 != f2 or args1.size() != args2.size()) { null }
                else {
                    var currentSub = sub;
                    for (i in Iter.range(0, args1.size() - 1)) {
                        switch (unify(args1[i], args2[i], currentSub)) {
                            case (?newSub) { currentSub := newSub };
                            case null { return null };
                        }
                    };
                    ?currentSub
                }
            };
            case (_, _) { null };
        }
    };
    
    // Rename variables in a clause to avoid conflicts
    private func renameVariables(clause: Clause, suffix: Text): Clause {
        let varMap = HashMap.HashMap<Text, Text>(0, Text.equal, Text.hash);
        
        func renameInTerm(term: Term): Term {
            switch (term) {
                case (#Variable(name)) {
                    switch (varMap.get(name)) {
                        case (?newName) { #Variable(newName) };
                        case null {
                            let newName = name # suffix;
                            varMap.put(name, newName);
                            #Variable(newName)
                        };
                    }
                };
                case (#Atom(a)) { #Atom(a) };
                case (#Compound({functor; args})) {
                    #Compound({
                        functor = functor;
                        args = Array.map<Term, Term>(args, renameInTerm);
                    })
                };
            }
        };
        
        {
            head = renameInTerm(clause.head);
            body = switch (clause.body) {
                case (?terms) { ?Array.map<Term, Term>(terms, renameInTerm) };
                case null { null };
            };
        }
    };
    
    // Resolve a query using SLD resolution
    private func resolve(goals: [Term], sub: Substitution, depth: Nat): [Substitution] {
        if (depth > 50) return []; // Prevent infinite recursion
        
        if (goals.size() == 0) {
            return [sub]; // Success - no more goals
        };
        
        let goal = goals[0];
        let remainingGoals = Array.tabulate<Term>(goals.size() - 1, func(i) = goals[i + 1]);
        let results = Buffer.Buffer<Substitution>(0);
        
        var clauseIndex = 0;
        for (clause in kb.vals()) {
            let renamedClause = renameVariables(clause, "_" # Nat.toText(clauseIndex));
            clauseIndex += 1;
            
            switch (unify(goal, renamedClause.head, newSubstitution())) {
                case (?unifySub) {
                    // Combine substitutions
                    let combinedSub = newSubstitution();
                    for ((k, v) in sub.entries()) {
                        combinedSub.put(k, applySubstitution(v, unifySub));
                    };
                    for ((k, v) in unifySub.entries()) {
                        combinedSub.put(k, v);
                    };
                    
                    let newGoals = switch (renamedClause.body) {
                        case (?bodyTerms) {
                            Array.append<Term>(bodyTerms, remainingGoals)
                        };
                        case null { remainingGoals };
                    };
                    
                    let subResults = resolve(newGoals, combinedSub, depth + 1);
                    for (result in subResults.vals()) {
                        results.add(result);
                    };
                };
                case null { /* Unification failed, try next clause */ };
            }
        };
        
        Buffer.toArray(results)
    };
    
    // Public API functions
    
    // Add a fact to the knowledge base
    private func addFact(head: Term): () {
        kb.add({head = head; body = null});
    };
    
    // Add a rule to the knowledge base
    private func addRule(head: Term, body: [Term]): () {
        kb.add({head = head; body = ?body});
    };
    
    // Query the knowledge base
    private func query_(goal: Term): [Substitution] {
        resolve([goal], newSubstitution(), 0)
    };
    
    // Clear the knowledge base
    private func clear(): () {
        kb := Buffer.Buffer<Clause>(0);
    };
    
    // Get all clauses in the knowledge base
    private func getClauses(): [Clause] {
        Buffer.toArray(kb)
    };
    
    // Helper functions for creating terms
    private func atom(name: Text): Term {
        #Atom(name)
    };
    
    private func variable(name: Text): Term {
        #Variable(name)
    };
    
    private func compound(functor: Text, args: [Term]): Term {
        #Compound({functor = functor; args = args})
    };
    
    // Format term as string for display
    private func termToText(term: Term): Text {
        switch (term) {
            case (#Atom(name)) { name };
            case (#Variable(name)) { name };
            case (#Compound({functor; args})) {
                if (args.size() == 0) {
                    functor
                } else {
                    functor # "(" # 
                    Text.join(", ", Array.map<Term, Text>(args, termToText).vals()) # 
                    ")"
                }
            };
        }
    };
    
    // Format substitution as string for display
    private func substitutionToText(sub: Substitution): Text {
        let bindings = Buffer.Buffer<Text>(0);
        for ((var_name, value) in sub.entries()) {
            bindings.add(var_name # " = " # termToText(value));
        };
        "{" # Text.join(", ", bindings.vals()) # "}"
    };
    
    // Example usage and test functions
    public func runExample(): async Text {
        clear();
        
        // Add facts: parent(tom, bob), parent(bob, ann)
        addFact(compound("parent", [atom("tom"), atom("bob")]));
        addFact(compound("parent", [atom("bob"), atom("ann")]));
        
        // Add rule: grandparent(X, Z) :- parent(X, Y), parent(Y, Z)
        addRule(
            compound("grandparent", [variable("X"), variable("Z")]),
            [
                compound("parent", [variable("X"), variable("Y")]),
                compound("parent", [variable("Y"), variable("Z")])
            ]
        );
        
        // Query: grandparent(tom, Z)?
        let results = query_(compound("grandparent", [atom("tom"), variable("Z")]));
        
        var output = "Knowledge Base:\n";
        for (clause in getClauses().vals()) {
            output #= termToText(clause.head);
            switch (clause.body) {
                case (?body) {
                    output #= " :- " # Text.join(", ", Array.map<Term, Text>(body, termToText).vals());
                };
                case null { };
            };
            output #= "\n";
        };
        
        output #= "\nQuery: grandparent(tom, Z)?\n";
        output #= "Results:\n";
        
        if (results.size() == 0) {
            output #= "No solutions found.\n";
        } else {
            for (result in results.vals()) {
                output #= substitutionToText(result) # "\n";
            };
        };
        
        output
    };
}