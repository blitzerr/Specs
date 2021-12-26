---- MODULE SimpleScheduler ----
\* A simple scheduler is in control of resoures and. The resources are system constants and so are
\* the clients we want to work with. 
EXTENDS TLC, FiniteSets

VARIABLES allocatedResources, requestedResources
CONSTANTS Clients, Resources
ASSUME IsFiniteSet(Resources)
----------------------------------------------------------------------------------------------------
TypeInvariant == 
    \* The allocated resources is a functions with domain as the client and the range as the
    \* possible resourcds it can be allocated. Since there is no restrictions to what a client can
    \* request and what it can be granted, the range is the powerset of resources.
    \* Note that -> instead of |-> is used and therefore allocatedResources belongs to all such
    \* functions whose domain is the client and the range is powerset of resources.
    /\ allocatedResources \in [Clients -> SUBSET Resources]
    /\ requestedResources \in [Clients -> SUBSET Resources]

\* Symmetry == Permutations(Clients) \cup  Permutations(Resources)

\* an ease of use definition that gives the available resources at a given point of time. A resource
\* that is not allocated to any client is available
available == Resources \ (UNION {allocatedResources[c]: c \in Clients})
----------------------------------------------------------------------------------------------------
\* Now we define the allowed operation by our simple scheduler.
\* We should support these operations:
\* - Request: Client requesting a set of resources.
\*      An operator always starts with the enabling condition. A client can ask for resources if
\*      - The requested resources is a non-empty set.
\*      - An for simplicity, let's say we let a client ask for resources one shot and only when it
\*          has Reurned all previously allocated resources. This means that
\*          allocatedResources[client] and requestedResources[client] are both empty sets.
Request(c, R) == /\ R /= {} /\ allocatedResources[c] = {} /\ requestedResources[c] = {} \* enabling conds
                 /\ requestedResources' = [requestedResources EXCEPT ![c] = R]
                 \* Resources are reqeusted but will be allocated as part of the allocation operator
                 \* and hence the UNCHNAGED marker.
                 /\ UNCHANGED allocatedResources


                      


\* - Return: CLient returns a subset of the resources that it was allocated.
\*      Enabling condition: A return is only allowed if the resouces being retured is a non-empty
\*               set, the client was allocated the resorce. Although resources are requested one
\*              shot but for an efficient system, a client must return the resources as it is done
\*              with them and is no longer going to need them for their completion. Think, two phase
\*              commit where in the shrinking phase, you should no longer acquire new locks and must
\*              start to return/unlock locks as woth in their respective critical section is done.
Return(c, R) == /\ R /= {} /\ R \subseteq allocatedResources[c]
                /\ allocatedResources' = [allocatedResources EXCEPT ![c] = @ \ R]
                /\ UNCHANGED requestedResources
    
\* - Allocate: The system granting requested resources to a client
\*      Enabling condition:
\*              - the resources being allocated are available
\*              - They are in the set of requested resoures by the client.
Allocate(c, R) == /\ R /= {} /\ R \subseteq available \intersect requestedResources[c]
                  /\ allocatedResources' = [allocatedResources EXCEPT ![c] = @ \cup R]
                  /\ requestedResources' = [requestedResources EXCEPT ![c] = @ \ R]
----------------------------------------------------------------------------------------------------
\* Transitions

Init == /\ allocatedResources = [c \in Clients |-> {}]
        /\ requestedResources = [c \in Clients |-> {}]

\* For any client, as each client takes these steps independent of each other, it can either request
\* for resource, or it can work with the granted resource or it can try to return a granted resource.
Next == \E c \in Clients, R \in SUBSET Resources:
            Request(c, R) \/ Allocate(c, R) \/ Return(c, R)
vars == <<allocatedResources, requestedResources>>
----------------------------------------------------------------------------------------------------
\* Specification
SimpleScheduler == 
    /\ Init
    /\ [] [Next]_vars
    \* Weak fairness property is that a clinet returns the resource that it is granted.
    /\ \A c \in Clients: WF_vars(Return(c, allocatedResources[c]))
    \* A client that requests for resources is eventually grated that.
    /\ \A c \in Clients: SF_vars(\E R \in SUBSET  Resources: Allocate(c, R))
----------------------------------------------------------------------------------------------------
\* No two clients can own the same resource at the same time.
Safety == \A c1, c2 \in Clients: c1 /= c2 => allocatedResources[c1] \intersect allocatedResources[c2] = {}

\* All requested resources by all clients are eventually allocated.
Liveness == \A c \in Clients, r \in Resources: r \in requestedResources[c] ~> r\in allocatedResources[c]
---------------------------------------------------------------------------------------------------- 
THEOREM  SimpleScheduler => []TypeInvariant
THEOREM SimpleScheduler => []Safety
THEOREM SimpleScheduler => Liveness
====
