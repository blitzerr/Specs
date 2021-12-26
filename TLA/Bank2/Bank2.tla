---- MODULE Bank2 ----
EXTENDS TLC, Naturals



(* https://www.learntla.com/introduction/example/ *)
(* This is a very simple banking example. There are two accounts and there are a configurable
numbers of accountants who are trying to parallelly withdraw and deposit money. The goal is to make
sure that we never let the balance. *)

CONSTANTS
    Withdrawls,  \* A set of all the amounts that can be withdrawn.
    Accountants, \*  A set of accountants that can paralley withdraw money.
    InitBalWithdrawAcc,
    InitBalDepositAcc

VARIABLES
    WithdrawAccBal,  \* The account from which money is withdrawn.
    DepositAccBal  \* The account to which the money is deposited

TotalBal == InitBalWithdrawAcc + InitBalDepositAcc

NoOverdraft == /\ WithdrawAccBal > 0
          /\ DepositAccBal > 0

Transfer(Accountant, Money) == /\ WithdrawAccBal >=Money
                               /\ WithdrawAccBal' = WithdrawAccBal - Money
                               /\ DepositAccBal' = DepositAccBal + Money
                               /\ PrintT(<<Accountant, " is withdrawing ", Money,
                                    "WithdrawAccBal:",
                                    WithdrawAccBal, " After: ", WithdrawAccBal'>>)

Init == /\ WithdrawAccBal = InitBalWithdrawAcc
        /\ DepositAccBal = InitBalDepositAcc

Next == \E accountant \in Accountants: \E withdrawl \in Withdrawls: Transfer(accountant, withdrawl)

Spec == Init /\ [][Next]_<<WithdrawAccBal, DepositAccBal>>

WealthConservationInvariant == WithdrawAccBal + DepositAccBal = TotalBal

THEOREM Spec => [](WealthConservationInvariant /\ NoOverdraft)

====