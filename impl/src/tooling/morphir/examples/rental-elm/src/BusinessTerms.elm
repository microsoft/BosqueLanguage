module Morphir.Example.App.BusinessTerms exposing (..)

{-| The number of items in stock.
-}


type alias CurrentInventory =
    Int


{-| The quantity granted for a reservation. Depending on availability, this might be less than the requested amount.
-}
type alias ReservationQuantity =
    Int


{-| The quantity of existing reservations.
-}
type alias ExistingReservations =
    Int


{-| The quantity of items in use that should be returned.
-}
type alias PendingReturns =
    Int


{-| The quantity of reservations that will probably be fulfilled. It is calculated based on the ratio of reservations
that are canceled before fulfillment.
-}
type alias ProbableReservations =
    Int


{-| The quantity of items in a reservation that are canceled before fulfillment.
-}
type alias CanceledQuantity =
    Int


{-| The ratio of cancelations vs reservations.
-}
type alias CancelationRatio =
    Float


{-| The quantity of items available for rent taking into account how the business wants to consider
current inventory, reservations, and probably cancelations.
-}
type alias Availability =
    Int


{-| Expertise level of renters. Important for deciding whether conditions are safe enough to rent.
-}
type ExpertiseLevel
    = Novice
    | Intermediate
    | Expert



-- Request specific


{-| The quantity of items in the reservation request.
-}
type alias RequestedQuantity =
    Int


{-| States whether the requester is OK with receiving fewer items or will only accept the quantity requested.
-}
type alias AllowPartials =
    Bool


{-| Reason codes for rejecting a reservation request.
-}
type Reason
    = InsufficientAvailability
    | ClosedDueToConditions
