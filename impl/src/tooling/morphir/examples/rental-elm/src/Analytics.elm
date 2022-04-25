module Morphir.Example.App.Analytics exposing (..)

import Morphir.Example.App.BusinessTerms exposing (..)


{-| Calculates the probable reservations by applying the historical cancelation ratio to current reservations.
-}
probableReservations : ReservationQuantity -> CanceledQuantity -> ReservationQuantity -> ProbableReservations
probableReservations averageReservationRequests averageCancelations currentReservationCount =
    let
        cancelationRatio : CancelationRatio
        cancelationRatio =
            toFloat averageCancelations / toFloat averageReservationRequests

        result : ProbableReservations
        result =
            ceiling (toFloat currentReservationCount * (1.0 - cancelationRatio))
    in
    result
