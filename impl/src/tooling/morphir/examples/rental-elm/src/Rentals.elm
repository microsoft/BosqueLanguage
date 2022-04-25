module Morphir.Example.App.Rentals exposing (..)

import Morphir.Example.App.BusinessTerms exposing (..)
import Morphir.Example.App.Forecast exposing (..)
import Morphir.Example.App.Winds exposing (..)


decide : WindCategory -> ForecastDetail -> CurrentInventory -> ProbableReservations -> PendingReturns -> RequestedQuantity -> AllowPartials -> Result Reason ReservationQuantity
decide windCategory forecastDetail inventory probableReservations returns requestedQuantity allowPartials =
    let
        isClosed : Bool
        isClosed = (windCategory == DangerousWinds) || (forecastDetail == Thunderstorms)

        availability : Availability
        availability =
            inventory - probableReservations + returns
    in
    if isClosed then
        Err ClosedDueToConditions

    else if availability == 0 then
        Err InsufficientAvailability

    else if requestedQuantity <= availability then
        Ok requestedQuantity

    else if allowPartials then
        Ok availability

    else
        Err InsufficientAvailability
