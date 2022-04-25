module Morphir.Example.App.App exposing (..)

import Morphir.Example.App.Analytics exposing (..)
import Morphir.Example.App.BusinessTerms exposing (..)
import Morphir.Example.App.Forecast exposing (..)
import Morphir.Example.App.Rentals exposing (..)
import Morphir.Example.App.Winds exposing (..)


main : Forecast -> CurrentInventory -> ExistingReservations -> ReservationQuantity -> CanceledQuantity -> PendingReturns -> RequestedQuantity -> AllowPartials -> Result Reason ReservationQuantity
main forecast inventory reservations reservationQuantity canceledQuantity returns requestedQuantity allowPartials =
    let
        windCategory : WindCategory
        windCategory =
            categorizeWindForForecast forecast

        estimatedReservations : ProbableReservations
        estimatedReservations =
            probableReservations reservationQuantity canceledQuantity reservations
    in
    decide windCategory forecast.shortForcast inventory estimatedReservations returns requestedQuantity allowPartials


categorizeWindForForecast : Forecast -> WindCategory
categorizeWindForForecast forecast =
    let
        windCategory : WindCategory
        windCategory =
            categorizeWind forecast.windSpeed.max
    in
    windCategory
