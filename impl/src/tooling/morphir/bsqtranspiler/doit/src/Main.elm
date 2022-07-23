
module Main exposing (..)

import Html exposing (..)

import BSQRuntime exposing(..)
import BSQMain exposing(..)

main =
    if (BSQRuntime.real_one /= BSQRuntime.real_zero) then
        text "Hello World"
    else
        text "Nope"

