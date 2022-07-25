
module Main exposing (..)

import Html exposing (..)

import BSQMain exposing(..)

main =
    if (BSQMain.real_one /= BSQMain.real_zero) then
        text "Hello World"
    else
        text "Nope"

