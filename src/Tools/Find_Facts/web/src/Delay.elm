{- Author: Fabian Huch, TU München

Simple delayed events.
-}
module Delay exposing (Model, empty, Delay, later, now, cancel, update)


import Dict exposing (Dict)
import Process
import Task


{- model to count invocations -}

type Model = Model (Dict String Int)

empty: Model
empty = Model Dict.empty


{- invoking delays -}

type alias Delay msg = {name: String, delay: Float, event: Cmd msg}

later: (Delay msg -> msg) -> Model -> Delay msg -> (Model, Cmd msg)
later msg (Model model) delay =
  let
    num = model |> Dict.get delay.name |> Maybe.withDefault 0
    model1 = model |> Dict.insert delay.name (num + 1)
    cmd = Task.perform (always (msg delay)) (Process.sleep delay.delay)
  in (Model model1, cmd)

now: Model -> Delay msg -> (Model, Cmd msg)
now (Model model) delay = (model |> Dict.remove delay.name |> Model, delay.event)

cancel: Model -> Delay msg -> Model
cancel (Model model) delay = model |> Dict.remove delay.name |> Model


{- update -}

update: Model -> Delay msg -> (Model, Cmd msg)
update (Model model) delay =
  case Dict.get delay.name model of
    Nothing -> (Model model, Cmd.none)
    Just num ->
      if num > 1
        then (model |> Dict.insert delay.name (num - 1) |> Model, Cmd.none)
        else (model |> Dict.remove delay.name |> Model, delay.event)
