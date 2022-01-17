#!/bin/bash

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"

$DIR/../../dist/build/flint-simulation/flint-simulation $DIR/parentship.frames $DIR/parentship.refine $DIR/parentship.initial $1 $2
