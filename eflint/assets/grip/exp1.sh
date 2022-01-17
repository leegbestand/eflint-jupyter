#!/bin/bash

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"

$DIR/../../dist/build/flint-simulation/flint-simulation $DIR/spec.frames $DIR/exp1.refine $DIR/exp1.initial $1 $2

