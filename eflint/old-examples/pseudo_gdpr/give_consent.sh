#!/bin/bash

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"

$DIR/../../dist/build/flint-simulation/flint-simulation $DIR/spec.frames $DIR/telfort.refine $DIR/give_consent.initial $1 $2

