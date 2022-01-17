#!/bin/bash

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"

if [ -z $1 ];
  then SEARCH_DIR=$DIR/tests
fi

run_test() {
      out=$(cabal run -v0 eflint-repl "$1" -- --test-mode)
      if [[ $out ]]
        then  echo "$1";
              echo $out;
      fi
}
export -f run_test
export DIR
find $SEARCH_DIR -type f \( -iname \*.eflint \) | xargs -n1 -I{} bash -c 'run_test "$@"' _ {} 
