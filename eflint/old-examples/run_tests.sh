#!/bin/bash

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"

if [ -z $1 ];
  then SEARCH_DIR=$DIR
  else SEARCH_DIR=$1
fi

run_test() {
  IFS='.' read -ra PARTS <<< "$1"
  if [[ 5 == ${#PARTS[@]} ]]
    then
      TEST_DIR="$( dirname "${PARTS[0]}.frames" )"
      out=$($DIR/../dist/build/flint-simulation/flint-simulation "${PARTS[0]}.frames" "$TEST_DIR/${PARTS[1]}.refine" "$TEST_DIR/${PARTS[2]}.initial" $1)
      if [[ $out ]]
        then  echo $1:;
              echo "$out";
      fi
  fi
}
export -f run_test
export DIR
find $SEARCH_DIR -type f \( -iname \*.pos -o -iname \*.neg \) | xargs -n1 -I{} bash -c 'run_test "$@"' _ {} 
