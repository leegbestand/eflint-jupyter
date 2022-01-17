FROM haskell 

RUN mkdir /tmp/eflint-project

WORKDIR /tmp/eflint-project

RUN cabal update 

COPY . .

RUN cabal install

RUN cp /root/.cabal/bin/eflint-server /usr/bin/eflint-server
RUN cp /root/.cabal/bin/eflint-repl /usr/bin/eflint-repl

RUN rm -rf /tmp/eflint-project
