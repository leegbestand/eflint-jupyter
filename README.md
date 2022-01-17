# eflint-jupyter


## Dependencies
- zeromq development libraries (see [https://zeromq.org/download/])
- Jupyter (pip3 install jupyter)
- Stack (see [https://docs.haskellstack.org/en/stable/README/#how-to-install])

## Installing
Install the kernel file as follows
```sh
jupyter kernelspec install --user eflint_kernel
```
now build eflint-jupyter
```sh
stack install
```
now you can run jupyter by executing
```
jupyter notebook
```
this opens your browser with jupyter that supports eFLINT kernels.