# OneFile

OneFile is a Software Transactional Memory (STM) meant to make it easy to
implement lock-free and wait-free data structures. It is based on the paper
["OneFile: A Wait-free Persistent Transactional
Memory"](https://github.com/pramalhe/OneFile/blob/master/OneFile-2019.pdf)
by Ramalhete, Correia, Felber and Cohen.

This is a port to D of the original C++ implementation. Currently, only the
Wait-Free STM has been ported.

The port is not well tested yet, so expect some bugs. If one bites you,
please check the issue list. If it isn't there yet, please file the issue!

# See also
* [The original C++ implementation](https://github.com/pramalhe/OneFile)
