#!/bin/bash

[C
qstat | grep jawolfe | sed 's/^\(.......\).*/\1/' | xargs -n 1 qdel
