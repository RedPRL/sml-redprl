#!/bin/sh
#
# Batch File Creator
#
# Arguments:
# $1 = SMLNJ runtime
# $2 = Directory of binaries and heap image
# $3 = Name of executable (e.g. celf)
cat > "$2/bin/$3" <<EOF
#! /bin/sh
exec "$1" @SMLcmdname=\$0 @SMLload="$2/bin/.heapimg" "\$@"
EOF
chmod a+x "$2/bin/$3"
