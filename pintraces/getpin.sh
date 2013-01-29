#!/usr/bin/env sh

# $Id: getpin.sh 6361 2012-06-20 16:00:42Z edmcman $
# Download and extract Pin

set -x

# check if pin dir exists first

wget 'http://software.intel.com/sites/landingpage/pintool/downloads/pin-2.11-49306-gcc.3.4.6-ia32_intel64-linux.tar.gz' -O - | tar -xvz -C ..
rm -rf ../pin
mv ../pin-* ../pin
#make
