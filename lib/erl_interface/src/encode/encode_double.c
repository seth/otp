/*
 * %CopyrightBegin%
 * 
 * Copyright Ericsson AB 1998-2009. All Rights Reserved.
 * 
 * The contents of this file are subject to the Erlang Public License,
 * Version 1.1, (the "License"); you may not use this file except in
 * compliance with the License. You should have received a copy of the
 * Erlang Public License along with this software. If not, it can be
 * retrieved online at http://www.erlang.org/.
 * 
 * Software distributed under the License is distributed on an "AS IS"
 * basis, WITHOUT WARRANTY OF ANY KIND, either express or implied. See
 * the License for the specific language governing rights and limitations
 * under the License.
 * 
 * %CopyrightEnd%
 */
#include <stdio.h>
#include <string.h>
#include "eidef.h"
#include "eiext.h"
#include "putget.h"

int ei_encode_double(char *buf, int *index, double p)
{
  char *s = buf + *index;
  char *s0 = s;

  if (!buf)
    s += 9;
  else {
    /* use IEEE 754 format */
    const unsigned int  bits    = 64;
    const unsigned int  expbits = 11;
    /* below subtract 1 for sign bit */
    const unsigned int  significantbits = bits - expbits - 1;
    long long           sign, exp, significant;
    long double         norm;
    int                 shift;

    put8(s, NEW_FLOAT_EXT);
    memset(s, 0, 8);

    if (p == 0.0)
      s += 8;
    else {
      /* check sign and begin normalization */
      if (p < 0) { sign = 1; norm = -p; }
      else       { sign = 0; norm =  p; }

      /* get the normalized form of p and track the exponent */
      shift = 0;
      while(norm >= 2.0) { norm /= 2.0; shift++; }
      while(norm < 1.0)  { norm *= 2.0; shift--; }
      norm = norm - 1.0;

      /* calculate the binary form (non-float) of the significant data */
      significant = (long long) ( norm * ((1LL << significantbits) + 0.5f) );

      /* get the biased exponent */
      exp = shift + ((1 << (expbits-1)) - 1); /* shift + bias */

      /* get the final answer */
      exp = (sign << (bits-1)) | (exp << (bits-expbits-1)) | significant;
      put64be(s, exp);
    }
  }

  *index += s-s0; 

  return 0; 
}

