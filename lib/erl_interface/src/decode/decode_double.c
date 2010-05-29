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
#include "eidef.h"
#include "eiext.h"
#include "putget.h"

int ei_decode_double(const char *buf, int *index, double *p)
{
  const char *s = buf + *index;
  const char *s0 = s;
  double f;

  switch (get8(s)) {
    case ERL_FLOAT_EXT:
      if (sscanf(s, "%lf", &f) != 1) return -1;
      s += 31;
      break;
    case NEW_FLOAT_EXT: {
      /* IEEE 754 decoder */
      const unsigned int bits    = 64;
      const unsigned int expbits = 11;
      /* below subtract 1 for sign bit */
      const unsigned int significantbits = bits - expbits - 1;
      unsigned long long i = get64be(s);
      long long shift;
      unsigned bias;

      if (!p)
        break;
      else if (i == 0)
        f = 0.0;
      else {
        /* get the significant */
        f  = (i & ((1LL << significantbits)-1)); /* mask */
        f /= (1LL << significantbits);           /* convert back to float */
        f += 1.0f;                               /* add the one back on */

        /* get the exponent */
        bias  = (1 << (expbits-1)) - 1;
        shift = ((i >> significantbits) & ((1LL << expbits)-1)) - bias;
        while (shift > 0) { f *= 2.0; shift--; }
        while (shift < 0) { f /= 2.0; shift++; }

        /* signness */
        f *= (i >> (bits-1)) & 1 ? -1.0: 1.0;
      }
      break;
    }
    default:
      return -1;
  }

  if (p) *p = f;
  *index += s-s0; 
  return 0; 
}
