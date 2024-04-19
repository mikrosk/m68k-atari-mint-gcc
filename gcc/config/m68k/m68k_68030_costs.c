#include "config.h"
#include "system.h"
#include "coretypes.h"
#include "backend.h"
#include "cfghooks.h"
#include "tree.h"
#include "rtl.h"

/**
 * calculate costs for the 68030.
 * opno == 1: calculate as if dst is a register
 * opno == 0: calculate difference to register assignment
 */
bool
m68k_68030_costs (rtx x, machine_mode mode, int outer_code, int opno,
		  int *total, bool speed)
{
  int code = GET_CODE(x);
  int total2 = 0;
  *total = 0;
  switch (code)
    {
    case CALL:
      {
	rtx a = XEXP(x, 0);
	if (MEM_P(a))
	  {
	    rtx b = XEXP(a, 0);
	    if (REG_P(b) || GET_CODE(b) == PC)
	      {
		*total = 7;
      return true;
	      }
	    if (GET_CODE(b) == PLUS)
	      {
		if (REG_P(XEXP(b, 0)))
		  {
		    *total = 9;
		    return true;
		  }
	      }
	    else if (SYMBOL_REF_P(b) || GET_CODE(b) == CONST_INT)
	      {
		tree decl = SYMBOL_REF_DECL(b);

		*total = 7;
		return true;
	      }
	  }
	*total = 13;
	return true;
      }
    case NE:
    case EQ:
    case GE:
    case GT:
    case LE:
    case LT:
    case GEU:
    case GTU:
    case LEU:
    case LTU:
      return m68k_68030_costs (XEXP(x, 0), mode, code, 0, total, speed);
    case CONST:
      {
	rtx a = XEXP(x, 0);
	if (GET_CODE(a) == PLUS)
	  {
	    rtx b = XEXP(a, 0);
	    if (GET_CODE(b) == SYMBOL_REF || GET_CODE(b) == LABEL_REF)
	      {
		*total = GET_MODE_SIZE(mode) > 2 ? 5 : 4;
		return true;
	      }
	    *total = 7;
	    return true;
	  }
      }
      break;
    case LABEL_REF:
    case SYMBOL_REF:
      *total = GET_MODE_SIZE(mode) > 2 ? 5 : 3;
      return true;
    case CONST_INT:
      if (INTVAL(x) >= -128 && INTVAL(x) <= 127)
	*total = 1;
      else
	*total = GET_MODE_SIZE(mode) > 2 ? 4 : 2;
      return true;
    case CONST_DOUBLE:
      *total = GET_MODE_SIZE(mode) > 4 ? 8 : 4;
      return true;
    case POST_INC:
      *total = 0;
      return true;
    case PRE_DEC:
      *total = opno ? 0 : 2;
      return true;
    case REG:
    case PC:
    case SUBREG:
    case STRICT_LOW_PART:
    case NOT:
    case NEG:
      *total = 2;
      return true;
    case SIGN_EXTRACT:
    case ZERO_EXTRACT:
	  if (outer_code == COMPARE && GET_CODE (XEXP (x, 1)) == CONST_INT && INTVAL (XEXP (x, 1)) == 1)
		*total = 2;
	  else;
		*total = 10;
	  return true;
    case TRUNCATE:
    case ZERO_EXTEND:
      *total = GET_MODE_SIZE(mode) > 2 ? 4 : 2;
      return true;
    case SIGN_EXTEND:
      *total = 4;
      return true;
    case UDIV:
      *total = GET_MODE_SIZE(mode) > 2 ? 79 : 44;
      return true;
    case MOD:
    case DIV:
      *total = GET_MODE_SIZE(mode) > 2 ? 90 : 56;
      return true;
    case MEM:
      {
	rtx a = XEXP(x, 0);
	if (REG_P(a))
	  {
	    *total = opno ? 5 : 4;
	    if (REGNO(a) < 8)
	      *total += 5;
	    return true;
	  }
	if (GET_CODE(a) == POST_INC)
	  {
	    *total = opno ? 5 : 4;
	    return true;
	  }
	if (GET_CODE(a) == PRE_DEC)
	  {
	    *total = opno ? 6 : 5;
	    return true;
	  }
	if (GET_CODE(a) == SYMBOL_REF || GET_CODE(a) == LABEL_REF)
	  {
	    *total = opno ? 10 : 9;
	    return true;
	  }
	if (GET_CODE(a) == PLUS)
	  {
	    rtx b = XEXP(a, 0);
	    rtx c = XEXP(a, 1);
	    if (REG_P(b)
		&& (GET_CODE(c) == CONST_INT || GET_CODE(c) == SYMBOL_REF))
	      {
		*total = opno ? 7 : 5;
		if (REGNO(b) < 8)
		  *total += 5;
		return true;
	      }
	    if (REG_P(b) && REG_P(c))
	      {
		*total = opno ? 12 : 10;
		return true;
	      }
	  }
	*total = opno ? 15 : 13;
	return true;
      }
      break;
    case SET:
      {
	rtx dst = XEXP(x, 0);
	rtx src = XEXP(x, 1);
	if (REG_P(dst) || GET_CODE(dst) == CC0)
		  {
	    if (m68k_68030_costs (src, mode, code, 1, total, speed))
		    return true;
		  }
	else if (m68k_68030_costs (dst, mode, code, 0, total, speed)
	    && m68k_68030_costs (src, mode, code, 1, &total2, speed))
	  {
	    *total += total2 - 2;
	    return true;
	  }
      }
      break;
    case PLUS:
    case MINUS:
    case AND:
    case IOR:
    case XOR:
      {
	rtx dst = XEXP(x, 0);
	rtx src = XEXP(x, 1);
	if (m68k_68030_costs (dst, mode, code, 0, total, speed)
	    && m68k_68030_costs (src, mode, code, 1, &total2, speed))
	  {
	    *total += total2 + 2;
	    if (REG_P(dst))
	      *total -= REG_P(src) ? 4 : 2;
	    return true;
	  }
      }
      break;
    case ASHIFT:
    case ASHIFTRT:
    case LSHIFTRT:
      {
	rtx a = XEXP(x, 0);
	rtx b = XEXP(x, 1);
	if (REG_P(a))
	  {
	    if (GET_CODE(b) == CONST_INT)
	      {
		*total = 4;
		return true;
	      }
	  }
	*total = 6;
	if (CONST_INT_P(b))
	  {
	    int n = INTVAL(b);
	    if (n > 8)
	      *total += 6;
	  }
	return true;
      }
      break;
    case MULT:
      {
	/* umul, smul or call to __mulsi3? */
	rtx dst = XEXP(x, 0);
	rtx src = XEXP(x, 1);

	if (GET_CODE(src) == CONST_INT)
	  {
	    unsigned i = INTVAL(src);
	    int bits = 0, l = 0;
	    if (i > 0)
	      {
		if (GET_CODE (dst) == ZERO_EXTEND || REG_P(dst))
		  {
		    while (i)
		      {
			if (i & 1)
			  ++bits;
			i >>= 1;
		      }
		    // it's a shift
		    if (bits == 1 && REG_P(dst))
		      {
			*total = 4;
			return true;
		      }
		  }
		else
		  // SIGN_EXTEND
		  while (i || l)
		    {
		      if ((i & 1) != l)
			{
			  l = !l;
			  ++bits;
			}
		      i >>= 1;
		    }

		*total = 12 + bits;
		return true;
	      }
	  }

	*total = GET_MODE_SIZE(mode) > 2 ? 44 : 28;
	return true;
      }
      break;
    case COMPARE:
      {
	rtx a = XEXP(x, 0);
	rtx b = XEXP(x, 1);
	if (REG_P(a))
	  {
	    if (GET_CODE(b) == CONST_INT)
	      {
		*total = INTVAL(b) == 0 ? 0 : 1;
		return true;
	      }
	    m68k_68030_costs (b, mode, code, 1, total, speed);
	    *total += 2;
	    return true;
	  }
	if (m68k_68030_costs (a, mode, code, 0, total, speed))
	  {
	    if (GET_CODE(b) == CONST_INT && INTVAL(b) == 0)
	      return true;

	    if (m68k_68030_costs (b, mode, code, 1, &total2, speed))
	      {
	    *total += total2 + 2;
	    return true;
	  }
      }
      }
      break;
    case IF_THEN_ELSE:
      *total = 7;
      return true;
    case FLOAT:
    case FLOAT_TRUNCATE:
    case FIX:
      // maybe check for 68881?
      *total = 3;
      return true;
    case ASM_OPERANDS:
    case ASM_INPUT:
      return false;
    }
  *total = 1;
//  fprintf (stderr, "%d: ", outer_code);
//  debug_rtx (x);
  return true;
}
