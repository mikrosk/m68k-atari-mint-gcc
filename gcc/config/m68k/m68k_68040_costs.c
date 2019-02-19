#include "config.h"
#include "system.h"
#include "coretypes.h"
#include "backend.h"
#include "cfghooks.h"
#include "tree.h"
#include "rtl.h"

/**
 * This function also calculates the "fetch effective address" costs.
 */
bool
m68k_68040_costs (rtx x, machine_mode mode, int outer_code, int opno,
		  int *total, bool speed)
{
  int code = GET_CODE(x);
  int total2 = 0;
  switch (code)
    {
    case CALL:
      *total = 3;
      return true;
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
      return m68k_68040_costs (XEXP(x, 0), mode, code, 0, total, speed);
    case CONST:
      {
	rtx a = XEXP(x, 0);
	if (GET_CODE(a) == PLUS)
	  {
	    rtx b = XEXP(a, 0);
	    rtx c = XEXP(a, 1);
	    if (GET_CODE(b) == SYMBOL_REF)
	      {
		*total = 1;
		return true;
	      }
	    *total = 3;
	    return true;
	  }
      }
      break;
    case LABEL_REF:
    case SYMBOL_REF:
      *total = 1;
      return true;
    case CONST_INT:
      *total = 1;
      return true;
    case CONST_DOUBLE:
      *total = GET_MODE_SIZE(mode) > 4 ? 2 : 1;
      return true;
    case POST_INC:
      *total = 0;
      return true;
    case PRE_DEC:
      *total = 0;
      return true;
    case REG:
    case SUBREG:
    case STRICT_LOW_PART:
    case PC:
      *total = 0;
      return true;
    case SIGN_EXTRACT:
    case ZERO_EXTRACT:
      m68k_68040_costs (XEXP(x, 0), mode, code, 0, total, speed);
      *total += 5;
      return true;
    case TRUNCATE:
    case ZERO_EXTEND:
      *total = 1;
      return true;
    case NOT:
    case NEG:
    case SIGN_EXTEND:
      *total = 1;
      return true;
    case UDIV:
      *total = GET_MODE_SIZE(mode) > 2 ? 44 : 27;
      return true;
    case MOD:
    case DIV:
      *total = GET_MODE_SIZE(mode) > 2 ? 44 : 27;
      return true;
    case MEM:
      {
	rtx a = XEXP(x, 0);
	if (REG_P(a))
	  {
	    *total = 0;
	    return true;
	  }
	if (GET_CODE(a) == POST_INC)
	  {
	    *total = 0;
	    return true;
	  }
	if (GET_CODE(a) == PRE_DEC)
	  {
	    *total = 0;
	    return true;
	  }
	if (GET_CODE(a) == PLUS)
	  {
	    rtx b = XEXP(a, 0);
	    rtx c = XEXP(a, 1);
	    if (REG_P(b) && GET_CODE(c) == CONST_INT)
	      {
		*total = 0;
		return true;
	      }
	    if (REG_P(b) && REG_P(c))
	      {
		*total = 1;
		return true;
	      }
	  }
	*total = 3;
	return true;
      }
      break;
    case SET:
      {
	rtx dst = XEXP(x, 0);
	rtx src = XEXP(x, 1);

	if (GET_CODE(dst) == CC0)
	  return m68k_68040_costs (src, GET_MODE(XEXP(src,0)), CC0, 0, total,
				   speed);

	if (REG_P(dst))
	  {
	    // handle moveq
	    if (REGNO(dst) < 8 && GET_CODE(src) == CONST_INT)
	      {
		int ival = INTVAL(src);
		if (ival >= -128 && ival <= 127)
		  {
		    *total = 0;
		    return true;
		  }
	      }

	    // ADDQ / SUBQ
	    if (GET_CODE(src) == PLUS || GET_CODE(src) == MINUS)
	      {
		rtx a = XEXP(src, 0);
		rtx b = XEXP(src, 1);
		if (REGNO(a) == REGNO(dst) && REG_P(a) && GET_CODE(b) == CONST_INT && UINTVAL(b) <= 8)
		  {
		    *total = 0;
		    return true;
		  }
	      }
	  }
	if (m68k_68040_costs (src, mode, code, 1 /* yes 1 */, total, speed)
	    && m68k_68040_costs (dst, mode, code, 1, &total2, speed))
	  {
	    *total += total2;
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
	if (m68k_68040_costs (dst, mode, code, 0, total, speed)
	    && m68k_68040_costs (src, mode, code, 1, &total2, speed))
	  {
	    *total += total2;
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
		return true;
	      }
	  }
	*total += 1;
	return true;
      }
      break;
    case MULT:
      {
	/* umul, smul or call to __mulsi3? */
	rtx dst = XEXP(x, 0);
	rtx src = XEXP(x, 1);

	/* if there is an extended HImode, mul.w might be a candidate. */
	if (GET_CODE (dst) == ZERO_EXTEND || GET_CODE (dst) == SIGN_EXTEND)
	  {
	    *total = 0;
	    mode = HImode;
	    dst = XEXP(dst, 0);
	  }
	if (m68k_68040_costs (dst, mode, code, 0, total, speed)
	    && m68k_68040_costs (src, mode, code, 1, &total2, speed))
	  {
	    *total += total2 + 20;
	    return true;
	  }
      }
      break;
    case COMPARE:
      {
	rtx a = XEXP(x, 0);
	rtx b = XEXP(x, 1);
	if (REG_P(a))
	  {
	    if (GET_CODE(b) == CONST_INT && INTVAL(b) == 0)
	      {
		*total = 1;
		return true;
	      }
	    m68k_68040_costs (b, mode, code, 1, total, speed);
	    *total + 1;
	    return true;
	  }
	if (m68k_68040_costs (a, mode, code, 0, total, speed)
	    && m68k_68040_costs (b, mode, code, 1, &total2, speed))
	  {
	    *total += total2 + 1;
	    return true;
	  }
      }
      break;
    case IF_THEN_ELSE:
      *total = 3;
      return true;
    case FLOAT:
    case FLOAT_TRUNCATE:
    case FIX:
      // maybe check for 68881?
      *total = 2;
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
