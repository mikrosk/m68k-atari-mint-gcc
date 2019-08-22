#include "config.h"
#include "system.h"
#include "coretypes.h"
#include "backend.h"
#include "cfghooks.h"
#include "tree.h"
#include "rtl.h"
#include "insn-modes.h"

/**
 * calculate costs for the 68080.
 * opno == 1: calculate as if dst is a register
 * opno == 0: calculate difference to register assignment
 */
bool
m68k_68080_costs (rtx x, machine_mode mode, int outer_code, int opno,
		  int *total, bool speed)
{
  int code = GET_CODE(x);
  int total2 = 0;
  *total = 0;
  switch (code)
    {
    case CALL:
      {
	*total = 8;
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
    case CONST:
      return m68k_68080_costs (XEXP(x, 0), mode, code, 0, total, speed);
    case LABEL_REF:
    case SYMBOL_REF:
      return true;
    case CONST_INT:
      if (outer_code == SET)
	{
	  int iv = INTVAL(x);
	  if (iv < -0x100 || iv > 0xff)
	    *total = 1;
	}
      return true;
    case CONST_DOUBLE:
      return true;
    case POST_INC:
      return true;
    case PRE_DEC:
      return true;
    case REG:
    case SUBREG:
    case STRICT_LOW_PART:
    case PC:
      return true;
    case SIGN_EXTRACT:
    case ZERO_EXTRACT:
      *total = 4;
      return true;
    case TRUNCATE:
    case ZERO_EXTEND:
      *total = 4;
      return true;
    case NOT:
    case NEG:
    case SIGN_EXTEND:
      *total = 4;
      return true;
    case UDIV:
      *total = 72;
      return true;
    case MOD:
    case DIV:
      *total = 72;
      return true;
    case MEM:
      {
	rtx a = XEXP(x, 0);
	if (REG_P(a))
	  {
	    *total = 4;
	    return true;
	  }
	if (GET_CODE(a) == POST_INC)
	  {
	    *total = 4;
	    return true;
	  }
	if (GET_CODE(a) == PRE_DEC)
	  {
	    *total = 4;
	    return true;
	  }
	if (GET_CODE(a) == PLUS)
	  {
	    rtx b = XEXP(a, 0);
	    rtx c = XEXP(a, 1);
	    if (REG_P(b) && (GET_CODE(c) == CONST_INT || GET_CODE(c) == SYMBOL_REF))
	      {
		*total = 5;
		return true;
	      }
	    if (REG_P(b) && REG_P(c))
	      {
		*total = 8;
		return true;
	      }
	  }
	*total = 20;
	return true;
      }
      break;
    case SET:
      {
	rtx dst = XEXP(x, 0);
	rtx src = XEXP(x, 1);
	if (REG_P(dst) || GET_CODE(dst) == CC0)
		  {
	    if (m68k_68080_costs (src, mode, code, 1, total, speed))
		    return true;
		  }
	else if (m68k_68080_costs (dst, mode, code, 0, total, speed)
	    && m68k_68080_costs (src, mode, code, 1, &total2, speed))
	  {
	    *total += 4 + total2;
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
	if (m68k_68080_costs (dst, mode, code, 0, total, speed)
	    && m68k_68080_costs (src, mode, code, 1, &total2, speed))
	  {
	    *total += 4 + total2;
	    return true;
	  }
      }
      break;
    case ASHIFT:
    case ASHIFTRT:
    case LSHIFTRT:
      {
	*total = 4;
	rtx op = XEXP(x, 1);
	if (CONST_INT_P(op))
	  {
	    int n = INTVAL(op);
	    while (n -= 8 > 0)
	      *total += 4;
	  }
	return true;
      }
      break;
    case MULT:
      {
	rtx op = XEXP(x, 0);
	if (CONST_INT_P(op) && exact_log2(INTVAL(op)))
	  *total = 4;
	else
	  *total = 12;
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
		*total = 0;
		return true;
	      }
	    m68k_68080_costs (b, mode, code, 1, total, speed);
	    return true;
	  }
	if (m68k_68080_costs (a, mode, code, 0, total, speed))
	  {
	    if (GET_CODE(b) == CONST_INT && INTVAL(b) == 0)
	      return true;

	    if (m68k_68080_costs (b, mode, code, 1, &total2, speed))
	      {
	    *total += total2;
	    return true;
	  }
      }
      }
      break;
    case IF_THEN_ELSE:
      *total = 4;
      return true;
    case FLOAT:
    case FLOAT_TRUNCATE:
    case FIX:
      // maybe check for 68881?
      *total = 4;
      return true;
    case ASM_OPERANDS:
    case ASM_INPUT:
      return false;
    }
  *total = 4;
  return true;
}

