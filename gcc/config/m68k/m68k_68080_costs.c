#include "config.h"
#include "system.h"
#include "coretypes.h"
#include "backend.h"
#include "cfghooks.h"
#include "tree.h"
#include "rtl.h"
#include "insn-modes.h"

bool
m68k_68080_costs (rtx x, machine_mode mode, int outer_code, int opno,
		  int *total, bool speed);
#if 1
static int ttotal;
#define TEST(a,r) {ttotal = 0; m68k_68080_costs(a, SImode, 0, 0, &ttotal, 1); if (ttotal != r) {debug(a);printf("%d <> %d: %s\n", ttotal, r, #a);}}

void
selftest_m68k_68080_costs (void)
{
  rtx d0 = gen_rtx_REG (SImode, 0);
  rtx d1 = gen_rtx_REG (SImode, 1);
  rtx a7 = gen_rtx_REG (SImode, 15);

  rtx c120 = GEN_INT(120);

  rtx mem_120ia0 = gen_rtx_MEM (SImode, gen_rtx_PLUS(SImode, a7, c120));

  rtx dummy = gen_rtx_SYMBOL_REF(SImode, "dummy");
  rtx minusa7 = gen_rtx_MEM(SImode, gen_rtx_PRE_DEC(SImode, a7));

  rtx movel_d0_d1 = gen_rtx_SET(d1, d0);
  TEST(movel_d0_d1, 4);

  rtx add_d0_d1 = gen_rtx_SET(d1, gen_rtx_PLUS(SImode, d1, d0));
  TEST(add_d0_d1, 4);

  rtx movel_120ia0_d0 = gen_rtx_SET(d0, mem_120ia0);
  TEST(movel_120ia0_d0, 8);

  rtx ashl_8_d0 = gen_rtx_SET(d0, gen_rtx_ASHIFT(SImode, d0, GEN_INT(8)));
  TEST(ashl_8_d0, 4);

  rtx pea_sym = gen_rtx_SET(minusa7, dummy);
  TEST(pea_sym, 9);

  rtx pea_32 = gen_rtx_SET(minusa7, GEN_INT(32));
  TEST(pea_32, 8);

  rtx addq8sp = gen_rtx_SET(a7, gen_rtx_PLUS(SImode, a7, GEN_INT(8)));
  TEST(addq8sp, 4);

  rtx cmpd0a7 = gen_rtx_SET(cc0_rtx, gen_rtx_COMPARE(SImode, d0, a7));
  TEST(cmpd0a7, 4);
}
static int run;
#endif

/**
 * calculate costs for the 68080.
 * opno == 1: calculate as if dst is a register
 * opno == 0: calculate difference to register assignment
 */
bool
m68k_68080_costs (rtx x, machine_mode mode, int outer_code, int opno,
		  int *total, bool speed)
{
  if (!run)
    {
      run = 1;
      selftest_m68k_68080_costs ();
    }

  int code = GET_CODE(x);
  int total2 = 0;
  *total = 0;

  if (outer_code == ADDRESS)
    {
      if (GET_CODE (x) == CONST)
	x = XEXP(x, 0);
      if (REG_P(x) || GET_CODE(x) == POST_INC || GET_CODE(x) == PRE_DEC)
	{
	  *total = 0; // (ax), (ax)+, -(ax)
	  return true;
	}
      if (GET_CODE(x) == SYMBOL_REF || GET_CODE(x) == LABEL_REF || CONST_INT_P(x))
	{
	  *total = 1;
	  return true;
	}
      if (GET_CODE(x) == MULT)
	{
	  *total = 3;
	  return true;
	}

      if (GET_CODE(x) == PLUS)
	{
	  rtx b = XEXP(x, 0);
	  if (GET_CODE(b) == CONST)
	    b = XEXP(b, 0);
	  rtx c = XEXP(x, 1);
	  if (GET_CODE(c) == CONST)
	    c = XEXP(c, 0);

	  if ((GET_CODE(b) == SYMBOL_REF || GET_CODE(b) == LABEL_REF  || CONST_INT_P(b))
	      && CONST_INT_P(c))
	    {
	      *total = 1; // sym+n
	      return true;
	    }

	  if (REG_P(b) && GET_CODE(c) == CONST_INT && INTVAL(c) >= -32768
	      && INTVAL(c) <= 37267)
	    {
	      *total = 1; // 16(An),Dn
	      return true;
	    }
	  if (REG_P(b) || GET_CODE(b) == MULT || GET_CODE(b) == ASHIFT)
	    {
	      if (REG_P(c))
		{
		  *total = 3; // (An,Xn*S)
		  return true;
		}
	      if (REG_P(c) || GET_CODE(c) == SYMBOL_REF
		  || GET_CODE(c) == CONST_INT)
		{
		  *total = 5; // (32,Xn*S)
		  return true;
		}
	    }
	  if (GET_CODE(b) == PLUS)
	    {
	      rtx b0 = XEXP(b, 0);
	      rtx b1 = XEXP(b, 1);
	      if (REG_P(b0) || GET_CODE(b0) == MULT || GET_CODE(b0) == ASHIFT)
		{
		  if (GET_CODE(c) == CONST_INT)
		    {
		      *total = INTVAL(c) >= -8 && INTVAL(c) <= 8 ? 3 // 8(An,Xn*S)
			  :
			       INTVAL(c) >= -32768 && INTVAL(c) <= 32767 ? 4 // (16,An,Xn*S)
				   : 5; // (32,An,Xn*S)
		      return true;
		    }
		  if (GET_CODE(c) == SYMBOL_REF || GET_CODE(c) == LABEL_REF || CONST_INT_P(c))
		    {
		      *total = 5;
		      return true;
		    }
		}
	      if (GET_CODE(b0) == SYMBOL_REF && CONST_INT_P(b1))
		{
		  *total = 5;
		  return true;
		}
	    }
	  if (GET_CODE(c) == PLUS)
	    {
	      *total = 5;
	      return true;
	    }
	}
      *total = 35;
      return true;
    }

  switch (code)
    {
    case CC0:
    case PC:
    case REG:
      return true;

    case CONST_INT:
      {
	int iv = INTVAL(x);
	switch (outer_code)
	{
	  case SET: // moveq
	    if (iv >= -0x100 && iv <= 0xff)
	      break;
	    goto Defconst;
	  case PLUS:
	  case MINUS:
	    if (iv >= -8 && iv <= 8)
	      break;
	    goto Defconst;
	  case ASHIFT:
	  case ASHIFTRT:
	  case LSHIFTRT:
	    break;
	  default:
Defconst:
	    if (iv == 0) // used in compares
	      break;

	    if ((outer_code == MEM || outer_code == COMPARE || outer_code == PLUS ||
		GET_MODE_SIZE(mode) < 4) && iv >= -32768 && iv <= 32767)
	      *total = 1;
	    else
	      *total = 2;
	    break;
	}
      }
      return true;

    case CONST_DOUBLE:
      *total = mode == SFmode ? 2 : mode == DFmode ? 4 : 6;
      return true;

    case FLOAT:
    case FLOAT_TRUNCATE:
    case FIX:
      *total = 8; // guessed
      return true;

    case MULT:
      {
	rtx op = XEXP(x, 0);
	if (CONST_INT_P(op) && exact_log2 (INTVAL(op)))
	  total2 = 0; // same as shift
	else
	  total2 = 8;
	goto OpCost;
      }
      break;

    case UDIV:
    case MOD:
    case DIV:
      total2 = 60; // always in a parallel with DIV and MOD -> half costs
      goto OpCost;

    case ASHIFT:
    case ASHIFTRT:
    case LSHIFTRT:
    case PLUS:
    case MINUS:
    case AND:
    case IOR:
    case XOR:
      {
	OpCost: rtx a = XEXP(x, 0);
	rtx b = XEXP(x, 1);

	// reg or mem
	m68k_68080_costs (a, mode, code, 0, total, speed);
	total2 += *total;

	// add cost for 2nd
	m68k_68080_costs (b, mode, code, 0, total, speed);
	*total += total2;
	return true;
      }
      break;

    case SUBREG:
    case STRICT_LOW_PART:
    case SIGN_EXTRACT:
    case ZERO_EXTRACT:
    case TRUNCATE:
    case ZERO_EXTEND:
    case NOT:
    case NEG:
    case SIGN_EXTEND:
    case CONST:
      // no additional cost
      return m68k_68080_costs (XEXP(x, 0), mode, code, 0, total, speed);

    case CALL:
      {
	bool r = m68k_68080_costs (XEXP(x, 0), mode, code, 0, total, speed);
	*total += 7;
	return true;
      }

    case MEM:
      {
	// ADDRESS cost + 3
	bool r = m68k_68080_costs (XEXP(x, 0), mode, ADDRESS, 0, total, speed);
	*total += 3;
	return r;
      }

    case SYMBOL_REF:
    case LABEL_REF:
      *total = 2;
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
    case COMPARE:
      {
	rtx dst = XEXP(x, 0);
	rtx src = XEXP(x, 1);
	bool r = m68k_68080_costs (dst, mode, code, 0, total, speed);
	total2 = *total;
	r &= m68k_68080_costs (src, mode, code, 0, total, speed);
	*total += total2;
	return r;
      }
    case SET:
      {
	total2 = 4;

	rtx dst = XEXP(x, 0);
	rtx src = XEXP(x, 1);
	if (GET_CODE(dst) == PC)
	  {
	    if (GET_CODE(src) == IF_THEN_ELSE)
	      {
		*total = 16;
		return true;
	      }
	    bool r = m68k_68080_costs (src, mode, ADDRESS, 0, total, speed);
	    *total += total2;
	    return true;
	  }
	if (GET_CODE(dst) == CC0)
	  {
	    bool r = m68k_68080_costs (src, mode, code, 0, total, speed);
	    *total += total2;
	    return r;
	  }

	bool r = m68k_68080_costs (dst, mode, code, 0, total, speed);
	total2 += *total;

	// binops have dst as first argument - check for binop
	const char *format = GET_RTX_FORMAT(GET_CODE(src));
	if (format && format[0] == 'e' && format[1] == 'e')
	  {
	    if (reload_completed)
	      {
		rtx p0 = XEXP(src, 0);
		if (SUBREG_P(p0))
		  p0 = XEXP(p0, 0);
		// reset cost if p0 == dst - do not add cost twice
		if (GET_CODE(src) == PLUS && !rtx_equal_p (p0, dst))
		  {
		    bool r = m68k_68080_costs (src, mode, ADDRESS, 0, total, speed);
		    *total += total2;
		    return true;
		  }
	      }
	    // modify dst with dst
	    total2 = 4; // reset to base cost
	  }

	r &= m68k_68080_costs (src, mode, MEM_P(dst) ? MEM : code, 0, total, speed);
	*total += total2;

	return r;
      }
      break;

    case IF_THEN_ELSE:
      *total = 16; // bcc
      return true;

    case ASM_OPERANDS:
    case ASM_INPUT:
      return false;
    }
  return false;
}
