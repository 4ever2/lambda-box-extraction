#ifndef GLUE_C
#define GLUE_C
#include <gc_stack.h>
#include <stdio.h>
#include "glue.h"
struct closure;
struct closure {
  value (*func)(struct thread_info *, value, value);
  value env;
};

extern int is_ptr(value);
unsigned long long get_unboxed_ordinal(value);
unsigned long long get_boxed_ordinal(value);
value *get_args(value);
value make_Coq_Init_Datatypes_list_nil(void);
value make_Coq_Init_Datatypes_list_cons(value, value, value *);
value alloc_make_Coq_Init_Datatypes_list_cons(struct thread_info *, value, value);
value make_CertiCoq_bool_false(void);
value make_CertiCoq_bool_true(void);
value make_Coq_Init_Datatypes_nat_O(void);
value make_Coq_Init_Datatypes_nat_S(value, value *);
value alloc_make_Coq_Init_Datatypes_nat_S(struct thread_info *, value);
value make_Coq_Init_Datatypes_option_Some(value, value *);
value alloc_make_Coq_Init_Datatypes_option_Some(struct thread_info *, value);
value make_Coq_Init_Datatypes_option_None(void);
value make_Coq_Init_Datatypes_prod_pair(value, value, value *);
value alloc_make_Coq_Init_Datatypes_prod_pair(struct thread_info *, value, value);
unsigned long long get_Coq_Init_Datatypes_list_tag(value);
unsigned long long get_CertiCoq_bool_tag(value);
unsigned long long get_Coq_Init_Datatypes_nat_tag(value);
unsigned long long get_Coq_Init_Datatypes_option_tag(value);
unsigned long long get_Coq_Init_Datatypes_prod_tag(value);
void print_Coq_Init_Datatypes_list(value, void (*)(value));
void print_CertiCoq_bool(value);
void print_Coq_Init_Datatypes_nat(value);
void print_Coq_Init_Datatypes_option(value, void (*)(value));
void print_Coq_Init_Datatypes_prod(value, void (*)(value), void (*)(value));
value call(struct thread_info *, value, value);
signed char const lparen_lit[2] = { 40, 0, };

signed char const rparen_lit[2] = { 41, 0, };

signed char const space_lit[2] = { 32, 0, };

signed char const fun_lit[6] = { 60, 102, 117, 110, 62, 0, };

signed char const type_lit[7] = { 60, 116, 121, 112, 101, 62, 0, };

signed char const unk_lit[6] = { 60, 117, 110, 107, 62, 0, };

signed char const prop_lit[7] = { 60, 112, 114, 111, 112, 62, 0, };

unsigned long long get_unboxed_ordinal(value $v)
{
  return (unsigned long long) $v >> 1LL;
}

unsigned long long get_boxed_ordinal(value $v)
{
  return (unsigned long long) *((unsigned long long *) $v + -1LL) & 255LL;
}

value *get_args(value $v)
{
  return (value *) $v;
}

signed char const names_of_Coq_Init_Datatypes_list[2][5] = { 110, 105, 108,
  0, 0, 99, 111, 110, 115, 0, /* skip 0 */ };

signed char const names_of_CertiCoq_bool[2][6] = { 102, 97, 108, 115, 101, 0,
  116, 114, 117, 101, 0, 0, /* skip 0 */ };

signed char const names_of_Coq_Init_Datatypes_nat[2][2] = { 79, 0, 83, 0,
  /* skip 0 */ };

signed char const names_of_Coq_Init_Datatypes_option[2][5] = { 83, 111, 109,
  101, 0, 78, 111, 110, 101, 0, /* skip 0 */ };

signed char const names_of_Coq_Init_Datatypes_prod[1][5] = { 112, 97, 105,
  114, 0, /* skip 0 */ };

value make_Coq_Init_Datatypes_list_nil(void)
{
  return (value) 1;
}

value make_Coq_Init_Datatypes_list_cons(value $arg0, value $arg1, value *$argv)
{
  *($argv + 0LL) = (value) 2048LL;
  *($argv + 1LL) = $arg0;
  *($argv + 2LL) = $arg1;
  return $argv + 1LL;
}

value alloc_make_Coq_Init_Datatypes_list_cons(struct thread_info *$tinfo, value $arg0, value $arg1)
{
  register value *$argv;
  $argv = (*$tinfo).alloc;
  *($argv + 0LL) = 2048LL;
  *($argv + 1LL) = $arg0;
  *($argv + 2LL) = $arg1;
  (*$tinfo).alloc = (*$tinfo).alloc + 3LL;
  return $argv + 1LL;
}

value make_CertiCoq_bool_false(void)
{
  return (value) 1;
}

value make_CertiCoq_bool_true(void)
{
  return (value) 3;
}

value make_Coq_Init_Datatypes_nat_O(void)
{
  return (value) 1;
}

value make_Coq_Init_Datatypes_nat_S(value $arg0, value *$argv)
{
  *($argv + 0LL) = (value) 1024LL;
  *($argv + 1LL) = $arg0;
  return $argv + 1LL;
}

value alloc_make_Coq_Init_Datatypes_nat_S(struct thread_info *$tinfo, value $arg0)
{
  register value *$argv;
  $argv = (*$tinfo).alloc;
  *($argv + 0LL) = 1024LL;
  *($argv + 1LL) = $arg0;
  (*$tinfo).alloc = (*$tinfo).alloc + 2LL;
  return $argv + 1LL;
}

value make_Coq_Init_Datatypes_option_Some(value $arg0, value *$argv)
{
  *($argv + 0LL) = (value) 1024LL;
  *($argv + 1LL) = $arg0;
  return $argv + 1LL;
}

value alloc_make_Coq_Init_Datatypes_option_Some(struct thread_info *$tinfo, value $arg0)
{
  register value *$argv;
  $argv = (*$tinfo).alloc;
  *($argv + 0LL) = 1024LL;
  *($argv + 1LL) = $arg0;
  (*$tinfo).alloc = (*$tinfo).alloc + 2LL;
  return $argv + 1LL;
}

value make_Coq_Init_Datatypes_option_None(void)
{
  return (value) 1;
}

value make_Coq_Init_Datatypes_prod_pair(value $arg0, value $arg1, value *$argv)
{
  *($argv + 0LL) = (value) 2048LL;
  *($argv + 1LL) = $arg0;
  *($argv + 2LL) = $arg1;
  return $argv + 1LL;
}

value alloc_make_Coq_Init_Datatypes_prod_pair(struct thread_info *$tinfo, value $arg0, value $arg1)
{
  register value *$argv;
  $argv = (*$tinfo).alloc;
  *($argv + 0LL) = 2048LL;
  *($argv + 1LL) = $arg0;
  *($argv + 2LL) = $arg1;
  (*$tinfo).alloc = (*$tinfo).alloc + 3LL;
  return $argv + 1LL;
}

unsigned long long get_Coq_Init_Datatypes_list_tag(value $v)
{
  register _Bool $b;
  register unsigned long long $t;
  $b = is_ptr($v);
  if ($b) {
    $t = get_boxed_ordinal($v);
    switch ($t) {
      case 0:
        return 1;
      
    }
  } else {
    $t = get_unboxed_ordinal($v);
    switch ($t) {
      case 0:
        return 0;
      
    }
  }
}

unsigned long long get_CertiCoq_bool_tag(value $v)
{
  register unsigned long long $t;
  $t = get_unboxed_ordinal($v);
  return $t;
}

unsigned long long get_Coq_Init_Datatypes_nat_tag(value $v)
{
  register _Bool $b;
  register unsigned long long $t;
  $b = is_ptr($v);
  if ($b) {
    $t = get_boxed_ordinal($v);
    switch ($t) {
      case 0:
        return 1;
      
    }
  } else {
    $t = get_unboxed_ordinal($v);
    switch ($t) {
      case 0:
        return 0;
      
    }
  }
}

unsigned long long get_Coq_Init_Datatypes_option_tag(value $v)
{
  register _Bool $b;
  register unsigned long long $t;
  $b = is_ptr($v);
  if ($b) {
    $t = get_boxed_ordinal($v);
    switch ($t) {
      case 0:
        return 0;
      
    }
  } else {
    $t = get_unboxed_ordinal($v);
    switch ($t) {
      case 0:
        return 1;
      
    }
  }
}

unsigned long long get_Coq_Init_Datatypes_prod_tag(value $v)
{
  register unsigned long long $t;
  $t = get_boxed_ordinal($v);
  return $t;
}

void print_Coq_Init_Datatypes_list(value $v, void $print_param_A(value))
{
  register unsigned int $tag;
  register void *$args;
  $tag = get_Coq_Init_Datatypes_list_tag($v);
  switch ($tag) {
    case 0:
      printf(*(names_of_Coq_Init_Datatypes_list + $tag));
      break;
    case 1:
      $args = get_args($v);
      printf(lparen_lit);
      printf(*(names_of_Coq_Init_Datatypes_list + $tag));
      printf(space_lit);
      $print_param_A(*((value *) $args + 0));
      printf(space_lit);
      print_Coq_Init_Datatypes_list(*((value *) $args + 1), $print_param_A);
      printf(rparen_lit);
      break;
    
  }
}

void print_CertiCoq_bool(value $v)
{
  register unsigned int $tag;
  $tag = get_CertiCoq_bool_tag($v);
  printf(*(names_of_CertiCoq_bool + $tag));
}

void print_Coq_Init_Datatypes_nat(value $v)
{
  register unsigned int $tag;
  register void *$args;
  $tag = get_Coq_Init_Datatypes_nat_tag($v);
  switch ($tag) {
    case 0:
      printf(*(names_of_Coq_Init_Datatypes_nat + $tag));
      break;
    case 1:
      $args = get_args($v);
      printf(lparen_lit);
      printf(*(names_of_Coq_Init_Datatypes_nat + $tag));
      printf(space_lit);
      print_Coq_Init_Datatypes_nat(*((value *) $args + 0));
      printf(rparen_lit);
      break;
    
  }
}

void print_Coq_Init_Datatypes_option(value $v, void $print_param_A(value))
{
  register unsigned int $tag;
  register void *$args;
  $tag = get_Coq_Init_Datatypes_option_tag($v);
  switch ($tag) {
    case 0:
      $args = get_args($v);
      printf(lparen_lit);
      printf(*(names_of_Coq_Init_Datatypes_option + $tag));
      printf(space_lit);
      $print_param_A(*((value *) $args + 0));
      printf(rparen_lit);
      break;
    case 1:
      printf(*(names_of_Coq_Init_Datatypes_option + $tag));
      break;
    
  }
}

void print_Coq_Init_Datatypes_prod(value $v, void $print_param_A(value), void $print_param_B(value))
{
  register unsigned int $tag;
  register void *$args;
  $tag = get_Coq_Init_Datatypes_prod_tag($v);
  switch ($tag) {
    case 0:
      $args = get_args($v);
      printf(lparen_lit);
      printf(*(names_of_Coq_Init_Datatypes_prod + $tag));
      printf(space_lit);
      $print_param_A(*((value *) $args + 0));
      printf(space_lit);
      $print_param_B(*((value *) $args + 1));
      printf(rparen_lit);
      break;
    
  }
}

value call(struct thread_info *$tinfo, value $clo, value $arg)
{
  register value $f;
  register value $envi;
  register value $tmp;
  $f = (*((struct closure *) $clo)).func;
  $envi = (*((struct closure *) $clo)).env;
  $tmp =
    ((value (*)(struct thread_info *, value, value)) $f)
    ($tinfo, $envi, $arg);
  return $tmp;
}


#endif /* GLUE_C */
