/* kitty: C++ truth table library
 * Copyright (C) 2017-2020  EPFL
 *
 * Permission is hereby granted, free of charge, to any person
 * obtaining a copy of this software and associated documentation
 * files (the "Software"), to deal in the Software without
 * restriction, including without limitation the rights to use,
 * copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following
 * conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
 * HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
 * WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
 * OTHER DEALINGS IN THE SOFTWARE.
 */

/*!
  \file threshold_identification.hpp
  \brief Threshold logic function identification

  \author CS-472 2020 Fall students
*/

#pragma once

#include <vector>
#include <lpsolve/lp_lib.h> /* uncomment this line to include lp_solve */
#include "traits.hpp"

#include <iostream>
using namespace std;

namespace kitty
{

/*! \brief Threshold logic function identification

  Given a truth table, this function determines whether it is a threshold logic function (TF)
  and finds a linear form if it is. A Boolean function is a TF if it can be expressed as

  f(x_1, ..., x_n) = \sum_{i=1}^n w_i x_i >= T

  where w_i are the weight values and T is the threshold value.
  The linear form of a TF is the vector [w_1, ..., w_n; T].

  \param tt The truth table
  \param plf Pointer to a vector that will hold a linear form of `tt` if it is a TF.
             The linear form has `tt.num_vars()` weight values and the threshold value
             in the end.
  \return `true` if `tt` is a TF; `false` if `tt` is a non-TF.
*/
template<typename TT, typename = std::enable_if_t<is_complete_truth_table<TT>::value>>
bool is_threshold( const TT& tt, std::vector<int64_t>* plf = nullptr )
{
  std::vector<int64_t> linear_form;

  /* if tt is non-TF: */
  const int MAX_NUM = 100; // number of variables <= 32 due to int32_t

  int NumBits = tt.num_bits();
  int NumVars = tt.num_vars();
  TT tt_flip = tt;
  int flip_table[MAX_NUM];

  if ( NumVars > MAX_NUM )
  {
    std::cout << "Number of variables are exceeded" << endl;
    return false;
  }

  // check the unateness of the truth table
  for ( auto i = 0u; i < NumVars; ++i )
  {
    if ( implies( cofactor1( tt, i ), cofactor0( tt, i ) ) ) // negative unate
    {
      tt_flip = flip( tt_flip, i ); // substitute the variable with its bar
      flip_table[i] = 1;
    }
    else if ( implies( cofactor0( tt, i ), cofactor1( tt, i ) ) ) // positive unate
    {
      flip_table[i] = 0;
    }
    else // binate means non-TF
    {
      return false; // non-TF
    }
  }

  /* "Formulation of an lp model in lpsolve" in http://lpsolve.sourceforge.net/ */
  lprec* lp;
  int Ncol, *colno = NULL, ret = 0;
  REAL* row = NULL;
  char var_name[10];

  /* build the model row by row
   * create a model with 0 rows and (NumVars + 1) columns */
  Ncol = NumVars + 1; // [w_1, w_2, ..., w_n; T]
  lp = make_lp( 0, Ncol );

  if ( lp == NULL )
  {
    ret = 1; // couldn't construct a new model...
  }

  // create the variables
  if ( ret == 0 )
  {
    // name the variables as [w_1, w_2, ..., w_n; T]
    for ( auto i = 0u; i < NumVars; ++i )
    {
      sprintf( var_name, "w_%d", i );
      set_col_name( lp, i + 1, var_name );
    }
    set_col_name( lp, Ncol, "T" );

    // create space large enough for one row
    colno = (int*)malloc( Ncol * sizeof( *colno ) );
    row = (REAL*)malloc( Ncol * sizeof( *row ) );
    if ( ( colno == NULL ) || ( row == NULL ) )
    {
      ret = 2;
    }
  }

  // add the constraints
  if ( ret == 0 )
  {
    set_add_rowmode( lp, TRUE ); // makes building the model faster if it is done row by row

    // all of the variables are positive
    for ( auto i = 0u; i < Ncol; ++i )
    {
      colno[0] = i + 1;
      row[i] = 1;
      if ( !add_constraintex( lp, 1, row, colno, GE, 0 ) )
      {
        ret = 3;
      }
    }
 
    for ( auto i = 0u; i < NumBits; ++i )
    {
      int temp = i;
      for ( auto j = 0u; j < NumVars; ++j )
      {
        colno[j] = j + 1;
        row[j] = temp % 2;
        temp = temp >> 1;
      }

      colno[NumVars] = Ncol;
      row[NumVars] = -1; // -T
      if ( get_bit( tt_flip, i ) )
      {
        add_constraintex( lp, Ncol, row, colno, GE, 0 ); // \sum_{i=1}^n w_i - T >= 0, xi is onset
      }
      else
      {
        add_constraintex( lp, Ncol, row, colno, LE, -1 ); // \sum_{i=1}^n w_i - T <= -1, xi is offset
      }
    }
  }

  // set the objective function \sum_{i=1}^n w_i + T
  if ( ret == 0 )
  {
    set_add_rowmode( lp, FALSE ); // rowmode should be turned off again when done building the model

    for ( auto i = 0u; i < Ncol; ++i )
    {
      colno[i] = i + 1;
      row[i] = 1;
    }
    // set the objective in lpsolve
    if ( !set_obj_fnex( lp, Ncol, row, colno ) )
    {
      ret = 6;
    }
  }

  // set variables to int
  if ( ret == 0 )
  {
    for ( int i = 1; i <= Ncol; i++ )
      set_int( lp, i, TRUE );
  }

  // start to solve this LP problem
  if ( ret == 0 )
  {
    // set the objective direction to minimize
    set_minim( lp );

    // print the LP problem
    //write_LP(lp, stdout);
    // write_lp(lp, "model.lp");

    // print important message on screen while solving
    set_verbose( lp, IMPORTANT );

    // Now let lpsolve calculate a solution
    ret = solve( lp );
    if ( ret == OPTIMAL )
    {
      ret = 0;
    }
    else
    {
      ret = 7;
    }
  }

  // get the results
  if ( ret == 0 )
  {
    // objective value
    printf( "Objactive value: %f\n", get_objective( lp ) );

    // variable values
    get_variables( lp, row );
    int T = row[Ncol - 1];
    for ( auto i = 0u; i < Ncol; ++i )
    {
      printf( "%s: %f\n", get_col_name( lp, i + 1 ), row[i] );
    }

    for ( auto i = 0u; i < NumVars; ++i )
    {
      if ( flip_table[i] == 0 )
      {
        linear_form.push_back( row[i] );
      }
      else
      {
        linear_form.push_back( -row[i] );
        T = T - row[i];
      }
    }
    linear_form.push_back( T );
  }

  // free allocated memory
  if ( row != NULL )
  {
    free( row );
  }
  if ( colno != NULL )
  {
    free( colno );
  }

  // clean up such that all used memory by lpsolve is freed
  if ( lp != NULL )
  {
    delete_lp( lp );
  }

  //std::cout << "ret = " << ret << endl;

  // ret != 0 means non-TF
  if ( ret != 0 )
  {
    return false;
  }
  /* if tt is TF: */
  /* push the weight and threshold values into `linear_form` */
  if ( plf )
  {
    *plf = linear_form;
  }
  return true;
}

} /* namespace kitty */
