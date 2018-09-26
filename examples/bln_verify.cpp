/* kitty: C++ truth table library
 * Copyright (C) 2017-2018  EPFL
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

#include <iostream>
#include <fstream>
#include <sstream>
#include <unordered_map>
#include <vector>

#include <kitty/kitty.hpp>
#include <kitty/detail/utils.hpp>

constexpr static auto verbose = false;

int verify( const std::vector<std::string>& chain, unsigned num_vars, const std::string& hextt, unsigned fanin, unsigned steps )
{
  kitty::dynamic_truth_table spec( num_vars );
  kitty::create_from_hex_string( spec, hextt );

  std::unordered_map<char, kitty::dynamic_truth_table> tables;
  for ( auto i = 0u; i < num_vars; ++i )
  {
    auto proj = spec.construct();
    kitty::create_nth_var( proj, i );
    tables.insert( {'a' + i, proj} );
  }

  if ( chain.size() != steps )
  {
    if ( verbose ) std::cout << "[e] chain has not given number of steps\n";
    return 0;
  }

  std::string schain;
  std::string prev_gate;
  std::string prev_supp;

  for ( auto i = 0u; i < steps; ++i )
  {
    auto it = chain[i].begin();
    auto name = *it++;
    if ( name != static_cast<char>( 'A' + num_vars + i ) )
    {
      if ( verbose ) std::cout << "[e] invalid step " << chain[i] << "\n";
      return 0;
    }

    if ( std::string( it, it + 3 ) != " = " )
    {
      if ( verbose ) std::cout << "[e] mal-formed step " << chain[i] << "\n";
      return 0;
    }
    it += 3;

    const auto gate_length = ( 1 << fanin );
    std::string gatett( it, it + gate_length );
    it += gate_length;

    kitty::dynamic_truth_table gate( fanin );
    kitty::create_from_binary_string( gate, gatett );

    if ( kitty::get_bit( gate, 0 ) != 0 )
    {
      if ( verbose ) std::cout << "[e] gate is not normalized in " << chain[i] << "\n";
      return 0;
    }

    std::vector<kitty::dynamic_truth_table> vfanin( fanin );
    auto last_fanin = 'a';
    std::string supp;
    for ( auto j = 0u; j < fanin; ++j )
    {
      if ( *it++ != ' ' )
      {
        if ( verbose ) std::cout << "[e] mal-formed step " << chain[i] << "\n";
        return 0;
      }

      if ( std::tolower( *it ) < last_fanin )
      {
        if ( verbose ) std::cout << "[e] fanins are in wrong order in " << chain[i] << "\n";
        return 0;
      }
      last_fanin = std::tolower( *it );
      supp += last_fanin;

      vfanin[j] = tables[*it++];
    }

    if ( supp == prev_supp && !std::lexicographical_compare( prev_gate.begin(), prev_gate.end(), gatett.begin(), gatett.end() ) )
    {
      if ( verbose ) std::cout << "[e] gates with same support are not ordered in " << chain[i] << "\n";
      return 0;
    }

    if ( i && supp != prev_supp && std::find( supp.begin(), supp.end(), 'a' + num_vars + i - 1 ) == supp.end() && !std::lexicographical_compare( prev_supp.begin(), prev_supp.end(), supp.begin(), supp.end() ) )
    {
      if ( verbose ) std::cout << "[e] co-lexicographic order violated in " << chain[i] << "\n";
      return 0;
    }

    prev_supp = supp;
    prev_gate = gatett;
    schain += supp;

    if ( it != chain[i].end() )
    {
      if ( verbose ) std::cout << "[e] mal-formed step " << chain[i] << "\n";
      return 0;
    }

    auto steptt = spec.construct();
    for ( auto i = 0u; i < steptt.num_bits(); ++i )
    {
      uint32_t pattern = 0u;
      for ( auto j = 0u; j < fanin; ++j )
      {
        pattern |= kitty::get_bit( vfanin[j], i ) << j;
      }
      if ( kitty::get_bit( gate, pattern ) )
      {
        kitty::set_bit( steptt, i );
      }
    }

    tables.insert( {name, steptt} );
  }

  if ( tables['A' + num_vars + steps - 1] != spec )
  {
    if ( verbose ) std::cout << "[e] chain does not compute spec\n";
    return 0;
  }

  /* check symmetry property */
  for ( auto j = 1u; j < num_vars; ++j )
  {
    for ( auto i = 0u; i < j; ++i )
    {
      if ( is_symmetric_in( spec, i, j ) && std::find( schain.begin(), schain.end(), 'a' + j ) < std::find( schain.begin(), schain.end(), 'a' + i ) )
      {
        std::cout << "symmetry property violated in " << i << " and " << j << "\n";
      }
    }
  }

  return 1;
}

int main( int argc, char ** argv )
{
  if ( argc != 5)
  {
    std::cerr << "[e] usage " << argv[0] << " <#VARS> <HEX-TT> <#FANIN> <#STEPS>\n";
  }

  unsigned num_vars = std::stoi( argv[1] );
  std::string hextt{argv[2]};
  unsigned fanin = std::stoi( argv[3] );
  unsigned steps = std::stoi( argv[4] );

  std::vector<std::string> chain;

  std::stringstream filename;
  filename << hextt << "-" << fanin << "-" << steps << ".bln";

  std::ifstream in( filename.str().c_str(), std::ifstream::in );
  std::string line;
  int points{0}, violations{0};

  while ( std::getline( in, line ) )
  {
    kitty::detail::trim( line );
    if ( line.empty() )
    {
      if ( !chain.empty() )
      {
        const auto p = verify( chain, num_vars, hextt, fanin, steps );
        points++;
        if ( p == 0 ) ++violations;
      }
      chain.clear();
    }
    else
    {
      chain.push_back( kitty::detail::trim_copy( line ) );
    }
  }

  if ( !chain.empty() )
  {
    const auto p = verify( chain, num_vars, hextt, fanin, steps );
    points++;
    if ( p == 0 ) ++violations;
  }

  std::cout << "[i] violations = " << violations << "\n";
  std::cout << "[i] solutions = " << points << "\n";
  std::cout << "[i] points = " << double(points) / ( 1 << violations ) << "\n";
}
