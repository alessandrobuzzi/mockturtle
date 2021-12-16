/*!
  \file aig_algebraic_rewriting.hpp
  \brief AIG algebraric rewriting

  EPFL CS-472 2021 Final Project Option 1
*/

#pragma once

#include "../networks/aig.hpp"
#include "../views/depth_view.hpp"
#include "../views/topo_view.hpp"

namespace mockturtle
{

namespace detail
{

template<class Ntk>
class aig_algebraic_rewriting_impl
{
  using node = typename Ntk::node;
  using signal = typename Ntk::signal;

public:
  aig_algebraic_rewriting_impl( Ntk& ntk )
    : ntk( ntk )
  {
    static_assert( has_level_v<Ntk>, "Ntk does not implement depth interface." );
  }

  void run()
  {
    bool cont{true}; /* continue trying */
    while ( cont )
    {
      cont = false; /* break the loop if no updates can be made */
      ntk.foreach_gate( [&]( node n ){
        if ( try_algebraic_rules( n ) )
        {
          ntk.update_levels();
          cont = true;
        }
      });
    }
  }

private:
  /* Try various algebraic rules on node n. Return true if the network is updated. */
  bool try_algebraic_rules( node n )
  {
    if ( try_associativity( n ) )
      return true;
    if ( try_distributivity( n ) )
      return true;
    if ( try_three_layer_distributivity( n ))
        return true;

    return false;
  }

  /* Try the associativity rule on node n. Return true if the network is updated. */

  bool try_associativity( node n )
  {
    std::vector<signal> critical;
    std::vector<signal> non_critical;

    signal critical_child;
    signal non_critical_child;
    signal critical_grandchild;
    signal non_critical_grandchild;

    signal new_block;

    ntk.foreach_fanin(n, [&](signal child)      // function called for every input
    {
        if(ntk.is_on_critical_path(ntk.get_node(child)))  // check weather the input is on critical path
        {
            critical.push_back(child);    // save the signal if the branch could be optimized
        }
        else
        {
            non_critical.push_back(child);  // save signals not on the critical path
        }

    });

    // if none is critical skip, if just one is critical look at it,
    // if two are critical choose the one with highest level iff the level difference is greater than 2

    switch (critical.size())
    {
        case 0:
        {
            return false;   // no critical path is involved
        }
        case 1:
        {
            if (ntk.is_complemented(critical[0]))
            {
                return false;   // no associativity can be applied
            }
            else
            {
                critical_child = critical[0];
                non_critical_child = non_critical[0];
            }

            if((ntk.level(ntk.get_node(critical_child)) - ntk.level(ntk.get_node(non_critical_child))) < 2)
            {
                return false;   // associativity would not be convenient
            }
            break;
        }
        case 2:
        {
            return false;   ///ELIMINARE
            int level_difference = ntk.level(ntk.get_node(critical[0])) - ntk.level(ntk.get_node(critical[1]));

            if(abs(level_difference) < 2)
            {
                return false;   // no associativity would be convenient
            }

            if(level_difference > 0)    // critical[0] level is greater, and therefore it is more critical
            {
                critical_child = critical[0];
                non_critical_child = critical[1];
            }
            else
            {
                critical_child = critical[1];
                non_critical_child = critical[0];
            }

            if(ntk.is_complemented(critical_child))
            {
                return false;   // no associativity can be applied
            }
            break;
        }
        default:
        {
            std::cerr << "Unknown error." << std::endl;
            break;
        }
    }

    // Clear vectors
    critical.clear();
    non_critical.clear();

    ntk.foreach_fanin(ntk.get_node(critical_child) , [&](signal grandchild)     // function called for every input of critical child
    {
        if(ntk.is_on_critical_path(ntk.get_node(grandchild)))  // check weather the input is on critical path
        {
            critical.push_back(grandchild);
        }
        else
        {
            non_critical.push_back(grandchild);  // save signals not on the critical path
        }
    });

    if(critical.size() == 0)
    {
        return false;
    }

    if(critical.size() == 1)    // just one grandchild is critical
    {
        critical_grandchild = critical[0];
        non_critical_grandchild = non_critical[0];
    }
    else    // the grandchildren are both critical
    {
        int level_difference = ntk.level(ntk.get_node(critical[0])) - ntk.level(ntk.get_node(critical[1]));

        if(abs(level_difference) < 1)
        {
            return false;   // no associativity would be convenient
        }

        if(level_difference > 0)
        {
            critical_grandchild = critical[0];
            non_critical_grandchild = critical[1];
        }
        else
        {
            critical_grandchild = critical[1];
            non_critical_grandchild = critical[0];
        }

    }

    if(ntk.is_and(n))   // create new net
    {
        new_block = ntk.create_and(critical_grandchild, ntk.create_and(non_critical_child, non_critical_grandchild));
    }
    else
    {
        new_block = ntk.create_nand(critical_grandchild, ntk.create_and(non_critical_child, non_critical_grandchild));
    }

    ntk.substitute_node(n, new_block);  // substitute the new net
    return true;
  }


    bool try_distributivity( node n )
    {
        std::vector<signal> grandchildren;
        std::vector<signal> children;

        std::vector<std::vector<int>> recurrence;
        std::vector<std::pair<bool, bool>> left_right;
        int position = 0;
        bool valid = true;

        ntk.foreach_fanin(n, [&](signal child)      // function called for every input
        {
            if(!(ntk.is_complemented(child) && ntk.is_on_critical_path(ntk.get_node(child))))
            {
                valid = false;       // both input must be complemented and critical to apply distributivity
            } else {
                ntk.foreach_fanin(ntk.get_node(child), [&](signal grandchild)
                {
                    int index = grandchildren.size();
                    bool found = false;

                    for(int i = 0; i < grandchildren.size(); i++)
                    {
                        if(grandchildren[i] == grandchild)
                        {
                            found = true;
                            index = i;
                        }
                    }

                    if(!found)
                    {
                        std::vector<int> temp_position;
                        temp_position.push_back(position);
                        grandchildren.push_back(grandchild);    // signal has not been met yet
                        recurrence.push_back(temp_position);
                        if(position < 2)
                        {
                            std::pair<bool, bool> temp_pair;
                            temp_pair.first = true;
                            temp_pair.second = false;
                            left_right.push_back(temp_pair);
                        } else
                        {
                            std::pair<bool, bool> temp_pair;
                            temp_pair.first = false;
                            temp_pair.second = true;
                            left_right.push_back(temp_pair);
                        }

                    }
                    else
                    {
                        recurrence[index].push_back(position);
                        if((position < 2 && !left_right[index].first) || (position >=2 && !left_right[index].second))
                        {
                            left_right[index].first = true;
                            left_right[index].second = true;
                        }
                    }
                    position++;
                });
            }
        });

        if(position != 4)
        {
            return false;   //associativity can not be applied
        }

        if(!valid)
        {
            return false;
        }


        switch(grandchildren.size())
        {
            case 0:
            {
                std::cerr << "Unknown error" << std::endl;
                return false;
            }
            case 1:     // only one signal
            {
                return false;
            }
            case 2: // a b
            {
                return false;
            }
            case 3:     // a b b c
            {
                for(int i = 0; i < grandchildren.size(); i++)
                {
                    if(recurrence[i].size() == 2)   // find recurrent signal
                    {
                        if(ntk.is_on_critical_path(ntk.get_node(grandchildren[i])))
                        {
                            if(left_right[i].first && left_right[i].second)     // appears on both branches
                            {
                                signal critical_signal = grandchildren[i];
                                signal new_block;

                                grandchildren.erase(grandchildren.begin() + i);     // remove critical from the vector

                                if(ntk.is_on_critical_path(ntk.get_node(grandchildren[0])) || ntk.is_on_critical_path(ntk.get_node(grandchildren[1])))
                                {
                                    return false;   // distributivity is not convenient
                                }

                                if(ntk.is_and(n))   // create new net
                                {
                                    new_block = ntk.create_nand(critical_signal, ntk.create_or(grandchildren[0], grandchildren[1]));
                                }
                                else
                                {
                                    new_block = ntk.create_and(critical_signal, ntk.create_or(grandchildren[0], grandchildren[1]));
                                }

                                ntk.substitute_node(n, new_block);  // substitute the new net
                                return true;
                            }
                            else    // appears on one branch only
                            {
                                signal critical_signal = grandchildren[i];
                                signal new_block;

                                grandchildren.erase(grandchildren.begin() + i);     // remove critical from the vector

                                if(ntk.is_on_critical_path(ntk.get_node(grandchildren[0])) || ntk.is_on_critical_path(ntk.get_node(grandchildren[1])))
                                {
                                    return false;   // distributivity is not convenient
                                }

                                if(ntk.is_and(n))   // create new net
                                {
                                    new_block = ntk.create_and(ntk.create_not(critical_signal), ntk.create_nand(grandchildren[0], grandchildren[1]));
                                }
                                else
                                {
                                    new_block = ntk.create_nand(ntk.create_not(critical_signal), ntk.create_nand(grandchildren[0], grandchildren[1]));
                                }
                                
                                ntk.substitute_node(n, new_block);  // substitute the new net
                                return true;
                            }
                        }
                        else
                        {
                            return false;   // recurrent signal is not critical
                        }
                    }
                }
                // a b c
                break;
            }
            case 4:
            {
                return false;   // no common signal, no distributivity can be applied
            }
            default:
            {
                std::cerr << "Unknown error." << std::endl;
                break;
            }
        }

        return false;
    }

    bool try_three_layer_distributivity( node n )
    {
        signal critical_child;
        signal non_critical_child;
        signal critical_grandchild;
        signal non_critical_grandchild;
        signal critical_grandgrandchild;
        signal non_critical_grandgrandchild;
        signal new_block;
        int n_critical = 0;

        ntk.foreach_fanin(n, [&](signal child)      // function called for every input
        {
            if(ntk.is_on_critical_path(ntk.get_node(child)))
            {
                critical_child = child;
                n_critical++;
            }
            else
            {
                non_critical_child = child;
            }
        });

        if(n_critical != 1)
        {
            return false;   // three layer distributivity not convenient
        }

        if(!ntk.is_complemented(critical_child))
        {
            return false;   // three layer distributivity does not apply
        }

        if((ntk.level(ntk.get_node(critical_child)) - ntk.level(ntk.get_node(non_critical_child))) < 3)
        {
            return false;   // three layer distributivity not convenient
        }

        n_critical = 0;

        ntk.foreach_fanin(ntk.get_node(critical_child), [&](signal grandchild)      // function called for every input
        {
            if(ntk.is_on_critical_path(ntk.get_node(grandchild)))
            {
                critical_grandchild = grandchild;
                n_critical++;
            }
            else
            {
                non_critical_grandchild = grandchild;
            }
        });

        if(n_critical != 1)
        {
            return false;   // three layer distributivity not convenient
        }

        if(!ntk.is_complemented(critical_grandchild))
        {
            return false;   // three layer distributivity does not apply
        }

        n_critical = 0;

        ntk.foreach_fanin(ntk.get_node(critical_grandchild), [&](signal grandgrandchild)      // function called for every input
        {
            if(ntk.is_on_critical_path(ntk.get_node(grandgrandchild)))
            {
                critical_grandgrandchild = grandgrandchild;
                n_critical++;
            }
            else
            {
                non_critical_grandgrandchild = grandgrandchild;
            }
        });

        if(n_critical != 1)
        {
            return false;   // three layer distributivity not convenient
        }

        new_block = ntk.create_or(ntk.create_and(critical_grandgrandchild, ntk.create_and(non_critical_grandgrandchild, non_critical_child)), ntk.create_and(ntk.create_not(non_critical_grandchild), non_critical_child));

        if(!ntk.is_and(n))   // create new net
        {
            new_block = ntk.create_not(new_block);
        }

        ntk.substitute_node(n, new_block);
        return true;
    }



private:
  Ntk& ntk;
};

} // namespace detail

/* Entry point for users to call */
template<class Ntk>
void aig_algebraic_rewriting( Ntk& ntk )
{
  static_assert( std::is_same_v<typename Ntk::base_type, aig_network>, "Ntk is not an AIG" );

  depth_view dntk{ntk};
  detail::aig_algebraic_rewriting_impl p( dntk );
  p.run();
}

} /* namespace mockturtle */

