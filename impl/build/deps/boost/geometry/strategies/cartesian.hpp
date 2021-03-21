// Boost.Geometry

// Copyright (c) 2020, Oracle and/or its affiliates.

// Contributed and/or modified by Adam Wulkiewicz, on behalf of Oracle

// Licensed under the Boost Software License version 1.0.
// http://www.boost.org/users/license.html

#ifndef BOOST_GEOMETRY_STRATEGIES_CARTESIAN_HPP
#define BOOST_GEOMETRY_STRATEGIES_CARTESIAN_HPP


#include <boost/geometry/strategies/area/cartesian.hpp>
#include <boost/geometry/strategies/envelope/cartesian.hpp>
#include <boost/geometry/strategies/expand/cartesian.hpp>


namespace boost { namespace geometry
{

    
namespace strategies
{


template <typename CalculationType = void>
struct cartesian : strategies::detail::cartesian_base
{
    // area

    template <typename Geometry>
    static auto area(Geometry const&)
    {
        return strategy::area::cartesian<CalculationType>();
    }

    // envelope

    template <typename Geometry, typename Box>
    static auto envelope(Geometry const&, Box const&,
                         typename util::enable_if_point_t<Geometry> * = nullptr)
    {
        return strategy::envelope::cartesian_point();
    }

    template <typename Geometry, typename Box>
    static auto envelope(Geometry const&, Box const&,
                         typename util::enable_if_multi_point_t<Geometry> * = nullptr)
    {
        return strategy::envelope::cartesian_multipoint();
    }

    template <typename Geometry, typename Box>
    static auto envelope(Geometry const&, Box const&,
                         typename util::enable_if_box_t<Geometry> * = nullptr)
    {
        return strategy::envelope::cartesian_box();
    }

    template <typename Geometry, typename Box>
    static auto envelope(Geometry const&, Box const&,
                         typename util::enable_if_segment_t<Geometry> * = nullptr)
    {
        return strategy::envelope::cartesian_segment<CalculationType>();
    }

    template <typename Geometry, typename Box>
    static auto envelope(Geometry const&, Box const&,
                         typename util::enable_if_polysegmental_t<Geometry> * = nullptr)
    {
        return strategy::envelope::cartesian<CalculationType>();
    }

    // expand

    template <typename Box, typename Geometry>
    static auto expand(Box const&, Geometry const&,
                       typename util::enable_if_point_t<Geometry> * = nullptr)
    {
        return strategy::expand::cartesian_point();
    }

    template <typename Box, typename Geometry>
    static auto expand(Box const&, Geometry const&,
                       typename util::enable_if_box_t<Geometry> * = nullptr)
    {
        return strategy::expand::cartesian_box();
    }

    template <typename Box, typename Geometry>
    static auto expand(Box const&, Geometry const&,
                       typename util::enable_if_segment_t<Geometry> * = nullptr)
    {
        return strategy::expand::cartesian_segment();
    }
};


} // namespace strategies


}} // namespace boost::geometry


#endif // BOOST_GEOMETRY_STRATEGIES_CARTESIAN_HPP
