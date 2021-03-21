// Boost.Geometry

// Copyright (c) 2020, Oracle and/or its affiliates.

// Contributed and/or modified by Adam Wulkiewicz, on behalf of Oracle

// Licensed under the Boost Software License version 1.0.
// http://www.boost.org/users/license.html

#ifndef BOOST_GEOMETRY_STRATEGIES_GEOGRAPHIC_HPP
#define BOOST_GEOMETRY_STRATEGIES_GEOGRAPHIC_HPP


#include <boost/geometry/strategies/area/geographic.hpp>
#include <boost/geometry/strategies/envelope/geographic.hpp>
#include <boost/geometry/strategies/expand/geographic.hpp>


namespace boost { namespace geometry
{

    
namespace strategies
{


template
<
    typename FormulaPolicy = strategy::andoyer,
    std::size_t SeriesOrder = strategy::default_order<FormulaPolicy>::value,
    typename Spheroid = srs::spheroid<double>,
    typename CalculationType = void
>
class geographic : strategies::detail::geographic_base<Spheroid>
{
    using base_t = strategies::detail::geographic_base<Spheroid>;

public:
    geographic()
        : base_t()
    {}

    explicit geographic(Spheroid const& spheroid)
        : base_t(spheroid)
    {}

    // area

    template <typename Geometry>
    auto area(Geometry const&) const
    {
        return strategy::area::geographic
            <
                FormulaPolicy, SeriesOrder, Spheroid, CalculationType
            >(base_t::m_spheroid);
    }

    // envelope

    template <typename Geometry, typename Box>
    static auto envelope(Geometry const&, Box const&,
                         typename util::enable_if_point_t<Geometry> * = nullptr)
    {
        return strategy::envelope::spherical_point();
    }

    template <typename Geometry, typename Box>
    static auto envelope(Geometry const&, Box const&,
                         typename util::enable_if_multi_point_t<Geometry> * = nullptr)
    {
        return strategy::envelope::spherical_multipoint();
    }

    template <typename Geometry, typename Box>
    static auto envelope(Geometry const&, Box const&,
                         typename util::enable_if_box_t<Geometry> * = nullptr)
    {
        return strategy::envelope::spherical_box();
    }

    template <typename Geometry, typename Box>
    auto envelope(Geometry const&, Box const&,
                  typename util::enable_if_segment_t<Geometry> * = nullptr) const
    {
        return strategy::envelope::geographic_segment
            <
                FormulaPolicy, Spheroid, CalculationType
            >(base_t::m_spheroid);
    }

    template <typename Geometry, typename Box>
    auto envelope(Geometry const&, Box const&,
                  typename util::enable_if_polysegmental_t<Geometry> * = nullptr) const
    {
        return strategy::envelope::geographic
            <
                FormulaPolicy, Spheroid, CalculationType
            >(base_t::m_spheroid);
    }

    // expand

    template <typename Box, typename Geometry>
    static auto expand(Box const&, Geometry const&,
                       typename util::enable_if_point_t<Geometry> * = nullptr)
    {
        return strategy::expand::spherical_point();
    }

    template <typename Box, typename Geometry>
    static auto expand(Box const&, Geometry const&,
                       typename util::enable_if_box_t<Geometry> * = nullptr)
    {
        return strategy::expand::spherical_box();
    }

    template <typename Box, typename Geometry>
    auto expand(Box const&, Geometry const&,
                typename util::enable_if_segment_t<Geometry> * = nullptr) const
    {
        return strategy::expand::geographic_segment
            <
                FormulaPolicy, Spheroid, CalculationType
            >(base_t::m_spheroid);
    }
};


} // namespace strategies


}} // namespace boost::geometry


#endif // BOOST_GEOMETRY_STRATEGIES_GEOGRAPHIC_HPP
