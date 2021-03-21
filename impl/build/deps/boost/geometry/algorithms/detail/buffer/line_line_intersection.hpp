// Boost.Geometry (aka GGL, Generic Geometry Library)

// Copyright (c) 2012-2020 Barend Gehrels, Amsterdam, the Netherlands.

// Use, modification and distribution is subject to the Boost Software License,
// Version 1.0. (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)

#ifndef BOOST_GEOMETRY_ALGORITHMS_DETAIL_BUFFER_LINE_LINE_INTERSECTION_HPP
#define BOOST_GEOMETRY_ALGORITHMS_DETAIL_BUFFER_LINE_LINE_INTERSECTION_HPP

#include <boost/geometry/core/assert.hpp>
#include <boost/geometry/arithmetic/infinite_line_functions.hpp>
#include <boost/geometry/algorithms/detail/make/make.hpp>

#include <boost/core/ignore_unused.hpp>


namespace boost { namespace geometry
{


#ifndef DOXYGEN_NO_DETAIL
namespace detail { namespace buffer
{

// TODO: this might once be changed to a proper strategy
struct line_line_intersection
{
    template <typename Point>
    static inline bool
    apply(Point const& pi, Point const& pj, Point const& qi, Point const& qj,
          Point& ip)
    {
        typedef typename coordinate_type<Point>::type ct;
        typedef model::infinite_line<ct> line_type;

        line_type const p = detail::make::make_infinite_line<ct>(pi, pj);
        line_type const q = detail::make::make_infinite_line<ct>(qi, qj);

        // The input lines are not parallel, they intersect, because
        // their join type is checked before.
        return arithmetic::intersection_point(p, q, ip);
    }
};


}} // namespace detail::buffer
#endif // DOXYGEN_NO_DETAIL


}} // namespace boost::geometry


#endif // BOOST_GEOMETRY_ALGORITHMS_DETAIL_BUFFER_LINE_LINE_INTERSECTION_HPP
