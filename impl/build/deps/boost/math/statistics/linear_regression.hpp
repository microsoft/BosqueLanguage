/*
 * Copyright Nick Thompson, 2019
 * Use, modification and distribution are subject to the
 * Boost Software License, Version 1.0. (See accompanying file
 * LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)
 */

#ifndef BOOST_MATH_STATISTICS_LINEAR_REGRESSION_HPP
#define BOOST_MATH_STATISTICS_LINEAR_REGRESSION_HPP

#include <cmath>
#include <algorithm>
#include <utility>
#include <boost/math/statistics/univariate_statistics.hpp>
#include <boost/math/statistics/bivariate_statistics.hpp>

namespace boost::math::statistics {


template<class RandomAccessContainer>
auto simple_ordinary_least_squares(RandomAccessContainer const & x,
                                   RandomAccessContainer const & y)
{
    using Real = typename RandomAccessContainer::value_type;
    if (x.size() <= 1)
    {
        throw std::domain_error("At least 2 samples are required to perform a linear regression.");
    }

    if (x.size() != y.size())
    {
        throw std::domain_error("The same number of samples must be in the independent and dependent variable.");
    }
    auto [mu_x, mu_y, cov_xy] = boost::math::statistics::means_and_covariance(x, y);

    auto var_x = boost::math::statistics::variance(x);

    if (var_x <= 0) {
        throw std::domain_error("Independent variable has no variance; this breaks linear regression.");
    }


    Real c1 = cov_xy/var_x;
    Real c0 = mu_y - c1*mu_x;

    return std::make_pair(c0, c1);
}

template<class RandomAccessContainer>
auto simple_ordinary_least_squares_with_R_squared(RandomAccessContainer const & x,
                                   RandomAccessContainer const & y)
{
    using Real = typename RandomAccessContainer::value_type;
    if (x.size() <= 1)
    {
        throw std::domain_error("At least 2 samples are required to perform a linear regression.");
    }

    if (x.size() != y.size())
    {
        throw std::domain_error("The same number of samples must be in the independent and dependent variable.");
    }
    auto [mu_x, mu_y, cov_xy] = boost::math::statistics::means_and_covariance(x, y);

    auto var_x = boost::math::statistics::variance(x);

    if (var_x <= 0) {
        throw std::domain_error("Independent variable has no variance; this breaks linear regression.");
    }


    Real c1 = cov_xy/var_x;
    Real c0 = mu_y - c1*mu_x;

    Real squared_residuals = 0;
    Real squared_mean_deviation = 0;
    for(decltype(y.size()) i = 0; i < y.size(); ++i) {
        squared_mean_deviation += (y[i] - mu_y)*(y[i]-mu_y);
        Real ei = (c0 + c1*x[i]) - y[i];
        squared_residuals += ei*ei;
    }

    Real Rsquared;
    if (squared_mean_deviation == 0) {
        // Then y = constant, so the linear regression is perfect.
        Rsquared = 1;
    } else {
        Rsquared = 1 - squared_residuals/squared_mean_deviation;
    }

    return std::make_tuple(c0, c1, Rsquared);
}

}
#endif
