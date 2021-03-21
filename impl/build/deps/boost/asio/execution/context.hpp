//
// execution/context.hpp
// ~~~~~~~~~~~~~~~~~~~~~
//
// Copyright (c) 2003-2020 Christopher M. Kohlhoff (chris at kohlhoff dot com)
//
// Distributed under the Boost Software License, Version 1.0. (See accompanying
// file LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)
//

#ifndef BOOST_ASIO_EXECUTION_CONTEXT2_HPP
#define BOOST_ASIO_EXECUTION_CONTEXT2_HPP

#if defined(_MSC_VER) && (_MSC_VER >= 1200)
# pragma once
#endif // defined(_MSC_VER) && (_MSC_VER >= 1200)

#include <boost/asio/detail/config.hpp>
#include <boost/asio/detail/type_traits.hpp>
#include <boost/asio/execution/executor.hpp>
#include <boost/asio/execution/scheduler.hpp>
#include <boost/asio/execution/sender.hpp>
#include <boost/asio/is_applicable_property.hpp>
#include <boost/asio/traits/query_static_constexpr_member.hpp>
#include <boost/asio/traits/static_query.hpp>

#if defined(BOOST_ASIO_HAS_STD_ANY)
# include <any>
#endif // defined(BOOST_ASIO_HAS_STD_ANY)

#include <boost/asio/detail/push_options.hpp>

namespace boost {
namespace asio {

#if defined(GENERATING_DOCUMENTATION)

namespace execution {

/// A property that is used to obtain the execution context that is associated
/// with an executor.
struct context_t
{
  /// The context_t property applies to executors, senders, and schedulers.
  template <typename T>
  static constexpr bool is_applicable_property_v =
    is_executor_v<T> || is_sender_v<T> || is_scheduler_v<T>;

  /// The context_t property cannot be required.
  static constexpr bool is_requirable = false;

  /// The context_t property cannot be preferred.
  static constexpr bool is_preferable = false;

  /// The type returned by queries against an @c any_executor.
  typedef std::any polymorphic_query_result_type;
};

/// A special value used for accessing the context_t property.
constexpr context_t context;

} // namespace execution

#else // defined(GENERATING_DOCUMENTATION)

namespace execution {
namespace detail {

template <int I = 0>
struct context_t
{
#if defined(BOOST_ASIO_HAS_VARIABLE_TEMPLATES)
  template <typename T>
  BOOST_ASIO_STATIC_CONSTEXPR(bool,
    is_applicable_property_v = is_executor<T>::value
      || is_sender<T>::value || is_scheduler<T>::value);
#endif // defined(BOOST_ASIO_HAS_VARIABLE_TEMPLATES)

  BOOST_ASIO_STATIC_CONSTEXPR(bool, is_requirable = false);
  BOOST_ASIO_STATIC_CONSTEXPR(bool, is_preferable = false);

#if defined(BOOST_ASIO_HAS_STD_ANY)
  typedef std::any polymorphic_query_result_type;
#endif // defined(BOOST_ASIO_HAS_STD_ANY)

  BOOST_ASIO_CONSTEXPR context_t()
  {
  }

#if defined(BOOST_ASIO_HAS_DEDUCED_STATIC_QUERY_TRAIT) \
  && defined(BOOST_ASIO_HAS_SFINAE_VARIABLE_TEMPLATES)
  template <typename T>
  static BOOST_ASIO_CONSTEXPR
  typename traits::query_static_constexpr_member<T, context_t>::result_type
  static_query()
    BOOST_ASIO_NOEXCEPT_IF((
      traits::query_static_constexpr_member<T, context_t>::is_noexcept))
  {
    return traits::query_static_constexpr_member<T, context_t>::value();
  }

  template <typename E, typename T = decltype(context_t::static_query<E>())>
  static BOOST_ASIO_CONSTEXPR const T static_query_v
    = context_t::static_query<E>();
#endif // defined(BOOST_ASIO_HAS_DEDUCED_STATIC_QUERY_TRAIT)
       //   && defined(BOOST_ASIO_HAS_SFINAE_VARIABLE_TEMPLATES)

#if !defined(BOOST_ASIO_HAS_CONSTEXPR)
  static const context_t instance;
#endif // !defined(BOOST_ASIO_HAS_CONSTEXPR)
};

#if defined(BOOST_ASIO_HAS_DEDUCED_STATIC_QUERY_TRAIT) \
  && defined(BOOST_ASIO_HAS_SFINAE_VARIABLE_TEMPLATES)
template <int I> template <typename E, typename T>
const T context_t<I>::static_query_v;
#endif // defined(BOOST_ASIO_HAS_DEDUCED_STATIC_QUERY_TRAIT)
       //   && defined(BOOST_ASIO_HAS_SFINAE_VARIABLE_TEMPLATES)

#if !defined(BOOST_ASIO_HAS_CONSTEXPR)
template <int I>
const context_t<I> context_t<I>::instance;
#endif

} // namespace detail

typedef detail::context_t<> context_t;

#if defined(BOOST_ASIO_HAS_CONSTEXPR) || defined(GENERATING_DOCUMENTATION)
constexpr context_t context;
#else // defined(BOOST_ASIO_HAS_CONSTEXPR) || defined(GENERATING_DOCUMENTATION)
namespace { static const context_t& context = context_t::instance; }
#endif

} // namespace execution

#if !defined(BOOST_ASIO_HAS_VARIABLE_TEMPLATES)

template <typename T>
struct is_applicable_property<T, execution::context_t>
  : integral_constant<bool,
      execution::is_executor<T>::value
        || execution::is_sender<T>::value
        || execution::is_scheduler<T>::value>
{
};

#endif // !defined(BOOST_ASIO_HAS_VARIABLE_TEMPLATES)

namespace traits {

#if !defined(BOOST_ASIO_HAS_DEDUCED_STATIC_QUERY_TRAIT) \
  || !defined(BOOST_ASIO_HAS_SFINAE_VARIABLE_TEMPLATES)

template <typename T>
struct static_query<T, execution::context_t,
  typename enable_if<
    traits::query_static_constexpr_member<T,
      execution::context_t>::is_valid
  >::type>
{
  BOOST_ASIO_STATIC_CONSTEXPR(bool, is_valid = true);
  BOOST_ASIO_STATIC_CONSTEXPR(bool, is_noexcept = true);

  typedef typename traits::query_static_constexpr_member<T,
    execution::context_t>::result_type result_type;

  static BOOST_ASIO_CONSTEXPR result_type value()
  {
    return traits::query_static_constexpr_member<T,
      execution::context_t>::value();
  }
};

#endif // !defined(BOOST_ASIO_HAS_DEDUCED_STATIC_QUERY_TRAIT)
       //   || !defined(BOOST_ASIO_HAS_SFINAE_VARIABLE_TEMPLATES)

} // namespace traits

#endif // defined(GENERATING_DOCUMENTATION)

} // namespace asio
} // namespace boost

#include <boost/asio/detail/pop_options.hpp>

#endif // BOOST_ASIO_EXECUTION_CONTEXT2_HPP
