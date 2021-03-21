#ifndef BOOST_LEAF_HPP_INCLUDED
#define BOOST_LEAF_HPP_INCLUDED

// Copyright (c) 2018-2020 Emil Dotchevski and Reverge Studios, Inc.

// Distributed under the Boost Software License, Version 1.0. (See accompanying
// file LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)

// >>> #include <boost/leaf/capture.hpp>
#line 1 "boost/leaf/capture.hpp"
#ifndef BOOST_LEAF_CAPTURE_HPP_INCLUDED
#define BOOST_LEAF_CAPTURE_HPP_INCLUDED

// Copyright (c) 2018-2020 Emil Dotchevski and Reverge Studios, Inc.

// Distributed under the Boost Software License, Version 1.0. (See accompanying
// file LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)

#ifndef BOOST_LEAF_ENABLE_WARNINGS
#   if defined(__clang__)
#       pragma clang system_header
#   elif (__GNUC__*100+__GNUC_MINOR__>301)
#       pragma GCC system_header
#   elif defined(_MSC_VER)
#       pragma warning(push,1)
#   endif
#endif

// >>> #include <boost/leaf/exception.hpp>
#line 1 "boost/leaf/exception.hpp"
#ifndef BOOST_LEAF_EXCEPTION_HPP_INCLUDED
#define BOOST_LEAF_EXCEPTION_HPP_INCLUDED

// Copyright (c) 2018-2020 Emil Dotchevski and Reverge Studios, Inc.

// Distributed under the Boost Software License, Version 1.0. (See accompanying
// file LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)

#ifndef BOOST_LEAF_ENABLE_WARNINGS
#   if defined(__clang__)
#       pragma clang system_header
#   elif (__GNUC__*100+__GNUC_MINOR__>301)
#       pragma GCC system_header
#   elif defined(_MSC_VER)
#       pragma warning(push,1)
#   endif
#endif

// >>> #include <boost/leaf/error.hpp>
#line 1 "boost/leaf/error.hpp"
#ifndef BOOST_LEAF_ERROR_HPP_INCLUDED
#define BOOST_LEAF_ERROR_HPP_INCLUDED

// Copyright (c) 2018-2020 Emil Dotchevski and Reverge Studios, Inc.

// Distributed under the Boost Software License, Version 1.0. (See accompanying
// file LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)

#ifndef BOOST_LEAF_ENABLE_WARNINGS
#   if defined(__clang__)
#       pragma clang system_header
#   elif (__GNUC__*100+__GNUC_MINOR__>301)
#       pragma GCC system_header
#   elif defined(_MSC_VER)
#       pragma warning(push,1)
#   endif
#endif

// >>> #include <boost/leaf/detail/function_traits.hpp>
#line 1 "boost/leaf/detail/function_traits.hpp"
#ifndef BOOST_LEAF_DETAIL_FUNCTION_TRAITS_HPP_INCLUDED
#define BOOST_LEAF_DETAIL_FUNCTION_TRAITS_HPP_INCLUDED

// Copyright (c) 2018-2020 Emil Dotchevski and Reverge Studios, Inc.

// Distributed under the Boost Software License, Version 1.0. (See accompanying
// file LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)

#ifndef BOOST_LEAF_ENABLE_WARNINGS
#   if defined(__clang__)
#       pragma clang system_header
#   elif (__GNUC__*100+__GNUC_MINOR__>301)
#       pragma GCC system_header
#   elif defined(_MSC_VER)
#       pragma warning(push,1)
#   endif
#endif

// >>> #include <boost/leaf/detail/mp11.hpp>
#line 1 "boost/leaf/detail/mp11.hpp"
#ifndef BOOST_LEAF_DETAIL_MP11_HPP_INCLUDED
#define BOOST_LEAF_DETAIL_MP11_HPP_INCLUDED

//  Copyright 2015-2017 Peter Dimov.
//  Copyright 2019 Emil Dotchevski.
//
//  Distributed under the Boost Software License, Version 1.0.
//
//  See accompanying file LICENSE_1_0.txt or copy at
//  http://www.boost.org/LICENSE_1_0.txt

#include <type_traits>
#include <cstddef>

namespace boost { namespace leaf { namespace leaf_detail_mp11 {

// mp_list<T...>
template<class... T> struct mp_list
{
};

// mp_identity
template<class T> struct mp_identity
{
    using type = T;
};

// mp_inherit
template<class... T> struct mp_inherit: T... {};

// mp_if, mp_if_c
namespace detail
{

template<bool C, class T, class... E> struct mp_if_c_impl
{
};

template<class T, class... E> struct mp_if_c_impl<true, T, E...>
{
    using type = T;
};

template<class T, class E> struct mp_if_c_impl<false, T, E>
{
    using type = E;
};

} // namespace detail

template<bool C, class T, class... E> using mp_if_c = typename detail::mp_if_c_impl<C, T, E...>::type;
template<class C, class T, class... E> using mp_if = typename detail::mp_if_c_impl<static_cast<bool>(C::value), T, E...>::type;

// mp_bool
template<bool B> using mp_bool = std::integral_constant<bool, B>;

using mp_true = mp_bool<true>;
using mp_false = mp_bool<false>;

// mp_to_bool
template<class T> using mp_to_bool = mp_bool<static_cast<bool>( T::value )>;

// mp_not<T>
template<class T> using mp_not = mp_bool< !T::value >;

// mp_int
template<int I> using mp_int = std::integral_constant<int, I>;

// mp_size_t
template<std::size_t N> using mp_size_t = std::integral_constant<std::size_t, N>;

// mp_set_contains<S, V>
namespace detail
{

template<class S, class V> struct mp_set_contains_impl;

template<template<class...> class L, class... T, class V> struct mp_set_contains_impl<L<T...>, V>
{
    using type = mp_to_bool<std::is_base_of<mp_identity<V>, mp_inherit<mp_identity<T>...> > >;
};

} // namespace detail

template<class S, class V> using mp_set_contains = typename detail::mp_set_contains_impl<S, V>::type;

// mp_set_push_back<S, T...>
namespace detail
{

template<class S, class... T> struct mp_set_push_back_impl;

template<template<class...> class L, class... U> struct mp_set_push_back_impl<L<U...>>
{
    using type = L<U...>;
};

template<template<class...> class L, class... U, class T1, class... T> struct mp_set_push_back_impl<L<U...>, T1, T...>
{
    using S = mp_if<mp_set_contains<L<U...>, T1>, L<U...>, L<U..., T1>>;
    using type = typename mp_set_push_back_impl<S, T...>::type;
};

} // namespace detail

template<class S, class... T> using mp_set_push_back = typename detail::mp_set_push_back_impl<S, T...>::type;

// mp_unique<L>
namespace detail
{

template<class L> struct mp_unique_impl;

template<template<class...> class L, class... T> struct mp_unique_impl<L<T...>>
{
    using type = mp_set_push_back<L<>, T...>;
};

} // namespace detail

template<class L> using mp_unique = typename detail::mp_unique_impl<L>::type;

// mp_append<L...>

namespace detail
{

template<class... L> struct mp_append_impl;

template<> struct mp_append_impl<>
{
    using type = mp_list<>;
};

template<template<class...> class L, class... T> struct mp_append_impl<L<T...>>
{
    using type = L<T...>;
};

template<template<class...> class L1, class... T1, template<class...> class L2, class... T2, class... Lr> struct mp_append_impl<L1<T1...>, L2<T2...>, Lr...>
{
    using type = typename mp_append_impl<L1<T1..., T2...>, Lr...>::type;
};

}

template<class... L> using mp_append = typename detail::mp_append_impl<L...>::type;

// mp_front<L>
namespace detail
{

template<class L> struct mp_front_impl
{
// An error "no type named 'type'" here means that the argument to mp_front
// is either not a list, or is an empty list
};

template<template<class...> class L, class T1, class... T> struct mp_front_impl<L<T1, T...>>
{
    using type = T1;
};

} // namespace detail

template<class L> using mp_front = typename detail::mp_front_impl<L>::type;

// mp_pop_front<L>
namespace detail
{

template<class L> struct mp_pop_front_impl
{
// An error "no type named 'type'" here means that the argument to mp_pop_front
// is either not a list, or is an empty list
};

template<template<class...> class L, class T1, class... T> struct mp_pop_front_impl<L<T1, T...>>
{
    using type = L<T...>;
};

} // namespace detail

template<class L> using mp_pop_front = typename detail::mp_pop_front_impl<L>::type;

// mp_first<L>
template<class L> using mp_first = mp_front<L>;

// mp_rest<L>
template<class L> using mp_rest = mp_pop_front<L>;

// mp_remove_if<L, P>
namespace detail
{

template<class L, template<class...> class P> struct mp_remove_if_impl;

template<template<class...> class L, class... T, template<class...> class P> struct mp_remove_if_impl<L<T...>, P>
{
    template<class U> using _f = mp_if<P<U>, mp_list<>, mp_list<U>>;
    using type = mp_append<L<>, _f<T>...>;
};

} // namespace detail

template<class L, template<class...> class P> using mp_remove_if = typename detail::mp_remove_if_impl<L, P>::type;

// integer_sequence
template<class T, T... I> struct integer_sequence
{
};

// detail::make_integer_sequence_impl
namespace detail
{

// iseq_if_c
template<bool C, class T, class E> struct iseq_if_c_impl;

template<class T, class E> struct iseq_if_c_impl<true, T, E>
{
    using type = T;
};

template<class T, class E> struct iseq_if_c_impl<false, T, E>
{
    using type = E;
};

template<bool C, class T, class E> using iseq_if_c = typename iseq_if_c_impl<C, T, E>::type;

// iseq_identity
template<class T> struct iseq_identity
{
    using type = T;
};

template<class S1, class S2> struct append_integer_sequence;

template<class T, T... I, T... J> struct append_integer_sequence<integer_sequence<T, I...>, integer_sequence<T, J...>>
{
    using type = integer_sequence< T, I..., ( J + sizeof...(I) )... >;
};

template<class T, T N> struct make_integer_sequence_impl;

template<class T, T N> struct make_integer_sequence_impl_
{
private:

    static_assert( N >= 0, "make_integer_sequence<T, N>: N must not be negative" );

    static T const M = N / 2;
    static T const R = N % 2;

    using S1 = typename make_integer_sequence_impl<T, M>::type;
    using S2 = typename append_integer_sequence<S1, S1>::type;
    using S3 = typename make_integer_sequence_impl<T, R>::type;
    using S4 = typename append_integer_sequence<S2, S3>::type;

public:

    using type = S4;
};

template<class T, T N> struct make_integer_sequence_impl: iseq_if_c<N == 0, iseq_identity<integer_sequence<T>>, iseq_if_c<N == 1, iseq_identity<integer_sequence<T, 0>>, make_integer_sequence_impl_<T, N> > >
{
};

} // namespace detail

// make_integer_sequence
template<class T, T N> using make_integer_sequence = typename detail::make_integer_sequence_impl<T, N>::type;

// index_sequence
template<std::size_t... I> using index_sequence = integer_sequence<std::size_t, I...>;

// make_index_sequence
template<std::size_t N> using make_index_sequence = make_integer_sequence<std::size_t, N>;

// index_sequence_for
template<class... T> using index_sequence_for = make_integer_sequence<std::size_t, sizeof...(T)>;

// implementation by Bruno Dutra (by the name is_evaluable)
namespace detail
{

template<template<class...> class F, class... T> struct mp_valid_impl
{
    template<template<class...> class G, class = G<T...>> static mp_true check(int);
    template<template<class...> class> static mp_false check(...);

    using type = decltype(check<F>(0));
};

} // namespace detail

template<template<class...> class F, class... T> using mp_valid = typename detail::mp_valid_impl<F, T...>::type;

} } }

#endif
// <<< #include <boost/leaf/detail/mp11.hpp>
#line 20 "boost/leaf/detail/function_traits.hpp"
#include <tuple>

namespace boost { namespace leaf {

    namespace leaf_detail
    {
        template<class...>
        struct gcc49_workaround //Thanks Glen Fernandes
        {
            using type = void;
        };

        template<class... T>
        using void_t = typename gcc49_workaround<T...>::type;

        template<class F,class V=void>
        struct function_traits
        {
            constexpr static int arity = -1;
        };

        template<class F>
        struct function_traits<F, void_t<decltype(&F::operator())>>
        {
        private:

            using tr = function_traits<decltype(&F::operator())>;

        public:

            using return_type = typename tr::return_type;
            static constexpr int arity = tr::arity - 1;

            using mp_args = typename leaf_detail_mp11::mp_rest<typename tr::mp_args>;

            template <int I>
            struct arg:
                tr::template arg<I+1>
            {
            };
        };

        template<class R, class... A>
        struct function_traits<R(A...)>
        {
            using return_type = R;
            static constexpr int arity = sizeof...(A);

            using mp_args = leaf_detail_mp11::mp_list<A...>;

            template <int I>
            struct arg
            {
                static_assert(I < arity, "I out of range");
                using type = typename std::tuple_element<I,std::tuple<A...>>::type;
            };
        };

        template<class F> struct function_traits<F&> : function_traits<F> { };
        template<class F> struct function_traits<F&&> : function_traits<F> { };
        template<class R, class... A> struct function_traits<R(*)(A...)> : function_traits<R(A...)> { };
        template<class R, class... A> struct function_traits<R(* &)(A...)> : function_traits<R(A...)> { };
        template<class R, class... A> struct function_traits<R(* const &)(A...)> : function_traits<R(A...)> { };
        template<class C, class R, class... A> struct function_traits<R(C::*)(A...)> : function_traits<R(C&,A...)> { };
        template<class C, class R, class... A> struct function_traits<R(C::*)(A...) const> : function_traits<R(C const &,A...)> { };
        template<class C, class R> struct function_traits<R(C::*)> : function_traits<R(C&)> { };

        template <class F>
        using fn_return_type = typename function_traits<F>::return_type;

        template <class F, int I>
        using fn_arg_type = typename function_traits<F>::template arg<I>::type;

        template <class F>
        using fn_mp_args = typename function_traits<F>::mp_args;

    }

} }

#endif
// <<< #include <boost/leaf/detail/function_traits.hpp>
#line 20 "boost/leaf/error.hpp"
// >>> #include <boost/leaf/detail/print.hpp>
#line 1 "boost/leaf/detail/print.hpp"
#ifndef BOOST_LEAF_DETAIL_PRINT_HPP_INCLUDED
#define BOOST_LEAF_DETAIL_PRINT_HPP_INCLUDED

// Copyright (c) 2018-2020 Emil Dotchevski and Reverge Studios, Inc.

// Distributed under the Boost Software License, Version 1.0. (See accompanying
// file LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)

#ifndef BOOST_LEAF_ENABLE_WARNINGS
#   if defined(__clang__)
#       pragma clang system_header
#   elif (__GNUC__*100+__GNUC_MINOR__>301)
#       pragma GCC system_header
#   elif defined(_MSC_VER)
#       pragma warning(push,1)
#   endif
#endif

// >>> #include <boost/leaf/detail/optional.hpp>
#line 1 "boost/leaf/detail/optional.hpp"
#ifndef BOOST_LEAF_DETAIL_OPTIONAL_HPP_INCLUDED
#define BOOST_LEAF_DETAIL_OPTIONAL_HPP_INCLUDED

// Copyright (c) 2018-2020 Emil Dotchevski and Reverge Studios, Inc.

// Distributed under the Boost Software License, Version 1.0. (See accompanying
// file LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)

#ifndef BOOST_LEAF_ENABLE_WARNINGS
#   if defined(__clang__)
#       pragma clang system_header
#   elif (__GNUC__*100+__GNUC_MINOR__>301)
#       pragma GCC system_header
#   elif defined(_MSC_VER)
#       pragma warning(push,1)
#   endif
#endif

// >>> #include <boost/leaf/detail/config.hpp>
#line 1 "boost/leaf/detail/config.hpp"
#ifndef BOOST_LEAF_CONFIG_HPP_INCLUDED
#define BOOST_LEAF_CONFIG_HPP_INCLUDED

// Copyright (c) 2018-2020 Emil Dotchevski and Reverge Studios, Inc.

// Distributed under the Boost Software License, Version 1.0. (See accompanying
// file LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)

// The following is based on Boost Config.

// (C) Copyright John Maddock 2001 - 2003.
// (C) Copyright Martin Wille 2003.
// (C) Copyright Guillaume Melquiond 2003.

#ifndef BOOST_LEAF_ENABLE_WARNINGS
#   if defined(__clang__)
#       pragma clang system_header
#   elif (__GNUC__*100+__GNUC_MINOR__>301)
#       pragma GCC system_header
#   elif defined(_MSC_VER)
#       pragma warning(push,1)
#   endif
#endif

////////////////////////////////////////

// Configure BOOST_LEAF_NO_EXCEPTIONS, unless already #defined
#ifndef BOOST_LEAF_NO_EXCEPTIONS

#   if defined(__clang__) && !defined(__ibmxl__)
//  Clang C++ emulates GCC, so it has to appear early.

#       if !__has_feature(cxx_exceptions)
#           define BOOST_LEAF_NO_EXCEPTIONS
#       endif

#   elif defined(__DMC__)
//  Digital Mars C++

#       if !defined(_CPPUNWIND)
#           define BOOST_LEAF_NO_EXCEPTIONS
#       endif

#   elif defined(__GNUC__) && !defined(__ibmxl__)
//  GNU C++:

#       if !defined(__EXCEPTIONS)
#           define BOOST_LEAF_NO_EXCEPTIONS
#       endif

#   elif defined(__KCC)
//  Kai C++

#       if !defined(_EXCEPTIONS)
#           define BOOST_LEAF_NO_EXCEPTIONS
#       endif

#   elif defined(__CODEGEARC__)
//  CodeGear - must be checked for before Borland

#       if !defined(_CPPUNWIND) && !defined(__EXCEPTIONS)
#           define BOOST_LEAF_NO_EXCEPTIONS
#       endif

#   elif defined(__BORLANDC__)
//  Borland

#       if !defined(_CPPUNWIND) && !defined(__EXCEPTIONS)
#           define BOOST_LEAF_NO_EXCEPTIONS
#       endif

#   elif defined(__MWERKS__)
//  Metrowerks CodeWarrior

#       if !__option(exceptions)
#           define BOOST_LEAF_NO_EXCEPTIONS
#       endif

#   elif defined(__IBMCPP__) && defined(__COMPILER_VER__) && defined(__MVS__)
//  IBM z/OS XL C/C++

#       if !defined(_CPPUNWIND) && !defined(__EXCEPTIONS)
#           define BOOST_LEAF_NO_EXCEPTIONS
#       endif

#   elif defined(__ibmxl__)
//  IBM XL C/C++ for Linux (Little Endian)

#       if !__has_feature(cxx_exceptions)
#           define BOOST_LEAF_NO_EXCEPTIONS
#       endif

#   elif defined(_MSC_VER)
//  Microsoft Visual C++
//
//  Must remain the last #elif since some other vendors (Metrowerks, for
//  example) also #define _MSC_VER

#       if !defined(_CPPUNWIND)
#           define BOOST_LEAF_NO_EXCEPTIONS
#       endif
#   endif

#endif

#ifdef BOOST_NORETURN
#   define BOOST_LEAF_NORETURN BOOST_NORETURN
#else
#   if defined(_MSC_VER)
#       define BOOST_LEAF_NORETURN __declspec(noreturn)
#   elif defined(__GNUC__)
#       define BOOST_LEAF_NORETURN __attribute__ ((__noreturn__))
#   elif defined(__has_attribute) && defined(__SUNPRO_CC) && (__SUNPRO_CC > 0x5130)
#       if __has_attribute(noreturn)
#           define BOOST_LEAF_NORETURN [[noreturn]]
#       endif
#   elif defined(__has_cpp_attribute)
#       if __has_cpp_attribute(noreturn)
#           define BOOST_LEAF_NORETURN [[noreturn]]
#       endif
#   endif
#endif
#if !defined(BOOST_LEAF_NORETURN)
#  define BOOST_LEAF_NORETURN
#endif

////////////////////////////////////////

#ifndef BOOST_LEAF_DIAGNOSTICS
#   define BOOST_LEAF_DIAGNOSTICS 1
#endif

#if BOOST_LEAF_DIAGNOSTICS!=0 && BOOST_LEAF_DIAGNOSTICS!=1
#   error BOOST_LEAF_DIAGNOSTICS must be 0 or 1.
#endif

////////////////////////////////////////

#ifdef _MSC_VER
#   define BOOST_LEAF_ALWAYS_INLINE __forceinline
#else
#   define BOOST_LEAF_ALWAYS_INLINE __attribute__((always_inline)) inline
#endif

////////////////////////////////////////

#ifndef BOOST_LEAF_NODISCARD
#   if __cplusplus >= 201703L
#       define BOOST_LEAF_NODISCARD [[nodiscard]]
#   else
#       define BOOST_LEAF_NODISCARD
#   endif
#endif

////////////////////////////////////////

#ifndef BOOST_LEAF_CONSTEXPR
#   if __cplusplus > 201402L
#       define BOOST_LEAF_CONSTEXPR constexpr
#   else
#       define BOOST_LEAF_CONSTEXPR
#   endif
#endif

////////////////////////////////////////

#ifndef BOOST_LEAF_ASSERT
#   ifdef BOOST_ASSERT
#       define BOOST_LEAF_ASSERT BOOST_ASSERT
#   else
#       include <cassert>
#       define BOOST_LEAF_ASSERT assert
#   endif
#endif

////////////////////////////////////////

#ifndef BOOST_LEAF_NO_EXCEPTIONS
#   include <exception>
#   if (defined(__cpp_lib_uncaught_exceptions) && __cpp_lib_uncaught_exceptions >= 201411L) || (defined(_MSC_VER) && _MSC_VER >= 1900)
#       define BOOST_LEAF_STD_UNCAUGHT_EXCEPTIONS 1
#   else
#       define BOOST_LEAF_STD_UNCAUGHT_EXCEPTIONS 0
#   endif
#endif

#endif
// <<< #include <boost/leaf/detail/config.hpp>
#line 20 "boost/leaf/detail/optional.hpp"
#include <utility>
#include <new>

namespace boost { namespace leaf {

    namespace leaf_detail
    {
        template <class T>
        class optional
        {
            int key_;
            union { T value_; };

        public:

            typedef T value_type;

            BOOST_LEAF_CONSTEXPR optional() noexcept:
                key_(0)
            {
            }

            BOOST_LEAF_CONSTEXPR optional( optional const & x ):
                key_(x.key_)
            {
                if( x.key_ )
                    (void) new (&value_) T( x.value_ );
            }

            BOOST_LEAF_CONSTEXPR optional( optional && x ) noexcept:
                key_(x.key_)
            {
                if( x.key_ )
                {
                    (void) new (&value_) T( std::move(x.value_) );
                    x.reset();
                }
            }

            BOOST_LEAF_CONSTEXPR optional( int key, T const & v ):
                key_(key),
                value_(v)
            {
                BOOST_LEAF_ASSERT(!empty());
            }

            BOOST_LEAF_CONSTEXPR optional( int key, T && v ) noexcept:
                key_(key),
                value_(std::move(v))
            {
                BOOST_LEAF_ASSERT(!empty());
            }

            BOOST_LEAF_CONSTEXPR optional & operator=( optional const & x )
            {
                reset();
                if( int key = x.key() )
                {
                    put(key, x.value_);
                    key_ = key;
                }
                return *this;
            }

            BOOST_LEAF_CONSTEXPR optional & operator=( optional && x ) noexcept
            {
                reset();
                if( int key = x.key() )
                {
                    put(key, std::move(x.value_));
                    x.reset();
                }
                return *this;
            }

            ~optional() noexcept
            {
                reset();
            }

            BOOST_LEAF_CONSTEXPR bool empty() const noexcept
            {
                return key_==0;
            }

            BOOST_LEAF_CONSTEXPR int key() const noexcept
            {
                return key_;
            }

            BOOST_LEAF_CONSTEXPR void reset() noexcept
            {
                if( key_ )
                {
                    value_.~T();
                    key_=0;
                }
            }

            BOOST_LEAF_CONSTEXPR T & put( int key, T const & v )
            {
                BOOST_LEAF_ASSERT(key);
                reset();
                (void) new(&value_) T(v);
                key_=key;
                return value_;
            }

            BOOST_LEAF_CONSTEXPR T & put( int key, T && v ) noexcept
            {
                BOOST_LEAF_ASSERT(key);
                reset();
                (void) new(&value_) T(std::move(v));
                key_=key;
                return value_;
            }

            BOOST_LEAF_CONSTEXPR T const * has_value(int key) const noexcept
            {
                BOOST_LEAF_ASSERT(key);
                return key_==key ? &value_ : 0;
            }

            BOOST_LEAF_CONSTEXPR T * has_value(int key) noexcept
            {
                BOOST_LEAF_ASSERT(key);
                return key_==key ? &value_ : 0;
            }

            BOOST_LEAF_CONSTEXPR T const & value(int key) const & noexcept
            {
                BOOST_LEAF_ASSERT(has_value(key) != 0);
                return value_;
            }

            BOOST_LEAF_CONSTEXPR T & value(int key) & noexcept
            {
                BOOST_LEAF_ASSERT(has_value(key) != 0);
                return value_;
            }

            BOOST_LEAF_CONSTEXPR T const && value(int key) const && noexcept
            {
                BOOST_LEAF_ASSERT(has_value(key) != 0);
                return value_;
            }

            BOOST_LEAF_CONSTEXPR T value(int key) && noexcept
            {
                BOOST_LEAF_ASSERT(has_value(key) != 0);
                T tmp(std::move(value_));
                reset();
                return tmp;
            }
        };

    }

} }

#endif
// <<< #include <boost/leaf/detail/optional.hpp>
#line 20 "boost/leaf/detail/print.hpp"
#include <iosfwd>
#include <cstring>

namespace boost { namespace leaf {

    namespace leaf_detail
    {
        template <int N>
        BOOST_LEAF_CONSTEXPR inline char const * check_prefix( char const * t, char const (&prefix)[N] )
        {
            return std::strncmp(t,prefix,sizeof(prefix)-1)==0 ? t+sizeof(prefix)-1 : t;
        }
    }

    template <class Name>
    inline char const * type()
    {
        using leaf_detail::check_prefix;
    char const * t =
#ifdef __FUNCSIG__
        __FUNCSIG__;
#else
        __PRETTY_FUNCTION__;
#endif
#if defined(__clang__)
        BOOST_LEAF_ASSERT(check_prefix(t,"const char *boost::leaf::type() ")==t+32);
        return t+32;
#elif defined(__GNUC__)
        BOOST_LEAF_ASSERT(check_prefix(t,"const char* boost::leaf::type() ")==t+32);
        return t+32;
#else
        char const * clang_style = check_prefix(t,"const char *boost::leaf::type() ");
        if( clang_style!=t )
            return clang_style;
        char const * gcc_style = check_prefix(t,"const char* boost::leaf::type() ");
        if( gcc_style!=t )
            return gcc_style;
#endif
        return t;
    }

    namespace leaf_detail
    {
        template <class T, class E = void>
        struct is_printable: std::false_type
        {
        };

        template <class T>
        struct is_printable<T, decltype(std::declval<std::ostream&>()<<std::declval<T const &>(), void())>: std::true_type
        {
        };

        ////////////////////////////////////////

        template <class T, class E = void>
        struct has_printable_member_value: std::false_type
        {
        };

        template <class T>
        struct has_printable_member_value<T, decltype(std::declval<std::ostream&>()<<std::declval<T const &>().value, void())>: std::true_type
        {
        };

        ////////////////////////////////////////

        template <class Wrapper, bool WrapperPrintable=is_printable<Wrapper>::value, bool ValuePrintable=has_printable_member_value<Wrapper>::value>
        struct diagnostic;

        template <class Wrapper, bool ValuePrintable>
        struct diagnostic<Wrapper, true, ValuePrintable>
        {
            static constexpr bool is_invisible = false;
            static void print( std::ostream & os, Wrapper const & x )
            {
                os << x;
            }
        };

        template <class Wrapper>
        struct diagnostic<Wrapper, false, true>
        {
            static constexpr bool is_invisible = false;
            static void print( std::ostream & os, Wrapper const & x )
            {
                os << type<Wrapper>() << ": " << x.value;
            }
        };

        template <class Wrapper>
        struct diagnostic<Wrapper, false, false>
        {
            static constexpr bool is_invisible = false;
            static void print( std::ostream & os, Wrapper const & )
            {
                os << type<Wrapper>() << ": {Non-Printable}";
            }
        };

#ifndef BOOST_LEAF_NO_EXCEPTIONS
        template <>
        struct diagnostic<std::exception_ptr, false, false>
        {
            static constexpr bool is_invisible = true;
            BOOST_LEAF_CONSTEXPR static void print( std::ostream &, std::exception_ptr const & )
            {
            }
        };
#endif
    }

} }

#endif
// <<< #include <boost/leaf/detail/print.hpp>
#line 21 "boost/leaf/error.hpp"
#include <system_error>
#include <type_traits>
#include <memory>
#include <string>

#if BOOST_LEAF_DIAGNOSTICS
#   include <sstream>
#   include <set>
#endif

#define BOOST_LEAF_TOKEN_PASTE(x, y) x ## y
#define BOOST_LEAF_TOKEN_PASTE2(x, y) BOOST_LEAF_TOKEN_PASTE(x, y)
#define BOOST_LEAF_TMP BOOST_LEAF_TOKEN_PASTE2(boost_leaf_tmp_, __LINE__)

#define BOOST_LEAF_ASSIGN(v,r)\
    static_assert(::boost::leaf::is_result_type<typename std::decay<decltype(r)>::type>::value, "The BOOST_LEAF_ASSIGN macro requires a result type as the second argument");\
    auto && BOOST_LEAF_TMP = r;\
    if( !BOOST_LEAF_TMP )\
        return BOOST_LEAF_TMP.error();\
    v = std::forward<decltype(BOOST_LEAF_TMP)>(BOOST_LEAF_TMP).value()

#define BOOST_LEAF_AUTO(v, r)\
    BOOST_LEAF_ASSIGN(auto v, r)

#define BOOST_LEAF_CHECK(r)\
    {\
        static_assert(::boost::leaf::is_result_type<typename std::decay<decltype(r)>::type>::value, "BOOST_LEAF_CHECK requires a result type");\
        auto && BOOST_LEAF_TMP = r;\
        if( !BOOST_LEAF_TMP )\
            return BOOST_LEAF_TMP.error();\
    }

#define BOOST_LEAF_NEW_ERROR ::leaf::leaf_detail::inject_loc{__FILE__,__LINE__,__FUNCTION__}+::boost::leaf::new_error

namespace boost { namespace leaf {

    namespace leaf_detail
    {
        struct inject_loc
        {
            char const * const file;
            int const line;
            char const * const fn;

            template <class T>
            friend T operator+( inject_loc loc, T && x ) noexcept
            {
                x.load_source_location_(loc.file, loc.line, loc.fn);
                return std::move(x);
            }
        };
    }

} }

////////////////////////////////////////

#ifdef BOOST_LEAF_NO_EXCEPTIONS

namespace boost
{
    BOOST_LEAF_NORETURN void throw_exception( std::exception const & ); // user defined
}

namespace boost { namespace leaf {

    template <class T>
    BOOST_LEAF_NORETURN void throw_exception( T const & e )
    {
        ::boost::throw_exception(e);
    }

} }

#else

namespace boost { namespace leaf {

    template <class T>
    BOOST_LEAF_NORETURN void throw_exception( T const & e )
    {
        throw e;
    }

} }

#endif

////////////////////////////////////////

#ifdef BOOST_LEAF_NO_THREADS

#   define BOOST_LEAF_THREAD_LOCAL
    namespace boost { namespace leaf {
        namespace leaf_detail
        {
            using atomic_unsigned_int = unsigned int;
        }
    } }

#else

#   include <atomic>
#   include <thread>
#   define BOOST_LEAF_THREAD_LOCAL thread_local
    namespace boost { namespace leaf {
        namespace leaf_detail
        {
            using atomic_unsigned_int = std::atomic<unsigned int>;
        }
    } }

#endif

////////////////////////////////////////

namespace boost { namespace leaf {

#if BOOST_LEAF_DIAGNOSTICS

    namespace leaf_detail
    {
        class e_unexpected_count
        {
        public:

            char const * (*first_type)();
            int count;

            BOOST_LEAF_CONSTEXPR explicit e_unexpected_count(char const * (*first_type)()) noexcept:
                first_type(first_type),
                count(1)
            {
            }

            template <class CharT, class Traits>
            void print( std::basic_ostream<CharT, Traits> & os ) const
            {
                BOOST_LEAF_ASSERT(first_type != 0);
                BOOST_LEAF_ASSERT(count>0);
                os << "Detected ";
                if( count==1 )
                    os << "1 attempt to communicate an unexpected error object";
                else
                    os << count << " attempts to communicate unexpected error objects, the first one";
                (os << " of type " << first_type() << '\n').flush();
            }
        };

        template <>
        struct diagnostic<e_unexpected_count, false, false>
        {
            static constexpr bool is_invisible = true;
            BOOST_LEAF_CONSTEXPR static void print(std::ostream &, e_unexpected_count const &) noexcept { }
        };

        class e_unexpected_info
        {
            std::string s_;
            std::set<char const *(*)()> already_;

        public:

            e_unexpected_info() noexcept
            {
            }

            template <class E>
            void add(E && e)
            {
                if( !diagnostic<E>::is_invisible && already_.insert(&type<E>).second  )
                {
                    std::stringstream s;
                    diagnostic<E>::print(s,e);
                    (s << '\n').flush();
                    s_ += s.str();
                }
            }

            template <class CharT, class Traits>
            void print( std::basic_ostream<CharT, Traits> & os ) const
            {
                os << "Unhandled error objects:\n" << s_;
            }
        };

        template <>
        struct diagnostic<e_unexpected_info, false, false>
        {
            static constexpr bool is_invisible = true;
            BOOST_LEAF_CONSTEXPR static void print(std::ostream &, e_unexpected_info const &) noexcept { }
        };

        template <class=void>
        struct tl_unexpected_enabled
        {
            static BOOST_LEAF_THREAD_LOCAL int counter;
        };

        template <class T>
        BOOST_LEAF_THREAD_LOCAL int tl_unexpected_enabled<T>::counter;
    }

#endif

} }

////////////////////////////////////////

namespace boost { namespace leaf {

    struct e_source_location
    {
        char const * const file;
        int const line;
        char const * const function;

        template <class CharT, class Traits>
        friend std::basic_ostream<CharT, Traits> & operator<<( std::basic_ostream<CharT, Traits> & os, e_source_location const & x )
        {
            return os << leaf::type<e_source_location>() << ": " << x.file << '(' << x.line << ") in function " << x.function;
        }
    };

    ////////////////////////////////////////

    namespace leaf_detail
    {
        template <class E>
        class slot;

        template <class E>
        struct tl_slot_ptr
        {
            static BOOST_LEAF_THREAD_LOCAL slot<E> * p;
        };

        template <class E>
        BOOST_LEAF_THREAD_LOCAL slot<E> * tl_slot_ptr<E>::p;

        template <class E>
        class slot:
            optional<E>
        {
            slot( slot const & ) = delete;
            slot & operator=( slot const & ) = delete;

            using impl = optional<E>;
            slot<E> * * top_;
            slot<E> * prev_;

        public:

            BOOST_LEAF_CONSTEXPR slot() noexcept:
                top_(0)
            {
            }

            BOOST_LEAF_CONSTEXPR slot( slot && x ) noexcept:
                optional<E>(std::move(x)),
                top_(0)
            {
                BOOST_LEAF_ASSERT(x.top_==0);
            }

            BOOST_LEAF_CONSTEXPR void activate() noexcept
            {
                BOOST_LEAF_ASSERT(top_==0 || *top_!=this);
                top_ = &tl_slot_ptr<E>::p;
                prev_ = *top_;
                *top_ = this;
            }

            BOOST_LEAF_CONSTEXPR void deactivate() noexcept
            {
                BOOST_LEAF_ASSERT(top_!=0 && *top_==this);
                *top_ = prev_;
            }

            BOOST_LEAF_CONSTEXPR void propagate() noexcept;

            template <class CharT, class Traits>
            void print( std::basic_ostream<CharT, Traits> & os, int key_to_print ) const
            {
                if( !diagnostic<E>::is_invisible )
                    if( int k = this->key() )
                    {
                        if( key_to_print )
                        {
                            if( key_to_print!=k )
                                return;
                        }
                        else
                            os << '[' << k << ']';
                        diagnostic<E>::print(os, value(k));
                        (os << '\n').flush();
                    }
            }

            using impl::put;
            using impl::has_value;
            using impl::value;
        };

#if BOOST_LEAF_DIAGNOSTICS

        template <class E>
        BOOST_LEAF_CONSTEXPR inline void load_unexpected_count( int err_id ) noexcept
        {
            if( slot<e_unexpected_count> * sl = tl_slot_ptr<e_unexpected_count>::p )
                if( e_unexpected_count * unx = sl->has_value(err_id) )
                    ++unx->count;
                else
                    sl->put(err_id, e_unexpected_count(&type<E>));
        }

        template <class E>
        BOOST_LEAF_CONSTEXPR inline void load_unexpected_info( int err_id, E && e ) noexcept
        {
            if( slot<e_unexpected_info> * sl = tl_slot_ptr<e_unexpected_info>::p )
                if( e_unexpected_info * unx = sl->has_value(err_id) )
                    unx->add(std::forward<E>(e));
                else
                    sl->put(err_id, e_unexpected_info()).add(std::forward<E>(e));
        }

        template <class E>
        BOOST_LEAF_CONSTEXPR inline void load_unexpected( int err_id, E && e  ) noexcept
        {
            load_unexpected_count<E>(err_id);
            load_unexpected_info(err_id, std::forward<E>(e));
        }

#endif

        template <class E>
        BOOST_LEAF_CONSTEXPR inline void slot<E>::propagate() noexcept
        {
            BOOST_LEAF_ASSERT(top_!=0 && (*top_==prev_ || *top_==this));
            if( prev_ )
            {
                impl & that_ = *prev_;
                if( that_.empty() )
                {
                    impl & this_ = *this;
                    that_ = std::move(this_);
                }
            }
#if BOOST_LEAF_DIAGNOSTICS
            else
            {
                int c = tl_unexpected_enabled<>::counter;
                BOOST_LEAF_ASSERT(c>=0);
                if( c )
                    if( int err_id = impl::key() )
                        load_unexpected(err_id, std::move(*this).value(err_id));
            }
#endif
        }

        template <class E>
        BOOST_LEAF_CONSTEXPR inline int load_slot( int err_id, E && e ) noexcept
        {
            static_assert(!std::is_pointer<E>::value, "Error objects of pointer types are not allowed");
            using T = typename std::decay<E>::type;
            BOOST_LEAF_ASSERT((err_id&3)==1);
            if( slot<T> * p = tl_slot_ptr<T>::p )
                (void) p->put(err_id, std::forward<E>(e));
#if BOOST_LEAF_DIAGNOSTICS
            else
            {
                int c = tl_unexpected_enabled<>::counter;
                BOOST_LEAF_ASSERT(c>=0);
                if( c )
                    load_unexpected(err_id, std::forward<E>(e));
            }
#endif
            return 0;
        }

        template <class F>
        BOOST_LEAF_CONSTEXPR inline int accumulate_slot( int err_id, F && f ) noexcept
        {
            static_assert(function_traits<F>::arity==1, "Lambdas passed to accumulate must take a single e-type argument by reference");
            using E = typename std::decay<fn_arg_type<F,0>>::type;
            static_assert(!std::is_pointer<E>::value, "Error objects of pointer types are not allowed");
            BOOST_LEAF_ASSERT((err_id&3)==1);
            if( auto sl = tl_slot_ptr<E>::p )
                if( auto v = sl->has_value(err_id) )
                    (void) std::forward<F>(f)(*v);
                else
                    (void) std::forward<F>(f)(sl->put(err_id,E()));
            return 0;
        }
    }

    ////////////////////////////////////////

    namespace leaf_detail
    {
        template <class=void>
        struct id_factory
        {
            static atomic_unsigned_int counter;
            static BOOST_LEAF_THREAD_LOCAL unsigned current_id;

            BOOST_LEAF_CONSTEXPR static unsigned generate_next_id() noexcept
            {
                auto id = (counter+=4);
                BOOST_LEAF_ASSERT((id&3)==1);
                return id;
            }
        };

        template <class T>
        atomic_unsigned_int id_factory<T>::counter(-3);

        template <class T>
        BOOST_LEAF_THREAD_LOCAL unsigned id_factory<T>::current_id(0);

        inline int current_id() noexcept
        {
            auto id = id_factory<>::current_id;
            BOOST_LEAF_ASSERT(id==0 || (id&3)==1);
            return id;
        }

        inline int new_id() noexcept
        {
            auto id = id_factory<>::generate_next_id();
            return id_factory<>::current_id = id;
        }
    }

    ////////////////////////////////////////

    namespace leaf_detail
    {
        template <class T, int Arity = function_traits<T>::arity>
        struct load_item
        {
            static_assert(Arity==0 || Arity==1, "If a functions is passed to new_error or load, it must take zero or one argument");
        };

        template <class E>
        struct load_item<E, -1>
        {
            BOOST_LEAF_CONSTEXPR static int load( int err_id, E && e ) noexcept
            {
                return load_slot(err_id, std::forward<E>(e));
            }
        };

        template <class F>
        struct load_item<F, 0>
        {
            BOOST_LEAF_CONSTEXPR static int load( int err_id, F && f ) noexcept
            {
                return load_slot(err_id, std::forward<F>(f)());
            }
        };

        template <class F>
        struct load_item<F, 1>
        {
            BOOST_LEAF_CONSTEXPR static int load( int err_id, F && f ) noexcept
            {
                return accumulate_slot(err_id, std::forward<F>(f));
            }
        };
    }

    ////////////////////////////////////////

    namespace leaf_detail
    {
        class leaf_category final: public std::error_category
        {
            bool equivalent( int,  std::error_condition const & ) const noexcept final override { return false; }
            bool equivalent( std::error_code const &, int ) const noexcept final override { return false; }
            char const * name() const noexcept final override { return "LEAF error"; }
            std::string message( int condition ) const final override { return name(); }
        public:
            ~leaf_category() noexcept final override { }
        };

        template <class=void>
        struct get_error_category
        {
            static leaf_category cat;
        };

        template <class T>
        leaf_category get_error_category<T>::cat;

        inline int import_error_code( std::error_code const & ec ) noexcept
        {
            if( int err_id = ec.value() )
            {
                std::error_category const & cat = get_error_category<>::cat;
                if( &ec.category()==&cat )
                {
                    BOOST_LEAF_ASSERT((err_id&3)==1);
                    return (err_id&~3)|1;
                }
                else
                {
                    err_id = new_id();
                    (void) load_slot(err_id, ec);
                    return (err_id&~3)|1;
                }
            }
            else
                return 0;
        }
    }

    inline bool is_error_id( std::error_code const & ec ) noexcept
    {
        bool res = (&ec.category() == &leaf_detail::get_error_category<>::cat);
        BOOST_LEAF_ASSERT(!res || !ec.value() || ((ec.value()&3)==1));
        return res;
    }

    ////////////////////////////////////////

    class error_id;

    namespace leaf_detail
    {
        BOOST_LEAF_CONSTEXPR error_id make_error_id(int) noexcept;
    }

    class error_id
    {
        friend error_id BOOST_LEAF_CONSTEXPR leaf_detail::make_error_id(int) noexcept;

        int value_;

        BOOST_LEAF_CONSTEXPR explicit error_id( int value ) noexcept:
            value_(value)
        {
            BOOST_LEAF_ASSERT(value_==0 || ((value_&3)==1));
        }

    public:

        BOOST_LEAF_CONSTEXPR error_id() noexcept:
            value_(0)
        {
        }

        error_id( std::error_code const & ec ) noexcept:
            value_(leaf_detail::import_error_code(ec))
        {
            BOOST_LEAF_ASSERT(!value_ || ((value_&3)==1));
        }

        template <class Enum>
        error_id( Enum e, typename std::enable_if<std::is_error_code_enum<Enum>::value, Enum>::type * = 0 ) noexcept:
            value_(leaf_detail::import_error_code(e))
        {
        }

        BOOST_LEAF_CONSTEXPR error_id load() const noexcept
        {
            return *this;
        }

        template <class... Item>
        BOOST_LEAF_CONSTEXPR error_id load( Item && ... item ) const noexcept
        {
            if( int err_id = value() )
            {
                int const unused[ ] = { 42, leaf_detail::load_item<Item>::load(err_id, std::forward<Item>(item))... };
                (void) unused;
            }
            return *this;
        }

        std::error_code to_error_code() const noexcept
        {
            return std::error_code(value_, leaf_detail::get_error_category<>::cat);
        }

        BOOST_LEAF_CONSTEXPR int value() const noexcept
        {
            if( int v = value_ )
            {
                BOOST_LEAF_ASSERT((v&3)==1);
                return (v&~3)|1;
            }
            else
                return 0;
        }

        BOOST_LEAF_CONSTEXPR explicit operator bool() const noexcept
        {
            return value_ != 0;
        }

        BOOST_LEAF_CONSTEXPR friend bool operator==( error_id a, error_id b ) noexcept
        {
            return a.value_ == b.value_;
        }

        BOOST_LEAF_CONSTEXPR friend bool operator!=( error_id a, error_id b ) noexcept
        {
            return !(a == b);
        }

        BOOST_LEAF_CONSTEXPR friend bool operator<( error_id a, error_id b ) noexcept
        {
            return a.value_ < b.value_;
        }

        template <class CharT, class Traits>
        friend std::basic_ostream<CharT, Traits> & operator<<( std::basic_ostream<CharT, Traits> & os, error_id x )
        {
            return os << x.value_;
        }

        BOOST_LEAF_CONSTEXPR void load_source_location_( char const * file, int line, char const * function ) const noexcept
        {
            BOOST_LEAF_ASSERT(file&&*file);
            BOOST_LEAF_ASSERT(line>0);
            BOOST_LEAF_ASSERT(function&&*function);
            BOOST_LEAF_ASSERT(value_);
            (void) load(e_source_location {file,line,function});
        }
    };

    namespace leaf_detail
    {
        BOOST_LEAF_CONSTEXPR inline error_id make_error_id( int err_id ) noexcept
        {
            BOOST_LEAF_ASSERT(err_id==0 || (err_id&3)==1);
            return error_id((err_id&~3)|1);
        }
    }

    inline error_id new_error() noexcept
    {
        return leaf_detail::make_error_id(leaf_detail::new_id());
    }

    template <class... Item>
    inline error_id new_error( Item && ... item ) noexcept
    {
        return leaf_detail::make_error_id(leaf_detail::new_id()).load(std::forward<Item>(item)...);
    }

    inline error_id current_error() noexcept
    {
        return leaf_detail::make_error_id(leaf_detail::current_id());
    }

    ////////////////////////////////////////////

    class polymorphic_context
    {
    protected:

        polymorphic_context() noexcept = default;
        ~polymorphic_context() noexcept = default;

    public:

        virtual error_id propagate_captured_errors() noexcept = 0;
        virtual void activate() noexcept = 0;
        virtual void deactivate() noexcept = 0;
        virtual void propagate() noexcept = 0;
        virtual bool is_active() const noexcept = 0;
        virtual void print( std::ostream & ) const = 0;
        error_id captured_id_;
    };

    using context_ptr = std::shared_ptr<polymorphic_context>;

    ////////////////////////////////////////////

    template <class Ctx>
    class context_activator
    {
        context_activator( context_activator const & ) = delete;
        context_activator & operator=( context_activator const & ) = delete;

#if !defined(BOOST_LEAF_NO_EXCEPTIONS) && BOOST_LEAF_STD_UNCAUGHT_EXCEPTIONS
        int const uncaught_exceptions_;
#endif
        Ctx * ctx_;

    public:

        explicit BOOST_LEAF_CONSTEXPR BOOST_LEAF_ALWAYS_INLINE context_activator(Ctx & ctx) noexcept:
#if !defined(BOOST_LEAF_NO_EXCEPTIONS) && BOOST_LEAF_STD_UNCAUGHT_EXCEPTIONS
            uncaught_exceptions_(std::uncaught_exceptions()),
#endif
            ctx_(ctx.is_active() ? 0 : &ctx)
        {
            if( ctx_ )
                ctx_->activate();
        }

        BOOST_LEAF_CONSTEXPR BOOST_LEAF_ALWAYS_INLINE context_activator( context_activator && x ) noexcept:
#if !defined(BOOST_LEAF_NO_EXCEPTIONS) && BOOST_LEAF_STD_UNCAUGHT_EXCEPTIONS
            uncaught_exceptions_(x.uncaught_exceptions_),
#endif
            ctx_(x.ctx_)
        {
            x.ctx_ = 0;
        }

        BOOST_LEAF_ALWAYS_INLINE ~context_activator() noexcept
        {
            if( !ctx_ )
                return;
            if( ctx_->is_active() )
                ctx_->deactivate();
#ifndef BOOST_LEAF_NO_EXCEPTIONS
#   if BOOST_LEAF_STD_UNCAUGHT_EXCEPTIONS
            if( std::uncaught_exceptions() > uncaught_exceptions_ )
#   else
            if( std::uncaught_exception() )
#   endif
                ctx_->propagate();
#endif
        }
    };

    template <class Ctx>
    BOOST_LEAF_CONSTEXPR BOOST_LEAF_ALWAYS_INLINE context_activator<Ctx> activate_context(Ctx & ctx) noexcept
    {
        return context_activator<Ctx>(ctx);
    }

    ////////////////////////////////////////////

    template <class R>
    struct is_result_type: std::false_type
    {
    };

    template <class R>
    struct is_result_type<R const>: is_result_type<R>
    {
    };

} }

#undef BOOST_LEAF_THREAD_LOCAL

#endif
// <<< #include <boost/leaf/error.hpp>
#line 20 "boost/leaf/exception.hpp"
#include <exception>

#define BOOST_LEAF_EXCEPTION ::boost::leaf::leaf_detail::inject_loc{__FILE__,__LINE__,__FUNCTION__}+::boost::leaf::exception
#define BOOST_LEAF_THROW_EXCEPTION ::boost::leaf::leaf_detail::throw_with_loc{__FILE__,__LINE__,__FUNCTION__}+::boost::leaf::exception

////////////////////////////////////////

namespace boost { namespace leaf {

    namespace leaf_detail
    {
        struct throw_with_loc
        {
            char const * const file;
            int const line;
            char const * const fn;

            template <class Ex>
            [[noreturn]] friend void operator+( throw_with_loc loc, Ex const & ex )
            {
                ex.load_source_location_(loc.file, loc.line, loc.fn);
                ::boost::leaf::throw_exception(ex);
            }
        };
    }

} }

////////////////////////////////////////

namespace boost { namespace leaf {

    namespace leaf_detail
    {
        inline void enforce_std_exception( std::exception const & ) noexcept { }

        class exception_base
        {
            std::shared_ptr<void const> auto_id_bump_;
        public:

            virtual error_id get_error_id() const noexcept = 0;

        protected:

            exception_base():
                auto_id_bump_(0, [](void const *) { (void) new_id(); })
            {
            }

            ~exception_base() noexcept { }
        };

        template <class Ex>
        class exception:
            public Ex,
            public exception_base,
            public error_id
        {
            error_id get_error_id() const noexcept final override
            {
                return *this;
            }

        public:

            exception( exception const & ) = default;
            exception( exception && ) = default;

            BOOST_LEAF_CONSTEXPR exception( error_id id, Ex && ex ) noexcept:
                Ex(std::move(ex)),
                error_id(id)
            {
                enforce_std_exception(*this);
            }

            explicit BOOST_LEAF_CONSTEXPR exception( error_id id ) noexcept:
                error_id(id)
            {
                enforce_std_exception(*this);
            }
        };

        template <class... T>
        struct at_least_one_derives_from_std_exception;

        template <>
        struct at_least_one_derives_from_std_exception<>: std::false_type { };

        template <class T, class... Rest>
        struct at_least_one_derives_from_std_exception<T, Rest...>
        {
            constexpr static const bool value = std::is_base_of<std::exception,T>::value || at_least_one_derives_from_std_exception<Rest...>::value;
        };
    }

    template <class Ex, class... E>
    inline
    typename std::enable_if<std::is_base_of<std::exception,Ex>::value, leaf_detail::exception<Ex>>::type
    exception( Ex && ex, E && ... e ) noexcept
    {
        static_assert(!leaf_detail::at_least_one_derives_from_std_exception<E...>::value, "Error objects passed to leaf::exception may not derive from std::exception");
        auto id = leaf::new_error(std::forward<E>(e)...);
        return leaf_detail::exception<Ex>(id, std::forward<Ex>(ex));
    }

    template <class E1, class... E>
    inline
    typename std::enable_if<!std::is_base_of<std::exception,E1>::value, leaf_detail::exception<std::exception>>::type
    exception( E1 && car, E && ... cdr ) noexcept
    {
        static_assert(!leaf_detail::at_least_one_derives_from_std_exception<E...>::value, "Error objects passed to leaf::exception may not derive from std::exception");
        auto id = leaf::new_error(std::forward<E1>(car), std::forward<E>(cdr)...);
        return leaf_detail::exception<std::exception>(id);
    }

    inline leaf_detail::exception<std::exception> exception() noexcept
    {
        return leaf_detail::exception<std::exception>(leaf::new_error());
    }

} }

#endif
// <<< #include <boost/leaf/exception.hpp>
#line 20 "boost/leaf/capture.hpp"
// >>> #include <boost/leaf/on_error.hpp>
#line 1 "boost/leaf/on_error.hpp"
#ifndef BOOST_LEAF_ON_ERROR_HPP_INCLUDED
#define BOOST_LEAF_ON_ERROR_HPP_INCLUDED

// Copyright (c) 2018-2020 Emil Dotchevski and Reverge Studios, Inc.

// Distributed under the Boost Software License, Version 1.0. (See accompanying
// file LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)

#ifndef BOOST_LEAF_ENABLE_WARNINGS
#   if defined(__clang__)
#       pragma clang system_header
#   elif (__GNUC__*100+__GNUC_MINOR__>301)
#       pragma GCC system_header
#   elif defined(_MSC_VER)
#       pragma warning(push,1)
#   endif
#endif


namespace boost { namespace leaf {

    class error_monitor
    {
#if !defined(BOOST_LEAF_NO_EXCEPTIONS) && BOOST_LEAF_STD_UNCAUGHT_EXCEPTIONS
        int const uncaught_exceptions_;
#endif
        int const err_id_;

    public:

        error_monitor() noexcept:
#if !defined(BOOST_LEAF_NO_EXCEPTIONS) && BOOST_LEAF_STD_UNCAUGHT_EXCEPTIONS
            uncaught_exceptions_(std::uncaught_exceptions()),
#endif
            err_id_(leaf_detail::current_id())
        {
        }

        int check_id() const noexcept
        {
            int err_id = leaf_detail::current_id();
            if( err_id != err_id_ )
                return err_id;
            else
            {
#ifndef BOOST_LEAF_NO_EXCEPTIONS
#   if BOOST_LEAF_STD_UNCAUGHT_EXCEPTIONS
                if( std::uncaught_exceptions() > uncaught_exceptions_ )
#   else
                if( std::uncaught_exception() )
#   endif
                    return leaf_detail::new_id();
#endif
                return 0;
            }
        }

        int get_id() const noexcept
        {
            int err_id = leaf_detail::current_id();
            if( err_id != err_id_ )
                return err_id;
            else
                return leaf_detail::new_id();
        }

        error_id check() const noexcept
        {
            return leaf_detail::make_error_id(check_id());
        }

        error_id assigned_error_id() const noexcept
        {
            return leaf_detail::make_error_id(get_id());
        }
    };

    ////////////////////////////////////////////

    namespace leaf_detail
    {
        template <int I, class Tuple>
        struct tuple_for_each_preload
        {
            BOOST_LEAF_CONSTEXPR static void trigger( Tuple & tup, int err_id ) noexcept
            {
                BOOST_LEAF_ASSERT((err_id&3)==1);
                tuple_for_each_preload<I-1,Tuple>::trigger(tup,err_id);
                std::get<I-1>(tup).trigger(err_id);
            }
        };

        template <class Tuple>
        struct tuple_for_each_preload<0, Tuple>
        {
            BOOST_LEAF_CONSTEXPR static void trigger( Tuple const &, int ) noexcept { }
        };

        template <class E>
        class preloaded_item
        {
            using decay_E = typename std::decay<E>::type;
            slot<decay_E> * s_;
            decay_E e_;

        public:

            BOOST_LEAF_CONSTEXPR preloaded_item( E && e ):
                s_(tl_slot_ptr<decay_E>::p),
                e_(std::forward<E>(e))
            {
            }

            BOOST_LEAF_CONSTEXPR void trigger( int err_id ) noexcept
            {
                BOOST_LEAF_ASSERT((err_id&3)==1);
                if( s_ )
                {
                    if( !s_->has_value(err_id) )
                        s_->put(err_id, std::move(e_));
                }
#if BOOST_LEAF_DIAGNOSTICS
                else
                {
                    int c = tl_unexpected_enabled<>::counter;
                    BOOST_LEAF_ASSERT(c>=0);
                    if( c )
                        load_unexpected(err_id, std::move(e_));
                }
#endif
            }
        };

        template <class F>
        class deferred_item
        {
            using E = decltype(std::declval<F>()());
            slot<E> * s_;
            F f_;

        public:

            BOOST_LEAF_CONSTEXPR deferred_item( F && f ) noexcept:
                s_(tl_slot_ptr<E>::p),
                f_(std::forward<F>(f))
            {
            }

            BOOST_LEAF_CONSTEXPR void trigger( int err_id ) noexcept
            {
                BOOST_LEAF_ASSERT((err_id&3)==1);
                if( s_ )
                {
                    if( !s_->has_value(err_id) )
                        s_->put(err_id, f_());
                }
#if BOOST_LEAF_DIAGNOSTICS
                else
                {
                    int c = tl_unexpected_enabled<>::counter;
                    BOOST_LEAF_ASSERT(c>=0);
                    if( c )
                        load_unexpected(err_id, std::forward<E>(f_()));
                }
#endif
            }
        };

        template <class F, class A0 = fn_arg_type<F,0>, int arity = function_traits<F>::arity>
        class accumulating_item;

        template <class F, class A0>
        class accumulating_item<F, A0 &, 1>
        {
            using E = A0;
            slot<E> * s_;
            F f_;

        public:

            BOOST_LEAF_CONSTEXPR accumulating_item( F && f ) noexcept:
                s_(tl_slot_ptr<E>::p),
                f_(std::forward<F>(f))
            {
            }

            BOOST_LEAF_CONSTEXPR void trigger( int err_id ) noexcept
            {
                BOOST_LEAF_ASSERT((err_id&3)==1);
                if( s_ )
                    if( E * e = s_->has_value(err_id) )
                        (void) f_(*e);
                    else
                        (void) f_(s_->put(err_id, E()));
            }
        };

        template <class... Item>
        class preloaded
        {
            preloaded & operator=( preloaded const & ) = delete;

            std::tuple<Item...> p_;
            bool moved_;
            error_monitor id_;

        public:

            BOOST_LEAF_CONSTEXPR explicit preloaded( Item && ... i ):
                p_(std::forward<Item>(i)...),
                moved_(false)
            {
            }

            BOOST_LEAF_CONSTEXPR preloaded( preloaded && x ) noexcept:
                p_(std::move(x.p_)),
                moved_(false),
                id_(std::move(x.id_))
            {
                x.moved_ = true;
            }

            ~preloaded() noexcept
            {
                if( moved_ )
                    return;
                if( auto id = id_.check_id() )
                    tuple_for_each_preload<sizeof...(Item),decltype(p_)>::trigger(p_,id);
            }
        };

        template <class T, int arity = function_traits<T>::arity>
        struct deduce_item_type;

        template <class T>
        struct deduce_item_type<T, -1>
        {
            using type = preloaded_item<T>;
        };

        template <class F>
        struct deduce_item_type<F, 0>
        {
            using type = deferred_item<F>;
        };

        template <class F>
        struct deduce_item_type<F, 1>
        {
            using type = accumulating_item<F>;
        };
    }

    template <class... Item>
    BOOST_LEAF_NODISCARD BOOST_LEAF_CONSTEXPR inline
    leaf_detail::preloaded<typename leaf_detail::deduce_item_type<Item>::type...>
    on_error( Item && ... i )
    {
        return leaf_detail::preloaded<typename leaf_detail::deduce_item_type<Item>::type...>(std::forward<Item>(i)...);
    }

} }

#endif
// <<< #include <boost/leaf/on_error.hpp>
#line 21 "boost/leaf/capture.hpp"

namespace boost { namespace leaf {

    namespace leaf_detail
    {
        template <class R, bool IsResult = is_result_type<R>::value>
        struct is_result_tag;

        template <class R>
        struct is_result_tag<R, false>
        {
        };

        template <class R>
        struct is_result_tag<R, true>
        {
        };
    }

#ifdef BOOST_LEAF_NO_EXCEPTIONS

    namespace leaf_detail
    {
        template <class R, class F, class... A>
        inline
        decltype(std::declval<F>()(std::forward<A>(std::declval<A>())...))
        capture_impl(is_result_tag<R, false>, context_ptr && ctx, F && f, A... a) noexcept
        {
            auto active_context = activate_context(*ctx);
            return std::forward<F>(f)(std::forward<A>(a)...);
        }

        template <class R, class F, class... A>
        inline
        decltype(std::declval<F>()(std::forward<A>(std::declval<A>())...))
        capture_impl(is_result_tag<R, true>, context_ptr && ctx, F && f, A... a) noexcept
        {
            auto active_context = activate_context(*ctx);
            if( auto r = std::forward<F>(f)(std::forward<A>(a)...) )
                return r;
            else
            {
                ctx->captured_id_ = r.error();
                return std::move(ctx);
            }
        }

        template <class R, class Future>
        inline
        decltype(std::declval<Future>().get())
        future_get_impl(is_result_tag<R, false>, Future & fut) noexcept
        {
            return fut.get();
        }

        template <class R, class Future>
        inline
        decltype(std::declval<Future>().get())
        future_get_impl(is_result_tag<R, true>, Future & fut) noexcept
        {
            if( auto r = fut.get() )
                return r;
            else
                return error_id(r.error()); // unloads
        }
    }

#else

    namespace leaf_detail
    {
        class capturing_exception:
            public std::exception
        {
            std::exception_ptr ex_;
            context_ptr ctx_;

        public:

            capturing_exception(std::exception_ptr && ex, context_ptr && ctx) noexcept:
                ex_(std::move(ex)),
                ctx_(std::move(ctx))
            {
                BOOST_LEAF_ASSERT(ex_);
                BOOST_LEAF_ASSERT(ctx_);
                BOOST_LEAF_ASSERT(ctx_->captured_id_);
            }

            [[noreturn]] void unload_and_rethrow_original_exception() const
            {
                BOOST_LEAF_ASSERT(ctx_->captured_id_);
                auto active_context = activate_context(*ctx_);
                id_factory<>::current_id = ctx_->captured_id_.value();
                std::rethrow_exception(ex_);
            }

            template <class CharT, class Traits>
            void print( std::basic_ostream<CharT, Traits> & os ) const
            {
                ctx_->print(os);
            }
        };

        template <class R, class F, class... A>
        inline
        decltype(std::declval<F>()(std::forward<A>(std::declval<A>())...))
        capture_impl(is_result_tag<R, false>, context_ptr && ctx, F && f, A... a)
        {
            auto active_context = activate_context(*ctx);
            error_monitor cur_err;
            try
            {
                return std::forward<F>(f)(std::forward<A>(a)...);
            }
            catch( capturing_exception const & )
            {
                throw;
            }
            catch( exception_base const & e )
            {
                ctx->captured_id_ = e.get_error_id();
                throw_exception( capturing_exception(std::current_exception(), std::move(ctx)) );
            }
            catch(...)
            {
                ctx->captured_id_ = cur_err.assigned_error_id();
                throw_exception( capturing_exception(std::current_exception(), std::move(ctx)) );
            }
        }

        template <class R, class F, class... A>
        inline
        decltype(std::declval<F>()(std::forward<A>(std::declval<A>())...))
        capture_impl(is_result_tag<R, true>, context_ptr && ctx, F && f, A... a)
        {
            auto active_context = activate_context(*ctx);
            error_monitor cur_err;
            try
            {
                if( auto && r = std::forward<F>(f)(std::forward<A>(a)...) )
                    return std::move(r);
                else
                {
                    ctx->captured_id_ = r.error();
                    return std::move(ctx);
                }
            }
            catch( capturing_exception const & )
            {
                throw;
            }
            catch( exception_base const & e )
            {
                ctx->captured_id_ = e.get_error_id();
                throw_exception( capturing_exception(std::current_exception(), std::move(ctx)) );
            }
            catch(...)
            {
                ctx->captured_id_ = cur_err.assigned_error_id();
                throw_exception( capturing_exception(std::current_exception(), std::move(ctx)) );
            }
        }

        template <class R, class Future>
        inline
        decltype(std::declval<Future>().get())
        future_get_impl(is_result_tag<R, false>, Future & fut )
        {
            try
            {
                return fut.get();
            }
            catch( capturing_exception const & cap )
            {
                cap.unload_and_rethrow_original_exception();
            }
        }

        template <class R, class Future>
        inline
        decltype(std::declval<Future>().get())
        future_get_impl(is_result_tag<R, true>, Future & fut )
        {
            try
            {
                if( auto r = fut.get() )
                    return r;
                else
                    return error_id(r.error()); // unloads
            }
            catch( capturing_exception const & cap )
            {
                cap.unload_and_rethrow_original_exception();
            }
        }
    }

#endif

    template <class F, class... A>
    inline
    decltype(std::declval<F>()(std::forward<A>(std::declval<A>())...))
    capture(context_ptr && ctx, F && f, A... a)
    {
        using namespace leaf_detail;
        return capture_impl(is_result_tag<decltype(std::declval<F>()(std::forward<A>(std::declval<A>())...))>(), std::move(ctx), std::forward<F>(f), std::forward<A>(a)...);
    }

    template <class Future>
    inline
    decltype(std::declval<Future>().get())
    future_get( Future & fut )
    {
        using namespace leaf_detail;
        return future_get_impl(is_result_tag<decltype(std::declval<Future>().get())>(), fut);
    }

    ////////////////////////////////////////

#ifndef BOOST_LEAF_NO_EXCEPTIONS

    template <class T>
    class result;

    namespace leaf_detail
    {
        inline error_id catch_exceptions_helper( std::exception const & ex, leaf_detail_mp11::mp_list<> )
        {
            return leaf::new_error(std::current_exception());
        }

        template <class Ex1, class... Ex>
        inline error_id catch_exceptions_helper( std::exception const & ex, leaf_detail_mp11::mp_list<Ex1,Ex...> )
        {
            if( Ex1 const * p = dynamic_cast<Ex1 const *>(&ex) )
                return catch_exceptions_helper(ex, leaf_detail_mp11::mp_list<Ex...>{ }).load(*p);
            else
                return catch_exceptions_helper(ex, leaf_detail_mp11::mp_list<Ex...>{ });
        }

        template <class T>
        struct deduce_exception_to_result_return_type_impl
        {
            using type = result<T>;
        };

        template <class T>
        struct deduce_exception_to_result_return_type_impl<result<T>>
        {
            using type = result<T>;
        };

        template <class T>
        using deduce_exception_to_result_return_type = typename deduce_exception_to_result_return_type_impl<T>::type;
    }

    template <class... Ex, class F>
    inline
    leaf_detail::deduce_exception_to_result_return_type<leaf_detail::fn_return_type<F>>
    exception_to_result( F && f ) noexcept
    {
        try
        {
            return std::forward<F>(f)();
        }
        catch( std::exception const & ex )
        {
            return leaf_detail::catch_exceptions_helper(ex, leaf_detail_mp11::mp_list<Ex...>());
        }
        catch(...)
        {
            return leaf::new_error(std::current_exception());
        }
    }

#endif

} }

#endif
// <<< #include <boost/leaf/capture.hpp>
#line 10 "../../include/boost/leaf/detail/all.hpp"
// >>> #include <boost/leaf/common.hpp>
#line 1 "boost/leaf/common.hpp"
#ifndef BOOST_LEAF_COMMON_HPP_INCLUDED
#define BOOST_LEAF_COMMON_HPP_INCLUDED

// Copyright (c) 2018-2020 Emil Dotchevski and Reverge Studios, Inc.

// Distributed under the Boost Software License, Version 1.0. (See accompanying
// file LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)

#ifndef BOOST_LEAF_ENABLE_WARNINGS
#   if defined(__clang__)
#       pragma clang system_header
#   elif (__GNUC__*100+__GNUC_MINOR__>301)
#       pragma GCC system_header
#   elif defined(_MSC_VER)
#       pragma warning(push,1)
#   endif
#endif

#include <string>
#include <cerrno>
#ifdef _WIN32
#   include <Windows.h>
#   include <cstring>
#ifdef min
#   undef min
#endif
#ifdef max
#   undef max
#endif
#endif

namespace boost { namespace leaf {

    struct e_api_function { char const * value; };

    struct e_file_name { std::string value; };

    struct e_errno
    {
        int value;

        template <class CharT, class Traits>
        friend std::basic_ostream<CharT, Traits> & operator<<( std::basic_ostream<CharT, Traits> & os, e_errno const & err )
        {
            return os << type<e_errno>() << ": " << err.value << ", \"" << std::strerror(err.value) << '"';
        }
    };

    struct e_type_info_name { char const * value; };

    struct e_at_line { int value; };

    namespace windows
    {
        struct e_LastError
        {
            unsigned value;

#ifdef _WIN32
            template <class CharT, class Traits>
            friend std::basic_ostream<CharT, Traits> & operator<<( std::basic_ostream<CharT, Traits> os, e_LastError const & err )
            {
                struct msg_buf
                {
                    LPVOID * p;
                    msg_buf(): p(0) { }
                    ~msg_buf() noexcept { if(p) LocalFree(p); }
                };
                msg_buf mb;
                if( FormatMessageA(
                    FORMAT_MESSAGE_ALLOCATE_BUFFER|FORMAT_MESSAGE_FROM_SYSTEM|FORMAT_MESSAGE_IGNORE_INSERTS,
                    0,
                    err.value,
                    MAKELANGID(LANG_NEUTRAL,SUBLANG_DEFAULT),
                    (LPSTR)&mb.p,
                    0,
                    0) )
                {
                    BOOST_LEAF_ASSERT(mb.p != 0);
                    char * z = std::strchr((LPSTR)mb.p,0);
                    if( z[-1] == '\n' )
                        *--z = 0;
                    if( z[-1] == '\r' )
                        *--z = 0;
                    return os << type<e_LastError>() << ": " << err.value << ", \"" << (LPCSTR)mb.p << '"';
                }
                return os;
            }
#else
            // TODO : Other platforms
#endif
        };
    }

} }

#endif
// <<< #include <boost/leaf/common.hpp>
#line 11 "../../include/boost/leaf/detail/all.hpp"
// >>> #include <boost/leaf/context.hpp>
#line 1 "boost/leaf/context.hpp"
#ifndef BOOST_LEAF_CONTEXT_HPP_INCLUDED
#define BOOST_LEAF_CONTEXT_HPP_INCLUDED

// Copyright (c) 2018-2020 Emil Dotchevski and Reverge Studios, Inc.

// Distributed under the Boost Software License, Version 1.0. (See accompanying
// file LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)

#ifndef BOOST_LEAF_ENABLE_WARNINGS
#   if defined(__clang__)
#       pragma clang system_header
#   elif (__GNUC__*100+__GNUC_MINOR__>301)
#       pragma GCC system_header
#   elif defined(_MSC_VER)
#       pragma warning(push,1)
#   endif
#endif


namespace boost { namespace leaf {

    class error_info;
    class diagnostic_info;
    class verbose_diagnostic_info;

    template <class>
    struct is_predicate: std::false_type
    {
    };

    namespace leaf_detail
    {
        template <class T>
        struct is_exception: std::is_base_of<std::exception, typename std::decay<T>::type>
        {
        };

        template <class E>
        struct handler_argument_traits;

        template <class E, bool IsPredicate = is_predicate<E>::value>
        struct handler_argument_traits_defaults;

        template <class E>
        struct handler_argument_traits_defaults<E, false>
        {
            using error_type = typename std::decay<E>::type;
            constexpr static bool always_available = false;

            template <class Tup>
            BOOST_LEAF_CONSTEXPR static error_type const * check( Tup const &, error_info const & ) noexcept;

            template <class Tup>
            BOOST_LEAF_CONSTEXPR static error_type * check( Tup &, error_info const & ) noexcept;

            template <class Tup>
            BOOST_LEAF_CONSTEXPR static E get( Tup & tup, error_info const & ei ) noexcept
            {
                return *check(tup, ei);
            }

            static_assert(!is_predicate<error_type>::value, "Handlers must take predicate arguments by value");
            static_assert(!std::is_same<E, error_info>::value, "Handlers must take leaf::error_info arguments by const &");
            static_assert(!std::is_same<E, diagnostic_info>::value, "Handlers must take leaf::diagnostic_info arguments by const &");
            static_assert(!std::is_same<E, verbose_diagnostic_info>::value, "Handlers must take leaf::verbose_diagnostic_info arguments by const &");
        };

        template <class Pred>
        struct handler_argument_traits_defaults<Pred, true>: handler_argument_traits<typename Pred::error_type>
        {
            using base = handler_argument_traits<typename Pred::error_type>;
            static_assert(!base::always_available, "Predicates can't use types that are always_available");

            template <class Tup>
            BOOST_LEAF_CONSTEXPR static bool check( Tup const & tup, error_info const & ei ) noexcept
            {
                auto e = base::check(tup, ei);
                return e && Pred::evaluate(*e);
            };

            template <class Tup>
            BOOST_LEAF_CONSTEXPR static Pred get( Tup const & tup, error_info const & ei ) noexcept
            {
                return Pred{*base::check(tup, ei)};
            }
        };

        template <class E>
        struct handler_argument_always_available
        {
            using error_type = E;
            constexpr static bool always_available = true;

            template <class Tup>
            BOOST_LEAF_CONSTEXPR static bool check( Tup &, error_info const & ) noexcept
            {
                return true;
            };
        };

        template <class E>
        struct handler_argument_traits: handler_argument_traits_defaults<E>
        {
        };

        template <>
        struct handler_argument_traits<void>
        {
            using error_type = void;
            constexpr static bool always_available = false;

            template <class Tup>
            BOOST_LEAF_CONSTEXPR static std::exception const * check( Tup const &, error_info const & ) noexcept;
        };

        template <class E>
        struct handler_argument_traits<E &&>
        {
            static_assert(sizeof(E) == 0, "Error handlers may not take rvalue ref arguments");
        };

        template <class E>
        struct handler_argument_traits<E *>: handler_argument_always_available<typename std::remove_const<E>::type>
        {
            template <class Tup>
            BOOST_LEAF_CONSTEXPR static E * get( Tup & tup, error_info const & ei) noexcept
            {
                return handler_argument_traits_defaults<E>::check(tup, ei);
            }
        };

        template <>
        struct handler_argument_traits<error_info const &>: handler_argument_always_available<void>
        {
            template <class Tup>
            BOOST_LEAF_CONSTEXPR static error_info const & get( Tup const &, error_info const & ei ) noexcept
            {
                return ei;
            }
        };

        template <class E>
        struct handler_argument_traits_require_by_value
        {
            static_assert(sizeof(E) == 0, "Error handlers must take this type by value");
        };
    }

    ////////////////////////////////////////

    namespace leaf_detail
    {
        template <int I, class Tuple>
        struct tuple_for_each
        {
            BOOST_LEAF_CONSTEXPR static void activate( Tuple & tup ) noexcept
            {
                static_assert(!std::is_same<error_info, typename std::decay<decltype(std::get<I-1>(tup))>::type>::value, "Bug in LEAF: context type deduction");
                tuple_for_each<I-1,Tuple>::activate(tup);
                std::get<I-1>(tup).activate();
            }

            BOOST_LEAF_CONSTEXPR static void deactivate( Tuple & tup ) noexcept
            {
                static_assert(!std::is_same<error_info, typename std::decay<decltype(std::get<I-1>(tup))>::type>::value, "Bug in LEAF: context type deduction");
                std::get<I-1>(tup).deactivate();
                tuple_for_each<I-1,Tuple>::deactivate(tup);
            }

            BOOST_LEAF_CONSTEXPR static void propagate( Tuple & tup ) noexcept
            {
                static_assert(!std::is_same<error_info, typename std::decay<decltype(std::get<I-1>(tup))>::type>::value, "Bug in LEAF: context type deduction");
                auto & sl = std::get<I-1>(tup);
                sl.propagate();
                tuple_for_each<I-1,Tuple>::propagate(tup);
            }

            BOOST_LEAF_CONSTEXPR static void propagate_captured( Tuple & tup, int err_id ) noexcept
            {
                static_assert(!std::is_same<error_info, typename std::decay<decltype(std::get<I-1>(tup))>::type>::value, "Bug in LEAF: context type deduction");
                auto & sl = std::get<I-1>(tup);
                if( sl.has_value(err_id) )
                    load_slot(err_id, std::move(sl).value(err_id));
                tuple_for_each<I-1,Tuple>::propagate_captured(tup, err_id);
            }

            static void print( std::ostream & os, void const * tup, int key_to_print )
            {
                BOOST_LEAF_ASSERT(tup != 0);
                tuple_for_each<I-1,Tuple>::print(os, tup, key_to_print);
                std::get<I-1>(*static_cast<Tuple const *>(tup)).print(os, key_to_print);
            }
        };

        template <class Tuple>
        struct tuple_for_each<0, Tuple>
        {
            BOOST_LEAF_CONSTEXPR static void activate( Tuple & ) noexcept { }
            BOOST_LEAF_CONSTEXPR static void deactivate( Tuple & ) noexcept { }
            BOOST_LEAF_CONSTEXPR static void propagate( Tuple & tup ) noexcept { }
            BOOST_LEAF_CONSTEXPR static void propagate_captured( Tuple & tup, int ) noexcept { }
            static void print( std::ostream &, void const *, int ) { }
        };
    }

    ////////////////////////////////////////////

#if BOOST_LEAF_DIAGNOSTICS

    namespace leaf_detail
    {
        template <class T> struct requires_unexpected { constexpr static bool value = false; };
        template <class T> struct requires_unexpected<T const> { constexpr static bool value = requires_unexpected<T>::value; };
        template <class T> struct requires_unexpected<T const &> { constexpr static bool value = requires_unexpected<T>::value; };
        template <class T> struct requires_unexpected<T const *> { constexpr static bool value = requires_unexpected<T>::value; };
        template <> struct requires_unexpected<e_unexpected_count> { constexpr static bool value = true; };
        template <> struct requires_unexpected<e_unexpected_info> { constexpr static bool value = true; };

        template <class L>
        struct unexpected_requested;

        template <template <class ...> class L>
        struct unexpected_requested<L<>>
        {
            constexpr static bool value = false;
        };

        template <template <class...> class L, template <class> class S, class Car, class... Cdr>
        struct unexpected_requested<L<S<Car>, S<Cdr>...>>
        {
            constexpr static bool value = requires_unexpected<Car>::value || unexpected_requested<L<S<Cdr>...>>::value;
        };
    }

#endif

    ////////////////////////////////////////////

    namespace leaf_detail
    {
        template <class T> struct does_not_participate_in_context_deduction: std::false_type { };
        template <> struct does_not_participate_in_context_deduction<void>: std::true_type { };

        template <class L>
        struct deduce_e_type_list;

        template <template<class...> class L, class... T>
        struct deduce_e_type_list<L<T...>>
        {
            using type =
                leaf_detail_mp11::mp_remove_if<
                    leaf_detail_mp11::mp_unique<
                        leaf_detail_mp11::mp_list<typename handler_argument_traits<T>::error_type...>
                    >,
                    does_not_participate_in_context_deduction
                >;
        };

        template <class L>
        struct deduce_e_tuple_impl;

        template <template <class...> class L, class... E>
        struct deduce_e_tuple_impl<L<E...>>
        {
            using type = std::tuple<slot<E>...>;
        };

        template <class... E>
        using deduce_e_tuple = typename deduce_e_tuple_impl<typename deduce_e_type_list<leaf_detail_mp11::mp_list<E...>>::type>::type;
    }

    ////////////////////////////////////////////

    template <class... E>
    class context
    {
        context( context const & ) = delete;
        context & operator=( context const & ) = delete;

        using Tup = leaf_detail::deduce_e_tuple<E...>;
        Tup tup_;

#if !defined(BOOST_LEAF_NO_THREADS) && !defined(NDEBUG)
        std::thread::id thread_id_;
#endif
        bool is_active_;

    protected:

        BOOST_LEAF_CONSTEXPR error_id propagate_captured_errors( error_id err_id ) noexcept
        {
            leaf_detail::tuple_for_each<std::tuple_size<Tup>::value,Tup>::propagate_captured(tup_, err_id.value());
            return err_id;
        }

    public:

        BOOST_LEAF_CONSTEXPR context( context && x ) noexcept:
            tup_(std::move(x.tup_)),
            is_active_(false)
        {
            BOOST_LEAF_ASSERT(!x.is_active());
        }

        BOOST_LEAF_CONSTEXPR context() noexcept:
            is_active_(false)
        {
        }

        ~context() noexcept
        {
            BOOST_LEAF_ASSERT(!is_active());
        }

        BOOST_LEAF_CONSTEXPR Tup const & tup() const noexcept
        {
            return tup_;
        }

        BOOST_LEAF_CONSTEXPR Tup & tup() noexcept
        {
            return tup_;
        }

        BOOST_LEAF_CONSTEXPR void activate() noexcept
        {
            using namespace leaf_detail;
            BOOST_LEAF_ASSERT(!is_active());
            tuple_for_each<std::tuple_size<Tup>::value,Tup>::activate(tup_);
#if BOOST_LEAF_DIAGNOSTICS
            if( unexpected_requested<Tup>::value )
                ++tl_unexpected_enabled<>::counter;
#endif
#if !defined(BOOST_LEAF_NO_THREADS) && !defined(NDEBUG)
            thread_id_ = std::this_thread::get_id();
#endif
            is_active_ = true;
        }

        BOOST_LEAF_CONSTEXPR void deactivate() noexcept
        {
            using namespace leaf_detail;
            BOOST_LEAF_ASSERT(is_active());
            is_active_ = false;
#if !defined(BOOST_LEAF_NO_THREADS) && !defined(NDEBUG)
            BOOST_LEAF_ASSERT(std::this_thread::get_id() == thread_id_);
            thread_id_ = std::thread::id();
#endif
#if BOOST_LEAF_DIAGNOSTICS
            if( unexpected_requested<Tup>::value )
                --tl_unexpected_enabled<>::counter;
#endif
            tuple_for_each<std::tuple_size<Tup>::value,Tup>::deactivate(tup_);
        }

        BOOST_LEAF_CONSTEXPR void propagate() noexcept
        {
            leaf_detail::tuple_for_each<std::tuple_size<Tup>::value,Tup>::propagate(tup_);
        }

        BOOST_LEAF_CONSTEXPR bool is_active() const noexcept
        {
            return is_active_;
        }

        void print( std::ostream & os ) const
        {
            leaf_detail::tuple_for_each<std::tuple_size<Tup>::value,Tup>::print(os, &tup_, 0);
        }

        template <class R, class... H>
        BOOST_LEAF_CONSTEXPR R handle_error( error_id, H && ... ) const;

        template <class R, class... H>
        BOOST_LEAF_CONSTEXPR R handle_error( error_id, H && ... );
    };

    ////////////////////////////////////////

    namespace leaf_detail
    {
        template <class TypeList>
        struct deduce_context_impl;

        template <template <class...> class L, class... E>
        struct deduce_context_impl<L<E...>>
        {
            using type = context<E...>;
        };

        template <class TypeList>
        using deduce_context = typename deduce_context_impl<TypeList>::type;

        template <class H>
        struct fn_mp_args_fwd
        {
            using type = fn_mp_args<H>;
        };

        template <class... H>
        struct fn_mp_args_fwd<std::tuple<H...> &>: fn_mp_args_fwd<std::tuple<H...>> { };

        template <class... H>
        struct fn_mp_args_fwd<std::tuple<H...>>
        {
            using type = leaf_detail_mp11::mp_append<typename fn_mp_args_fwd<H>::type...>;
        };

        template <class... H>
        struct context_type_from_handlers_impl
        {
            using type = deduce_context<leaf_detail_mp11::mp_append<typename fn_mp_args_fwd<H>::type...>>;
        };

        template <class Ctx>
        struct polymorphic_context_impl: polymorphic_context, Ctx
        {
            error_id propagate_captured_errors() noexcept final override { return Ctx::propagate_captured_errors(captured_id_); }
            void activate() noexcept final override { Ctx::activate(); }
            void deactivate() noexcept final override { Ctx::deactivate(); }
            void propagate() noexcept final override { Ctx::propagate(); }
            bool is_active() const noexcept final override { return Ctx::is_active(); }
            void print( std::ostream & os ) const final override { return Ctx::print(os); }
        };
    }

    template <class... H>
    using context_type_from_handlers = typename leaf_detail::context_type_from_handlers_impl<H...>::type;

    ////////////////////////////////////////////

    template <class...  H>
    BOOST_LEAF_CONSTEXPR inline context_type_from_handlers<H...> make_context() noexcept
    {
        return { };
    }

    template <class...  H>
    BOOST_LEAF_CONSTEXPR inline context_type_from_handlers<H...> make_context( H && ... ) noexcept
    {
        return { };
    }

    ////////////////////////////////////////////

    template <class...  H>
    inline context_ptr make_shared_context() noexcept
    {
        return std::make_shared<leaf_detail::polymorphic_context_impl<context_type_from_handlers<H...>>>();
    }

    template <class...  H>
    inline context_ptr make_shared_context( H && ... ) noexcept
    {
        return std::make_shared<leaf_detail::polymorphic_context_impl<context_type_from_handlers<H...>>>();
    }

} }

#endif
// <<< #include <boost/leaf/context.hpp>
#line 12 "../../include/boost/leaf/detail/all.hpp"
// >>> #include <boost/leaf/handle_errors.hpp>
#line 1 "boost/leaf/handle_errors.hpp"
#ifndef BOOST_LEAF_HANDLE_ERRORS_HPP_INCLUDED
#define BOOST_LEAF_HANDLE_ERRORS_HPP_INCLUDED

// Copyright (c) 2018-2020 Emil Dotchevski and Reverge Studios, Inc.

// Distributed under the Boost Software License, Version 1.0. (See accompanying
// file LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)

#ifndef BOOST_LEAF_ENABLE_WARNINGS
#   if defined(__clang__)
#       pragma clang system_header
#   elif (__GNUC__*100+__GNUC_MINOR__>301)
#       pragma GCC system_header
#   elif defined(_MSC_VER)
#       pragma warning(push,1)
#   endif
#endif

// >>> #include <boost/leaf/detail/demangle.hpp>
#line 1 "boost/leaf/detail/demangle.hpp"
#ifndef BOOST_LEAF_DETAIL_DEMANGLE_HPP_INCLUDED
#define BOOST_LEAF_DETAIL_DEMANGLE_HPP_INCLUDED

// Copyright (c) 2018-2020 Emil Dotchevski and Reverge Studios, Inc.

// Distributed under the Boost Software License, Version 1.0. (See accompanying
// file LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)

// core::demangle
//
// Copyright 2014 Peter Dimov
// Copyright 2014 Andrey Semashev
//
// Distributed under the Boost Software License, Version 1.0.
// See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt

#ifndef BOOST_LEAF_ENABLE_WARNINGS
#   if defined(__clang__)
#       pragma clang system_header
#   elif (__GNUC__*100+__GNUC_MINOR__>301)
#       pragma GCC system_header
#   elif defined(_MSC_VER)
#       pragma warning(push,1)
#   endif
#endif

#if !defined(_MSC_VER)
#   if defined(__has_include) && __has_include(<cxxabi.h>)
#       define BOOST_LEAF_HAS_CXXABI_H
#   endif
#endif

#if defined( BOOST_LEAF_HAS_CXXABI_H )
#   include <cxxabi.h>
// For some architectures (mips, mips64, x86, x86_64) cxxabi.h in Android NDK is implemented by gabi++ library
// (https://android.googlesource.com/platform/ndk/+/master/sources/cxx-stl/gabi++/), which does not implement
// abi::__cxa_demangle(). We detect this implementation by checking the include guard here.
#   if defined( __GABIXX_CXXABI_H__ )
#       undef BOOST_LEAF_HAS_CXXABI_H
#   else
#       include <cstddef>
#   endif
#endif

namespace boost { namespace leaf {

    namespace leaf_detail
    {
        inline char const * demangle_alloc( char const * name ) noexcept;
        inline void demangle_free( char const * name ) noexcept;

        class scoped_demangled_name
        {
        private:

            char const * m_p;

        public:

            explicit scoped_demangled_name( char const * name ) noexcept :
                m_p( demangle_alloc( name ) )
            {
            }

            ~scoped_demangled_name() noexcept
            {
                demangle_free( m_p );
            }

            char const * get() const noexcept
            {
                return m_p;
            }

            scoped_demangled_name( scoped_demangled_name const& ) = delete;
            scoped_demangled_name& operator= ( scoped_demangled_name const& ) = delete;
        };

#if defined( BOOST_LEAF_HAS_CXXABI_H )

        inline char const * demangle_alloc( char const * name ) noexcept
        {
            int status = 0;
            std::size_t size = 0;
            return abi::__cxa_demangle( name, NULL, &size, &status );
        }

        inline void demangle_free( char const * name ) noexcept
        {
            std::free( const_cast< char* >( name ) );
        }

        inline char const * demangle( char const * name )
        {
            scoped_demangled_name demangled_name( name );
            char const * p = demangled_name.get();
            if( !p )
                p = name;
            return p;
        }

#else

        inline char const * demangle_alloc( char const * name ) noexcept
        {
            return name;
        }

        inline void demangle_free( char const * ) noexcept
        {
        }

        inline char const * demangle( char const * name )
        {
            return name;
        }

#endif
    }

} }

#ifdef BOOST_LEAF_HAS_CXXABI_H
#   undef BOOST_LEAF_HAS_CXXABI_H
#endif

#endif
// <<< #include <boost/leaf/detail/demangle.hpp>
#line 21 "boost/leaf/handle_errors.hpp"

#ifndef BOOST_LEAF_NO_EXCEPTIONS
#endif

namespace boost { namespace leaf {

    class error_info
    {
        error_info & operator=( error_info const & ) = delete;

#ifndef BOOST_LEAF_NO_EXCEPTIONS
        static error_id unpack_error_id( std::exception const * ex ) noexcept
        {
            if( std::system_error const * se = dynamic_cast<std::system_error const *>(ex) )
                if( is_error_id(se->code()) )
                    return leaf_detail::make_error_id(se->code().value());
            if( std::error_code const * ec = dynamic_cast<std::error_code const *>(ex) )
                if( is_error_id(*ec) )
                    return leaf_detail::make_error_id(ec->value());
            if( error_id const * err_id = dynamic_cast<error_id const *>(ex) )
                return *err_id;
            return current_error();
        }

        std::exception * const ex_;
#endif

        error_id const err_id_;

    protected:

        error_info( error_info const & ) noexcept = default;

        template <class CharT, class Traits>
        void print( std::basic_ostream<CharT, Traits> & os ) const
        {
            os << "Error ID = " << err_id_.value();
#ifndef BOOST_LEAF_NO_EXCEPTIONS
            if( ex_ )
            {
                os <<
                    "\nException dynamic type: " << leaf_detail::demangle(typeid(*ex_).name()) <<
                    "\nstd::exception::what(): " << ex_->what();
            }
#endif
        }

    public:

        BOOST_LEAF_CONSTEXPR explicit error_info( error_id id ) noexcept:
#ifndef BOOST_LEAF_NO_EXCEPTIONS
            ex_(0),
#endif
            err_id_(id)
        {
        }

#ifndef BOOST_LEAF_NO_EXCEPTIONS
        explicit error_info( std::exception * ex ) noexcept:
            ex_(ex),
            err_id_(unpack_error_id(ex_))
        {
        }
#endif

        BOOST_LEAF_CONSTEXPR error_id error() const noexcept
        {
            return err_id_;
        }

        BOOST_LEAF_CONSTEXPR std::exception * exception() const noexcept
        {
#ifdef BOOST_LEAF_NO_EXCEPTIONS
            return nullptr;
#else
            return ex_;
#endif
        }

        template <class CharT, class Traits>
        friend std::basic_ostream<CharT, Traits> & operator<<( std::basic_ostream<CharT, Traits> & os, error_info const & x )
        {
            os << "leaf::error_info: ";
            x.print(os);
            return os << '\n';
        }
    };

    ////////////////////////////////////////

#if BOOST_LEAF_DIAGNOSTICS

    class diagnostic_info: public error_info
    {
        leaf_detail::e_unexpected_count const * e_uc_;
        void const * tup_;
        void (*print_)( std::ostream &, void const * tup, int key_to_print );

    protected:

        diagnostic_info( diagnostic_info const & ) noexcept = default;

        template <class Tup>
        BOOST_LEAF_CONSTEXPR diagnostic_info( error_info const & ei, leaf_detail::e_unexpected_count const * e_uc, Tup const & tup ) noexcept:
            error_info(ei),
            e_uc_(e_uc),
            tup_(&tup),
            print_(&leaf_detail::tuple_for_each<std::tuple_size<Tup>::value, Tup>::print)
        {
        }

    public:

        template <class CharT, class Traits>
        friend std::basic_ostream<CharT, Traits> & operator<<( std::basic_ostream<CharT, Traits> & os, diagnostic_info const & x )
        {
            os << "leaf::diagnostic_info for ";
            x.print(os);
            os << ":\n";
            x.print_(os, x.tup_, x.error().value());
            if( x.e_uc_  )
                x.e_uc_->print(os);
            return os;
        }
    };

    namespace leaf_detail
    {
        struct diagnostic_info_: diagnostic_info
        {
            template <class Tup>
            BOOST_LEAF_CONSTEXPR diagnostic_info_( error_info const & ei, leaf_detail::e_unexpected_count const * e_uc, Tup const & tup ) noexcept:
                diagnostic_info(ei, e_uc, tup)
            {
            }
        };

        template <>
        struct handler_argument_traits<diagnostic_info const &>: handler_argument_always_available<e_unexpected_count>
        {
            template <class Tup>
            BOOST_LEAF_CONSTEXPR static diagnostic_info_ get( Tup const & tup, error_info const & ei ) noexcept
            {
                return diagnostic_info_(ei, handler_argument_traits_defaults<e_unexpected_count>::check(tup, ei), tup);
            }
        };
    }

#else

    class diagnostic_info: public error_info
    {
    protected:

        diagnostic_info( diagnostic_info const & ) noexcept = default;

        BOOST_LEAF_CONSTEXPR diagnostic_info( error_info const & ei ) noexcept:
            error_info(ei)
        {
        }

    public:

        template <class CharT, class Traits>
        friend std::basic_ostream<CharT, Traits> & operator<<( std::basic_ostream<CharT, Traits> & os, diagnostic_info const & x )
        {
            os <<
                "leaf::diagnostic_info requires #define BOOST_LEAF_DIAGNOSTICS 1\n"
                "leaf::error_info: ";
            x.print(os);
            return os << '\n';
        }
    };

    namespace leaf_detail
    {
        struct diagnostic_info_: diagnostic_info
        {
            BOOST_LEAF_CONSTEXPR diagnostic_info_( error_info const & ei ) noexcept:
                diagnostic_info(ei)
            {
            }
        };

        template <>
        struct handler_argument_traits<diagnostic_info const &>: handler_argument_always_available<void>
        {
            template <class Tup>
            BOOST_LEAF_CONSTEXPR static diagnostic_info_ get( Tup const & tup, error_info const & ei ) noexcept
            {
                return diagnostic_info_(ei);
            }
        };
    }

#endif

    ////////////////////////////////////////

#if BOOST_LEAF_DIAGNOSTICS

    class verbose_diagnostic_info: public error_info
    {
        leaf_detail::e_unexpected_info const * e_ui_;
        void const * tup_;
        void (*print_)( std::ostream &, void const * tup, int key_to_print );

    protected:

        verbose_diagnostic_info( verbose_diagnostic_info const & ) noexcept = default;

        template <class Tup>
        BOOST_LEAF_CONSTEXPR verbose_diagnostic_info( error_info const & ei, leaf_detail::e_unexpected_info const * e_ui, Tup const & tup ) noexcept:
            error_info(ei),
            e_ui_(e_ui),
            tup_(&tup),
            print_(&leaf_detail::tuple_for_each<std::tuple_size<Tup>::value, Tup>::print)
        {
        }

    public:

        template <class CharT, class Traits>
        friend std::basic_ostream<CharT, Traits> & operator<<( std::basic_ostream<CharT, Traits> & os, verbose_diagnostic_info const & x )
        {
            os << "leaf::verbose_diagnostic_info for ";
            x.print(os);
            os << ":\n";
            x.print_(os, x.tup_, x.error().value());
            if( x.e_ui_ )
                x.e_ui_->print(os);
            return os;
        }
    };

    namespace leaf_detail
    {
        struct verbose_diagnostic_info_: verbose_diagnostic_info
        {
            template <class Tup>
            BOOST_LEAF_CONSTEXPR verbose_diagnostic_info_( error_info const & ei, leaf_detail::e_unexpected_info const * e_ui, Tup const & tup ) noexcept:
                verbose_diagnostic_info(ei, e_ui, tup)
            {
            }
        };

        template <>
        struct handler_argument_traits<verbose_diagnostic_info const &>: handler_argument_always_available<e_unexpected_info>
        {
            template <class Tup>
            BOOST_LEAF_CONSTEXPR static verbose_diagnostic_info_ get( Tup const & tup, error_info const & ei ) noexcept
            {
                return verbose_diagnostic_info_(ei, handler_argument_traits_defaults<e_unexpected_info>::check(tup, ei), tup);
            }
        };
    }

#else

    class verbose_diagnostic_info: public error_info
    {
    protected:

        verbose_diagnostic_info( verbose_diagnostic_info const & ) noexcept = default;

        BOOST_LEAF_CONSTEXPR verbose_diagnostic_info( error_info const & ei ) noexcept:
            error_info(ei)
        {
        }

    public:

        template <class CharT, class Traits>
        friend std::basic_ostream<CharT, Traits> & operator<<( std::basic_ostream<CharT, Traits> & os, verbose_diagnostic_info const & x )
        {
            os <<
                "leaf::verbose_diagnostic_info requires #define BOOST_LEAF_DIAGNOSTICS 1\n"
                "leaf::error_info: ";
            x.print(os);
            return os << '\n';
        }
    };

    namespace leaf_detail
    {
        struct verbose_diagnostic_info_: verbose_diagnostic_info
        {
            BOOST_LEAF_CONSTEXPR verbose_diagnostic_info_( error_info const & ei ) noexcept:
                verbose_diagnostic_info(ei)
            {
            }
        };


        template <>
        struct handler_argument_traits<verbose_diagnostic_info const &>: handler_argument_always_available<void>
        {
            template <class Tup>
            BOOST_LEAF_CONSTEXPR static verbose_diagnostic_info_ get( Tup const & tup, error_info const & ei ) noexcept
            {
                return verbose_diagnostic_info_(ei);
            }
        };
    }

#endif

    ////////////////////////////////////////

    namespace leaf_detail
    {
        template <class T, class... List>
        struct type_index;

        template <class T, class... Cdr>
        struct type_index<T, T, Cdr...>
        {
            constexpr static int value = 0;
        };

        template <class T, class Car, class... Cdr>
        struct type_index<T, Car, Cdr...>
        {
            constexpr static int value = 1 + type_index<T,Cdr...>::value;
        };

        template <class T, class Tuple>
        struct tuple_type_index;

        template <class T, class... TupleTypes>
        struct tuple_type_index<T,std::tuple<TupleTypes...>>
        {
            constexpr static int value = type_index<T,TupleTypes...>::value;
        };

#ifndef BOOST_LEAF_NO_EXCEPTIONS

        template <class E, bool = std::is_class<E>::value>
        struct peek_exception;

        template <>
        struct peek_exception<std::exception const, true>
        {
            BOOST_LEAF_CONSTEXPR static std::exception const * peek( error_info const & ei ) noexcept
            {
                return ei.exception();
            }
        };

        template <>
        struct peek_exception<std::exception, true>
        {
            BOOST_LEAF_CONSTEXPR static std::exception * peek( error_info const & ei ) noexcept
            {
                return ei.exception();
            }
        };

        template <>
        struct peek_exception<std::error_code const, true>
        {
            static std::error_code const * peek( error_info const & ei ) noexcept
            {
                auto const ex = ei.exception();
                if( std::system_error * se = dynamic_cast<std::system_error *>(ex) )
                    return &se->code();
                else if( std::error_code * ec = dynamic_cast<std::error_code *>(ex) )
                    return ec;
                else
                    return 0;
            }
        };

        template <>
        struct peek_exception<std::error_code, true>
        {
            static std::error_code * peek( error_info const & ei ) noexcept
            {
                auto const ex = ei.exception();
                if( std::system_error * se = dynamic_cast<std::system_error *>(ex) )
                    return const_cast<std::error_code *>(&se->code());
                else if( std::error_code * ec = dynamic_cast<std::error_code *>(ex) )
                    return ec;
                else
                    return 0;
            }
        };

        template <class E>
        struct peek_exception<E, true>
        {
            static E * peek( error_info const & ei ) noexcept
            {
                return dynamic_cast<E *>(ei.exception());
            }
        };

        template <class E>
        struct peek_exception<E, false>
        {
            BOOST_LEAF_CONSTEXPR static E * peek( error_info const & ) noexcept
            {
                return 0;
            }
        };

#endif

        template <class E, class SlotsTuple>
        BOOST_LEAF_CONSTEXPR inline
        E const *
        peek( SlotsTuple const & tup, error_info const & ei ) noexcept
        {
            if( error_id err = ei.error() )
                if( E const * e = std::get<tuple_type_index<slot<E>,SlotsTuple>::value>(tup).has_value(err.value()) )
                    return e;
#ifndef BOOST_LEAF_NO_EXCEPTIONS
                else
                    return peek_exception<E const>::peek(ei);
#endif
            return 0;
        }

        template <class E, class SlotsTuple>
        BOOST_LEAF_CONSTEXPR inline
        E *
        peek( SlotsTuple & tup, error_info const & ei ) noexcept
        {
            if( error_id err = ei.error() )
                if( E * e = std::get<tuple_type_index<slot<E>,SlotsTuple>::value>(tup).has_value(err.value()) )
                    return e;
#ifndef BOOST_LEAF_NO_EXCEPTIONS
                else
                    return peek_exception<E>::peek(ei);
#endif
            return 0;
        }
    }

    ////////////////////////////////////////

    namespace leaf_detail
    {
        template <class A>
        template <class Tup>
        BOOST_LEAF_CONSTEXPR inline
        typename handler_argument_traits_defaults<A, false>::error_type const *
        handler_argument_traits_defaults<A, false>::
        check( Tup const & tup, error_info const & ei ) noexcept
        {
            return peek<typename std::decay<A>::type>(tup, ei);
        }

        template <class A>
        template <class Tup>
        BOOST_LEAF_CONSTEXPR inline
        typename handler_argument_traits_defaults<A, false>::error_type *
        handler_argument_traits_defaults<A, false>::
        check( Tup & tup, error_info const & ei ) noexcept
        {
            return peek<typename std::decay<A>::type>(tup, ei);
        }

        template <class Tup>
        BOOST_LEAF_CONSTEXPR inline
        std::exception const *
        handler_argument_traits<void>::
        check( Tup const &, error_info const & ei ) noexcept
        {
            return ei.exception();
        }

        template <class Tup, class... List>
        struct check_arguments;

        template <class Tup>
        struct check_arguments<Tup>
        {
            BOOST_LEAF_CONSTEXPR static bool check( Tup const &, error_info const & )
            {
                return true;
            }
        };

        template <class Tup, class Car, class... Cdr>
        struct check_arguments<Tup, Car, Cdr...>
        {
            BOOST_LEAF_CONSTEXPR static bool check( Tup & tup, error_info const & ei ) noexcept
            {
                return handler_argument_traits<Car>::check(tup, ei) && check_arguments<Tup, Cdr...>::check(tup, ei);
            }
        };
    }

    ////////////////////////////////////////

    namespace leaf_detail
    {
        template <class>
        struct handler_matches_any_error: std::false_type
        {
        };

        template <template<class...> class L>
        struct handler_matches_any_error<L<>>: std::true_type
        {
        };

        template <template<class...> class L, class Car, class... Cdr>
        struct handler_matches_any_error<L<Car, Cdr...>>
        {
            constexpr static bool value = handler_argument_traits<Car>::always_available && handler_matches_any_error<L<Cdr...>>::value;
        };
    }

    ////////////////////////////////////////

    namespace leaf_detail
    {
        template <class Tup, class... A>
        BOOST_LEAF_CONSTEXPR inline bool check_handler_( Tup & tup, error_info const & ei, leaf_detail_mp11::mp_list<A...> ) noexcept
        {
            return check_arguments<Tup, A...>::check(tup, ei);
        }

        template <class R, class F, bool IsResult = is_result_type<R>::value, class FReturnType = fn_return_type<F>>
        struct handler_caller
        {
            template <class Tup, class... A>
            BOOST_LEAF_CONSTEXPR static R call( Tup & tup, error_info const & ei, F && f, leaf_detail_mp11::mp_list<A...> )
            {
                return std::forward<F>(f)( handler_argument_traits<A>::get(tup, ei)... );
            }
        };

        template <template <class...> class Result, class... E, class F>
        struct handler_caller<Result<void, E...>, F, true, void>
        {
            using R = Result<void, E...>;

            template <class Tup, class... A>
            BOOST_LEAF_CONSTEXPR static R call( Tup & tup, error_info const & ei, F && f, leaf_detail_mp11::mp_list<A...> )
            {
                std::forward<F>(f)( handler_argument_traits<A>::get(tup, ei)... );
                return { };
            }
        };

        template <class T>
        struct is_tuple: std::false_type { };

        template <class... T>
        struct is_tuple<std::tuple<T...>>: std::true_type { };

        template <class... T>
        struct is_tuple<std::tuple<T...> &>: std::true_type { };

        template <class R, class Tup, class H>
        BOOST_LEAF_CONSTEXPR
        inline
        typename std::enable_if<!is_tuple<H>::value, R>::type
        handle_error_( Tup & tup, error_info const & ei, H && h )
        {
            static_assert( handler_matches_any_error<fn_mp_args<H>>::value, "The last handler passed to handle_all must match any error." );
            return handler_caller<R, H>::call( tup, ei, std::forward<H>(h), fn_mp_args<H>{ } );
        }

        template <class R, class Tup, class Car, class... Cdr>
        BOOST_LEAF_CONSTEXPR inline
        typename std::enable_if<!is_tuple<Car>::value, R>::type
        handle_error_( Tup & tup, error_info const & ei, Car && car, Cdr && ... cdr )
        {
            if( handler_matches_any_error<fn_mp_args<Car>>::value || check_handler_( tup, ei, fn_mp_args<Car>{ } ) )
                return handler_caller<R, Car>::call( tup, ei, std::forward<Car>(car), fn_mp_args<Car>{ } );
            else
                return handle_error_<R>( tup, ei, std::forward<Cdr>(cdr)...);
        }

        template <class R, class Tup, class HTup, size_t ... I>
        BOOST_LEAF_CONSTEXPR inline
        R
        handle_error_tuple_( Tup & tup, error_info const & ei, leaf_detail_mp11::index_sequence<I...>, HTup && htup )
        {
            return handle_error_<R>(tup, ei, std::get<I>(std::forward<HTup>(htup))...);
        }

        template <class R, class Tup, class HTup, class... Cdr, size_t ... I>
        BOOST_LEAF_CONSTEXPR inline
        R
        handle_error_tuple_( Tup & tup, error_info const & ei, leaf_detail_mp11::index_sequence<I...>, HTup && htup, Cdr && ... cdr )
        {
            return handle_error_<R>(tup, ei, std::get<I>(std::forward<HTup>(htup))..., std::forward<Cdr>(cdr)...);
        }

        template <class R, class Tup, class H>
        BOOST_LEAF_CONSTEXPR inline
        typename std::enable_if<is_tuple<H>::value, R>::type
        handle_error_( Tup & tup, error_info const & ei, H && h )
        {
            return handle_error_tuple_<R>(
                tup,
                ei,
                leaf_detail_mp11::make_index_sequence<std::tuple_size<typename std::decay<H>::type>::value>(),
                std::forward<H>(h));
        }

        template <class R, class Tup, class Car, class... Cdr>
        BOOST_LEAF_CONSTEXPR inline
        typename std::enable_if<is_tuple<Car>::value, R>::type
        handle_error_( Tup & tup, error_info const & ei, Car && car, Cdr && ... cdr )
        {
            return handle_error_tuple_<R>(
                tup,
                ei,
                leaf_detail_mp11::make_index_sequence<std::tuple_size<typename std::decay<Car>::type>::value>(),
                std::forward<Car>(car),
                std::forward<Cdr>(cdr)...);
        }
    }

    ////////////////////////////////////////

    template <class... E>
    template <class R, class... H>
    BOOST_LEAF_CONSTEXPR BOOST_LEAF_ALWAYS_INLINE
    R
    context<E...>::
    handle_error( error_id id, H && ... h ) const
    {
        BOOST_LEAF_ASSERT(!is_active());
        return leaf_detail::handle_error_<R>(tup(), error_info(id), std::forward<H>(h)...);
    }

    template <class... E>
    template <class R, class... H>
    BOOST_LEAF_CONSTEXPR BOOST_LEAF_ALWAYS_INLINE
    R
    context<E...>::
    handle_error( error_id id, H && ... h )
    {
        BOOST_LEAF_ASSERT(!is_active());
        return leaf_detail::handle_error_<R>(tup(), error_info(id), std::forward<H>(h)...);
    }

    ////////////////////////////////////////

#ifdef BOOST_LEAF_NO_EXCEPTIONS

    template <class TryBlock, class... H>
    BOOST_LEAF_CONSTEXPR inline
    typename std::decay<decltype(std::declval<TryBlock>()().value())>::type
    try_handle_all( TryBlock && try_block, H && ... h ) noexcept
    {
        static_assert(is_result_type<decltype(std::declval<TryBlock>()())>::value, "The return type of the try_block passed to a try_handle_all function must be registered with leaf::is_result_type");
        context_type_from_handlers<H...> ctx;
        auto active_context = activate_context(ctx);
        if( auto r = std::forward<TryBlock>(try_block)() )
            return r.value();
        else
        {
            error_id id = r.error();
            ctx.deactivate();
            using R = typename std::decay<decltype(std::declval<TryBlock>()().value())>::type;
            return ctx.template handle_error<R>(std::move(id), std::forward<H>(h)...);
        }
    }

    template <class TryBlock, class... H>
    BOOST_LEAF_NODISCARD BOOST_LEAF_CONSTEXPR inline
    typename std::decay<decltype(std::declval<TryBlock>()())>::type
    try_handle_some( TryBlock && try_block, H && ... h ) noexcept
    {
        static_assert(is_result_type<decltype(std::declval<TryBlock>()())>::value, "The return type of the try_block passed to a try_handle_some function must be registered with leaf::is_result_type");
        context_type_from_handlers<H...> ctx;
        auto active_context = activate_context(ctx);
        if( auto r = std::forward<TryBlock>(try_block)() )
            return r;
        else
        {
            error_id id = r.error();
            ctx.deactivate();
            using R = typename std::decay<decltype(std::declval<TryBlock>()())>::type;
            auto rr = ctx.template handle_error<R>(std::move(id), std::forward<H>(h)..., [&r]()->R { return std::move(r); });
            if( !rr )
                ctx.propagate();
            return rr;
        }
    }

    template <class TryBlock, class... H>
    BOOST_LEAF_CONSTEXPR inline
    decltype(std::declval<TryBlock>()())
    try_catch( TryBlock && try_block, H && ... ) noexcept
    {
        static_assert(sizeof(context_type_from_handlers<H...>) > 0,
            "When exceptions are disabled, try_catch can't fail and has no use for the handlers, but this ensures that the supplied H... types are compatible.");
        return std::forward<TryBlock>(try_block)();
    }

#else

    namespace leaf_detail
    {
        template <class Ctx, class TryBlock, class... H>
        decltype(std::declval<TryBlock>()())
        try_catch_( Ctx & ctx, TryBlock && try_block, H && ... h )
        {
            using namespace leaf_detail;
            BOOST_LEAF_ASSERT(ctx.is_active());
            using R = decltype(std::declval<TryBlock>()());
            try
            {
                return std::forward<TryBlock>(try_block)();
            }
            catch( capturing_exception const & cap )
            {
                try
                {
                    cap.unload_and_rethrow_original_exception();
                }
                catch( std::exception & ex )
                {
                    ctx.deactivate();
                    return handle_error_<R>(ctx.tup(), error_info(&ex), std::forward<H>(h)...,
                        []() -> R { throw; } );
                }
                catch(...)
                {
                    ctx.deactivate();
                    return handle_error_<R>(ctx.tup(), error_info(nullptr), std::forward<H>(h)...,
                        []() -> R { throw; } );
                }
            }
            catch( std::exception & ex )
            {
                ctx.deactivate();
                return handle_error_<R>(ctx.tup(), error_info(&ex), std::forward<H>(h)...,
                    []() -> R { throw; } );
            }
            catch(...)
            {
                ctx.deactivate();
                return handle_error_<R>(ctx.tup(), error_info(nullptr), std::forward<H>(h)...,
                    []() -> R { throw; } );
            }
        }
    }

    template <class TryBlock, class... H>
    BOOST_LEAF_CONSTEXPR inline
    typename std::decay<decltype(std::declval<TryBlock>()().value())>::type
    try_handle_all( TryBlock && try_block, H && ... h )
    {
        static_assert(is_result_type<decltype(std::declval<TryBlock>()())>::value, "The return type of the try_block passed to a try_handle_all function must be registered with leaf::is_result_type");
        context_type_from_handlers<H...> ctx;
        auto active_context = activate_context(ctx);
        if( auto r = leaf_detail::try_catch_(
                ctx,
                [&]
                {
                    return std::forward<TryBlock>(try_block)();
                },
                std::forward<H>(h)...) )
            return r.value();
        else
        {
            error_id id = r.error();
            if( ctx.is_active() )
                ctx.deactivate();
            using R = typename std::decay<decltype(std::declval<TryBlock>()().value())>::type;
            return ctx.template handle_error<R>(std::move(id), std::forward<H>(h)...);
        }
    }

    template <class TryBlock, class... H>
    BOOST_LEAF_NODISCARD BOOST_LEAF_CONSTEXPR inline
    typename std::decay<decltype(std::declval<TryBlock>()())>::type
    try_handle_some( TryBlock && try_block, H && ... h )
    {
        static_assert(is_result_type<decltype(std::declval<TryBlock>()())>::value, "The return type of the try_block passed to a try_handle_some function must be registered with leaf::is_result_type");
        context_type_from_handlers<H...> ctx;
        auto active_context = activate_context(ctx);
        if( auto r = leaf_detail::try_catch_(
                ctx,
                [&]
                {
                    return std::forward<TryBlock>(try_block)();
                },
                std::forward<H>(h)...) )
            return r;
        else
        {
            error_id id = r.error();
            if( ctx.is_active() )
                ctx.deactivate();
            using R = typename std::decay<decltype(std::declval<TryBlock>()())>::type;
            auto rr = ctx.template handle_error<R>(std::move(id), std::forward<H>(h)..., [&r]()->R { return std::move(r); });
            if( !rr )
                ctx.propagate();
            return rr;
        }
    }

    template <class TryBlock, class... H>
    BOOST_LEAF_CONSTEXPR inline
    decltype(std::declval<TryBlock>()())
    try_catch( TryBlock && try_block, H && ... h )
    {
        context_type_from_handlers<H...> ctx;
        auto active_context = activate_context(ctx);
        return leaf_detail::try_catch_(
            ctx,
            [&]
            {
                return std::forward<TryBlock>(try_block)();
            },
            std::forward<H>(h)...);
    }

#endif

} }

// Boost Exception Integration

namespace boost { class exception; }
namespace boost { template <class Tag,class T> class error_info; }
namespace boost { namespace exception_detail { template <class ErrorInfo> struct get_info; } }

namespace boost { namespace leaf {

    namespace leaf_detail
    {
        template <class T>
        struct match_enum_type;

        template <class Tag, class T>
        struct match_enum_type<boost::error_info<Tag, T>>
        {
            using type = T;
        };

        template <class Ex>
        BOOST_LEAF_CONSTEXPR inline Ex * get_exception( error_info const & ei )
        {
            return dynamic_cast<Ex *>(ei.exception());
        }

        template <class, class T>
        struct dependent_type { using type = T; };

        template <class Dep, class T>
        using dependent_type_t = typename dependent_type<Dep, T>::type;

        template <class Tag, class T>
        struct handler_argument_traits<boost::error_info<Tag, T>>
        {
            using error_type = void;
            constexpr static bool always_available = false;

            template <class Tup>
            BOOST_LEAF_CONSTEXPR static T * check( Tup & tup, error_info const & ei ) noexcept
            {
                using boost_exception = dependent_type_t<T, boost::exception>;
                if( auto * be = get_exception<boost_exception>(ei) )
                    return exception_detail::get_info<boost::error_info<Tag, T>>::get(*be);
                else
                    return 0;
            }

            template <class Tup>
            BOOST_LEAF_CONSTEXPR static boost::error_info<Tag, T> get( Tup const & tup, error_info const & ei ) noexcept
            {
                return boost::error_info<Tag, T>(*check(tup, ei));
            }
        };

        template <class Tag, class T> struct handler_argument_traits<boost::error_info<Tag, T> const &>: handler_argument_traits_require_by_value<boost::error_info<Tag, T>> { };
        template <class Tag, class T> struct handler_argument_traits<boost::error_info<Tag, T> const *>: handler_argument_traits_require_by_value<boost::error_info<Tag, T>> { };
        template <class Tag, class T> struct handler_argument_traits<boost::error_info<Tag, T> &>: handler_argument_traits_require_by_value<boost::error_info<Tag, T>> { };
        template <class Tag, class T> struct handler_argument_traits<boost::error_info<Tag, T> *>: handler_argument_traits_require_by_value<boost::error_info<Tag, T>> { };
    }

} }

#endif
// <<< #include <boost/leaf/handle_errors.hpp>
#line 15 "../../include/boost/leaf/detail/all.hpp"
// >>> #include <boost/leaf/pred.hpp>
#line 1 "boost/leaf/pred.hpp"
#ifndef BOOST_LEAF_PRED_HPP_INCLUDED
#define BOOST_LEAF_PRED_HPP_INCLUDED

// Copyright (c) 2018-2020 Emil Dotchevski and Reverge Studios, Inc.

// Distributed under the Boost Software License, Version 1.0. (See accompanying
// file LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)

#ifndef BOOST_LEAF_ENABLE_WARNINGS
#   if defined(__clang__)
#       pragma clang system_header
#   elif (__GNUC__*100+__GNUC_MINOR__>301)
#       pragma GCC system_header
#   elif defined(_MSC_VER)
#       pragma warning(push,1)
#   endif
#endif


#if __cplusplus >= 201703L
#   define BOOST_LEAF_MATCH_ARGS(et,v1,v) auto v1, auto... v
#else
#   define BOOST_LEAF_MATCH_ARGS(et,v1,v) typename leaf_detail::et::type v1, typename leaf_detail::et::type... v
#endif
#define BOOST_LEAF_ESC(...) __VA_ARGS__

namespace boost { namespace leaf {

    namespace leaf_detail
    {
#if __cplusplus >= 201703L
        template <class MatchType, class T>
        BOOST_LEAF_CONSTEXPR BOOST_LEAF_ALWAYS_INLINE bool cmp_value_pack( MatchType const & e, bool (*P)(T) noexcept ) noexcept
        {
            BOOST_LEAF_ASSERT(P != 0);
            return P(e);
        }

        template <class MatchType, class T>
        BOOST_LEAF_CONSTEXPR BOOST_LEAF_ALWAYS_INLINE bool cmp_value_pack( MatchType const & e, bool (*P)(T) )
        {
            BOOST_LEAF_ASSERT(P != 0);
            return P(e);
        }
#endif

        template <class MatchType, class V>
        BOOST_LEAF_CONSTEXPR BOOST_LEAF_ALWAYS_INLINE bool cmp_value_pack( MatchType const & e, V v )
        {
            return e == v;
        }

        template <class MatchType, class VCar, class... VCdr>
        BOOST_LEAF_CONSTEXPR BOOST_LEAF_ALWAYS_INLINE bool cmp_value_pack( MatchType const & e, VCar car, VCdr ... cdr )
        {
            return cmp_value_pack(e, car) || cmp_value_pack(e, cdr...);
        }
    }

    ////////////////////////////////////////

    template <class E, class Enum = E>
    struct condition
    {
        static_assert(std::is_error_condition_enum<Enum>::value || std::is_error_code_enum<Enum>::value, "leaf::condition<E, Enum> requires Enum to be registered either with std::is_error_condition_enum or std::is_error_code_enum.");
    };

    template <class Enum>
    struct condition<Enum, Enum>
    {
        static_assert(std::is_error_condition_enum<Enum>::value || std::is_error_code_enum<Enum>::value, "leaf::condition<Enum> requires Enum to be registered either with std::is_error_condition_enum or std::is_error_code_enum.");
    };

#if __cplusplus >= 201703L
    template <class ErrorCodeEnum>
    BOOST_LEAF_CONSTEXPR inline bool category( std::error_code const & ec )
    {
        static_assert(std::is_error_code_enum<ErrorCodeEnum>::value, "leaf::category requires an error code enum");
        return &ec.category() == &std::error_code(ErrorCodeEnum{}).category();
    }
#endif

    ////////////////////////////////////////

    namespace leaf_detail
    {
        template <class T>
        struct match_enum_type
        {
            using type = T;
        };

        template <class Enum>
        struct match_enum_type<condition<Enum, Enum>>
        {
            using type = Enum;
        };

        template <class E, class Enum>
        struct match_enum_type<condition<E, Enum>>
        {
            static_assert(sizeof(Enum) == 0, "leaf::condition<E, Enum> should be used with leaf::match_value<>, not with leaf::match<>");
        };
    }

    template <class E, BOOST_LEAF_MATCH_ARGS(match_enum_type<E>, V1, V)>
    struct match
    {
        using error_type = E;
        E matched;

        template <class T>
        BOOST_LEAF_CONSTEXPR static bool evaluate(T && x)
        {
            return leaf_detail::cmp_value_pack(std::forward<T>(x), V1, V...);
        }
    };

    template <class Enum, BOOST_LEAF_MATCH_ARGS(BOOST_LEAF_ESC(match_enum_type<condition<Enum, Enum>>), V1, V)>
    struct match<condition<Enum, Enum>, V1, V...>
    {
        using error_type = std::error_code;
        std::error_code const & matched;

        BOOST_LEAF_CONSTEXPR static bool evaluate(std::error_code const & e) noexcept
        {
            return leaf_detail::cmp_value_pack(e, V1, V...);
        }
    };

    template <class E, BOOST_LEAF_MATCH_ARGS(match_enum_type<E>, V1, V)>
    struct is_predicate<match<E, V1, V...>>: std::true_type
    {
    };

    ////////////////////////////////////////

    namespace leaf_detail
    {
        template <class E>
        struct match_value_enum_type
        {
            using type = typename std::remove_reference<decltype(std::declval<E>().value)>::type;
        };

        template <class E, class Enum>
        struct match_value_enum_type<condition<E, Enum>>
        {
            using type = Enum;
        };

        template <class Enum>
        struct match_value_enum_type<condition<Enum, Enum>>
        {
            static_assert(sizeof(Enum)==0, "leaf::condition<Enum> should be used with leaf::match<>, not with leaf::match_value<>");
        };
    }

    template <class E, BOOST_LEAF_MATCH_ARGS(match_value_enum_type<E>, V1, V)>
    struct match_value
    {
        using error_type = E;
        E const & matched;

        BOOST_LEAF_CONSTEXPR static bool evaluate(E const & e) noexcept
        {
            return leaf_detail::cmp_value_pack(e.value, V1, V...);
        }
    };

    template <class E, class Enum, BOOST_LEAF_MATCH_ARGS(BOOST_LEAF_ESC(match_value_enum_type<condition<E, Enum>>), V1, V)>
    struct match_value<condition<E, Enum>, V1, V...>
    {
        using error_type = E;
        E const & matched;

        BOOST_LEAF_CONSTEXPR static bool evaluate(E const & e)
        {
            return leaf_detail::cmp_value_pack(e.value, V1, V...);
        }
    };

    template <class E, BOOST_LEAF_MATCH_ARGS(match_value_enum_type<E>, V1, V)>
    struct is_predicate<match_value<E, V1, V...>>: std::true_type
    {
    };

    ////////////////////////////////////////

#if __cplusplus >= 201703L
    template <auto, auto, auto...>
    struct match_member;

    template <class T, class E, T E::* P, auto V1, auto... V>
    struct match_member<P, V1, V...>
    {
        using error_type = E;
        E const & matched;

        BOOST_LEAF_CONSTEXPR static bool evaluate(E const & e) noexcept
        {
            return leaf_detail::cmp_value_pack(e.*P, V1, V...);
        }
    };

    template <auto P, auto V1, auto... V>
    struct is_predicate<match_member<P, V1, V...>>: std::true_type
    {
    };
#endif

    ////////////////////////////////////////

    template <class P>
    struct if_not
    {
        using error_type = typename P::error_type;;
        decltype(std::declval<P>().matched) matched;

        template <class E>
        BOOST_LEAF_CONSTEXPR static bool evaluate(E && e) noexcept
        {
            return !P::evaluate(std::forward<E>(e));
        }
    };

    template <class P>
    struct is_predicate<if_not<P>>: std::true_type
    {
    };

    ////////////////////////////////////////


#ifndef BOOST_LEAF_NO_EXCEPTIONS

    namespace leaf_detail
    {
        template <class Ex>
        BOOST_LEAF_CONSTEXPR inline bool check_exception_pack( std::exception const & ex, Ex const * ) noexcept
        {
            return dynamic_cast<Ex const *>(&ex)!=0;
        }

        template <class Ex, class... ExRest>
        BOOST_LEAF_CONSTEXPR inline bool check_exception_pack( std::exception const & ex, Ex const *, ExRest const * ... ex_rest ) noexcept
        {
            return dynamic_cast<Ex const *>(&ex)!=0 || check_exception_pack(ex, ex_rest...);
        }

        BOOST_LEAF_CONSTEXPR inline bool check_exception_pack( std::exception const & ) noexcept
        {
            return true;
        }
    }

    template <class... Ex>
    struct catch_
    {
        using error_type = void;
        std::exception const & matched;

        BOOST_LEAF_CONSTEXPR static bool evaluate(std::exception const & ex) noexcept
        {
            return leaf_detail::check_exception_pack(ex, static_cast<Ex const *>(0)...);
        }
    };

    template <class Ex>
    struct catch_<Ex>
    {
        using error_type = void;
        Ex const & matched;

        BOOST_LEAF_CONSTEXPR static Ex const * evaluate(std::exception const & ex) noexcept
        {
            return dynamic_cast<Ex const *>(&ex);
        }

        explicit catch_( std::exception const & ex ):
            matched(*dynamic_cast<Ex const *>(&ex))
        {
        }
    };

    template <class... Ex>
    struct is_predicate<catch_<Ex...>>: std::true_type
    {
    };

#endif

} }

#endif
// <<< #include <boost/leaf/pred.hpp>
#line 17 "../../include/boost/leaf/detail/all.hpp"
// >>> #include <boost/leaf/result.hpp>
#line 1 "boost/leaf/result.hpp"
#ifndef BOOST_LEAF_RESULT_HPP_INCLUDED
#define BOOST_LEAF_RESULT_HPP_INCLUDED

// Copyright (c) 2018-2020 Emil Dotchevski and Reverge Studios, Inc.

// Distributed under the Boost Software License, Version 1.0. (See accompanying
// file LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)

#ifndef BOOST_LEAF_ENABLE_WARNINGS
#   if defined(__clang__)
#       pragma clang system_header
#   elif (__GNUC__*100+__GNUC_MINOR__>301)
#       pragma GCC system_header
#   elif defined(_MSC_VER)
#       pragma warning(push,1)
#   endif
#endif

#include <climits>

namespace boost { namespace leaf {

    class bad_result:
        public std::exception,
        public error_id
    {
        char const * what() const noexcept final override
        {
            return "boost::leaf::bad_result";
        }

    public:

        explicit bad_result( error_id id ) noexcept:
            error_id(id)
        {
            BOOST_LEAF_ASSERT(value());
        }
    };

    ////////////////////////////////////////

    namespace leaf_detail
    {
        template <class T>
        struct stored
        {
            using type = T;
            using value_type = T;
            using value_type_const = T const;
            using value_cref = T const &;
            using value_ref = T &;
            using value_rv_cref = T const &&;
            using value_rv_ref = T &&;
        };

        template <class T>
        struct stored<T &>
        {
            using type = std::reference_wrapper<T>;
            using value_type_const = T;
            using value_type = T;
            using value_ref = T &;
            using value_cref = T &;
            using value_rv_ref = T &;
            using value_rv_cref = T &;
        };

        class result_discriminant
        {
            unsigned state_;

        public:

            enum kind_t
            {
                no_error = 0,
                err_id = 1,
                ctx_ptr = 2,
                val = 3
            };

            explicit result_discriminant( error_id id ) noexcept:
                state_(id.value())
            {
                BOOST_LEAF_ASSERT(state_==0 || (state_&3)==1);
            }

            struct kind_val { };
            explicit result_discriminant( kind_val ) noexcept:
                state_(val)
            {
            }

            struct kind_ctx_ptr { };
            explicit result_discriminant( kind_ctx_ptr ) noexcept:
                state_(ctx_ptr)
            {
            }

            kind_t kind() const noexcept
            {
                return kind_t(state_&3);
            }

            error_id get_error_id() const noexcept
            {
                BOOST_LEAF_ASSERT(kind()==no_error || kind()==err_id);
                return make_error_id(state_);
            }
        };
    }

    ////////////////////////////////////////

    template <class T>
    class result
    {
        template <class U>
        friend class result;

        using result_discriminant = leaf_detail::result_discriminant;

        struct error_result
        {
            error_result( error_result && ) = default;
            error_result( error_result const & ) = delete;
            error_result & operator=( error_result const & ) = delete;

            result & r_;

            error_result( result & r ) noexcept:
                r_(r)
            {
            }

            template <class U>
            operator result<U>() noexcept
            {
                switch(r_.what_.kind())
                {
                case result_discriminant::val:
                    return result<U>(error_id());
                case result_discriminant::ctx_ptr:
                    return result<U>(std::move(r_.ctx_));
                default:
                    return result<U>(std::move(r_.what_));
                }
            }

            operator error_id() noexcept
            {
                switch(r_.what_.kind())
                {
                case result_discriminant::val:
                    return error_id();
                case result_discriminant::ctx_ptr:
                {
                    error_id captured_id = r_.ctx_->propagate_captured_errors();
                    leaf_detail::id_factory<>::current_id = captured_id.value();
                    return captured_id;
                }
                default:
                    return r_.what_.get_error_id();
                }
            }
        };

        using stored_type = typename leaf_detail::stored<T>::type;
        using value_type = typename leaf_detail::stored<T>::value_type;
        using value_type_const = typename leaf_detail::stored<T>::value_type_const;
        using value_ref = typename leaf_detail::stored<T>::value_ref;
        using value_cref = typename leaf_detail::stored<T>::value_cref;
        using value_rv_ref = typename leaf_detail::stored<T>::value_rv_ref;
        using value_rv_cref = typename leaf_detail::stored<T>::value_rv_cref;

        union
        {
            stored_type stored_;
            context_ptr ctx_;
        };

        result_discriminant what_;

        void destroy() const noexcept
        {
            switch(this->what_.kind())
            {
            case result_discriminant::val:
                stored_.~stored_type();
                break;
            case result_discriminant::ctx_ptr:
                BOOST_LEAF_ASSERT(!ctx_ || ctx_->captured_id_);
                ctx_.~context_ptr();
            default:
                break;
            }
        }

        template <class U>
        result_discriminant move_from( result<U> && x ) noexcept
        {
            auto x_what = x.what_;
            switch(x_what.kind())
            {
            case result_discriminant::val:
                (void) new(&stored_) stored_type(std::move(x.stored_));
                break;
            case result_discriminant::ctx_ptr:
                BOOST_LEAF_ASSERT(!x.ctx_ || x.ctx_->captured_id_);
                (void) new(&ctx_) context_ptr(std::move(x.ctx_));
            default:
                break;
            }
            return x_what;
        }

        result( result_discriminant && what ) noexcept:
            what_(std::move(what))
        {
            BOOST_LEAF_ASSERT(what_.kind()==result_discriminant::err_id || what_.kind()==result_discriminant::no_error);
        }

        error_id get_error_id() const noexcept
        {
            BOOST_LEAF_ASSERT(what_.kind()!=result_discriminant::val);
            return what_.kind()==result_discriminant::ctx_ptr ? ctx_->captured_id_ : what_.get_error_id();
        }

        static int init_T_with_U( T && );

    protected:

        void enforce_value_state() const
        {
            if( what_.kind() != result_discriminant::val )
                ::boost::leaf::throw_exception(bad_result(get_error_id()));
        }

    public:

        result( result && x ) noexcept:
            what_(move_from(std::move(x)))
        {
        }

        template <class U>
        result( result<U> && x ) noexcept:
            what_(move_from(std::move(x)))

        {
        }

        result():
            stored_(stored_type()),
            what_(result_discriminant::kind_val{})
        {
        }

        result( value_type && v ) noexcept:
            stored_(std::forward<value_type>(v)),
            what_(result_discriminant::kind_val{})
        {
        }

        result( value_type const & v ):
            stored_(v),
            what_(result_discriminant::kind_val{})
        {
        }

        result( error_id err ) noexcept:
            what_(err)
        {
        }

        // SFINAE: T can be initialized with a U, e.g. result<std::string>("literal").
        // Not using is_constructible on purpose, bug with COMPILER=/usr/bin/clang++ CXXSTD=11 clang 3.3.
        template <class U>
        result( U && u, decltype(init_T_with_U(std::forward<U>(u))) * = 0 ):
            stored_(std::forward<U>(u)),
            what_(result_discriminant::kind_val{})
        {
        }

        result( std::error_code const & ec ) noexcept:
            what_(error_id(ec))
        {
        }

        template <class Enum>
        result( Enum e, typename std::enable_if<std::is_error_code_enum<Enum>::value, int>::type * = 0 ) noexcept:
            what_(error_id(e))
        {
        }

        result( context_ptr && ctx ) noexcept:
            ctx_(std::move(ctx)),
            what_(result_discriminant::kind_ctx_ptr{})
        {
        }

        ~result() noexcept
        {
            destroy();
        }

        result & operator=( result && x ) noexcept
        {
            destroy();
            what_ = move_from(std::move(x));
            return *this;
        }

        template <class U>
        result & operator=( result<U> && x ) noexcept
        {
            destroy();
            what_ = move_from(std::move(x));
            return *this;
        }

        explicit operator bool() const noexcept
        {
            return what_.kind() == result_discriminant::val;
        }

        value_cref value() const &
        {
            enforce_value_state();
            return stored_;
        }

        value_ref value() &
        {
            enforce_value_state();
            return stored_;
        }

        value_rv_cref value() const &&
        {
            enforce_value_state();
            return std::move(stored_);
        }

        value_rv_ref value() &&
        {
            enforce_value_state();
            return std::move(stored_);
        }

        value_cref operator*() const &
        {
            return value();
        }

        value_ref operator*() &
        {
            return value();
        }

        value_rv_cref operator*() const &&
        {
            return value();
        }

        value_rv_ref operator*() &&
        {
            return value();
        }

        value_type_const * operator->() const
        {
            return &value();
        }

        value_type * operator->()
        {
            return &value();
        }

        error_result error() noexcept
        {
            return error_result{*this};
        }

        template <class... Item>
        error_id load( Item && ... item ) noexcept
        {
            return error_id(error()).load(std::forward<Item>(item)...);
        }
    };

    ////////////////////////////////////////

    namespace leaf_detail
    {
        struct void_ { };
    }

    template <>
    class result<void>:
        result<leaf_detail::void_>
    {
        using result_discriminant = leaf_detail::result_discriminant;
        using void_ = leaf_detail::void_;
        using base = result<void_>;

        template <class U>
        friend class result;

        result( result_discriminant && what ) noexcept:
            base(std::move(what))
        {
        }

    public:

        using value_type = void;

        result( result && x ) noexcept:
            base(std::move(x))
        {
        }

        result() noexcept
        {
        }

        result( error_id err ) noexcept:
            base(err)
        {
        }

        result( std::error_code const & ec ) noexcept:
            base(ec)
        {
        }

        template <class Enum>
        result( Enum e, typename std::enable_if<std::is_error_code_enum<Enum>::value, Enum>::type * = 0 ) noexcept:
            base(e)
        {
        }

        result( context_ptr && ctx ) noexcept:
            base(std::move(ctx))
        {
        }

        ~result() noexcept
        {
        }

        void value() const
        {
            base::enforce_value_state();
        }

        using base::operator=;
        using base::operator bool;
        using base::get_error_id;
        using base::error;
        using base::load;
    };

    ////////////////////////////////////////

    template <class R>
    struct is_result_type;

    template <class T>
    struct is_result_type<result<T>>: std::true_type
    {
    };

} }

#endif
// <<< #include <boost/leaf/result.hpp>
#line 18 "../../include/boost/leaf/detail/all.hpp"

#endif
