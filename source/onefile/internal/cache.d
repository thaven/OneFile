/*
 * Copyright 2019
 *   Harry T. Vennik <htvennik@gmail.com>
 *
 * This work is published under the MIT license. See LICENSE.txt
 */
module onefile.internal.cache;

template CacheAligned(T)
{
    enum cacheAlignment = 64;

    static if (T.alignof >= cacheAlignment)
        alias CacheAligned = T;
    else
    {
        align(cacheAlignment)
        struct CacheAligned
        {
            private T _value;
            alias value this;

            this(V)(V value)
            {
                _value = value;
            }

            @property
            ref value() inout return
            {
                return _value;
            }
        }
    }
}
