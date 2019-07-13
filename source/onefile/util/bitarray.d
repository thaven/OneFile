/*
 * Copyright 2019
 *   Harry T. Vennik <htvennik@gmail.com>
 *
 * This work is published under the MIT license. See LICENSE.txt
 */
module onefile.util.bitarray;

import core.atomic;
import onefile.util.allocator;

struct AtomicBitArray
{
    private uint[] _arr;

@nogc nothrow @safe:

    this(size_t length) shared
    {
        _arr = allocator.makeArray!(shared uint)((length + 31) / 32);
    }

    @property
    @system
    void length(size_t value)
    {
        import core.exception : onOutOfMemoryError;

        auto newLength = (value + 31) / 32;

        if (newLength > _arr.length)
        {
            if (null is _arr)
                _arr = allocator.makeArray!uint(newLength);
            else if (!allocator.expandArray(_arr, newLength - _arr.length))
                _arr = null;

            if (null is _arr)
                onOutOfMemoryError();
        }
        else
        {
            if (!allocator.shrinkArray(_arr, _arr.length - newLength))
                _arr = _arr[0 .. newLength];
        }
    }

pure:
    @property
    size_t length() const shared
    {
        return _arr.length / 4;
    }

    bool opIndex(in size_t idx) const shared
    {
        immutable arrIdx = idx / 32;
        immutable shift = idx & 31;
        return 0 != ((1 << shift) & _arr[arrIdx].atomicLoad);
    }

    void opIndexAssign(in bool value, in size_t idx) shared
    {
        immutable arrIdx = idx / 32;
        immutable shift = idx & 31;
        immutable mask = ~(1U << shift);
        immutable shiftedValue = (cast(uint) value) << shift;

        do
        {
            immutable arrValue = _arr[arrIdx].atomicLoad;
            immutable appliedValue = (arrValue & mask) | shiftedValue;

            if (arrValue == appliedValue
                    || _arr[arrIdx].casByRef(arrValue, appliedValue))
                return;
        }
        while (true);
    }

    bool setIfClear(in size_t idx) shared
    {
        immutable arrIdx = idx / 32;
        immutable shiftedValue = 1U << (idx & 31);

        do
        {
            immutable arrValue = _arr[arrIdx].atomicLoad;

            if (arrValue & shiftedValue)
                return false;

            if (_arr[arrIdx].casByRef(arrValue, arrValue | shiftedValue))
                return true;
        }
        while(true);
    }
}
