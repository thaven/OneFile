/*
 * Copyright 2017-2019
 *   Andreia Correia <andreia.veiga@unine.ch>
 *   Pedro Ramalhete <pramalhe@gmail.com>
 *   Pascal Felber <pascal.felber@unine.ch>
 *   Nachshon Cohen <nachshonc@gmail.com>
 *
 * Modified for D by Harry T. Vennik.
 *
 * Copyright 2019
 *   Harry T. Vennik <htvennik@gmail.com>
 *
 * This work is published under the MIT license. See LICENSE.txt
 */
module onefile.thread_registry;

align(128)
struct ThreadRegistry
{
private:
    import core.atomic : atomicLoad, casByRef, MemoryOrder;
    import onefile.internal.bitarray : AtomicBitArray;

    shared static ThreadRegistry g_instance;
    package static short s_tid = -1;

    // Bit array indicating which TIDs are in use by threads
    AtomicBitArray _usedTID;

    // Highest TID (+1) in use by threads
    short _maxTid = -1;

public @nogc:

    static instance()
    {
        return &g_instance;
    }

    @disable this();
    @disable this() shared;

    void initialize(ushort maxThreads) shared
    in (-1 == _maxTid)
    in (maxThreads < (1 << 10)) // cannot support more because of TxId format
    {
        // We can quite safely cast away shared here because no threads
        // are in the registry yet.
        () @trusted {
            return cast(AtomicBitArray*) &_usedTID;
        } ().length = maxThreads;

        registerThreadNew();
    }

    @property
    bool isInitialized() shared
    {
        return 0 != _usedTID.length;
    }

    // Progress condition: wait-free bounded (by the number of threads)
    short registerThreadNew() shared
    in (s_tid == -1)
    {
        auto l = _usedTID.length;

        for (short tid = 0; tid < l; ++tid)
        {
            if (!_usedTID.setIfClear(tid))
                continue;

            short curMax = _maxTid.atomicLoad();
            while (curMax <= tid)
            {
                _maxTid.casByRef(curMax, cast(short) (tid+1));
                curMax = _maxTid.atomicLoad();
            }

            s_tid = tid;
            return tid;
        }

        throw new ThreadRegistryException(
            0 == l ? "Thread registry not initialized" : "Too many threads");
    }

    // Progress condition: wait-free population oblivious
    nothrow
    private void deregisterThread(in short tid) shared
    {
        _usedTID[tid] = false;
    }

    // Progress condition: wait-free population oblivious
    nothrow
    @property
    static short maxTID()
    {
        auto lmaxTid = g_instance._maxTid.atomicLoad!(MemoryOrder.acq);
        return (lmaxTid > 0) ? lmaxTid : 0;
    }

    nothrow
    @property
    @safe
    static ushort maxThreads()
    {
        return cast(ushort) g_instance._usedTID.length;
    }

    // Progress condition: wait-free bounded (by the number of threads)
    @trusted
    static short getTID()
    {
        auto tid = g_instance.s_tid;
        return (tid >= 0) ? tid : g_instance.registerThreadNew();
    }

    static void deregisterMe()
    {
        g_instance.deregisterThread(getTID());
        s_tid = -1;
    }

    // Progress condition: wait-free bounded (by the number of threads)
    @safe
    static bool isMe(in short tid)
    {
        return tid == g_instance.s_tid;
    }
}

class ThreadRegistryException : Exception
{
    import std.exception : basicExceptionCtors;

    ///
    mixin basicExceptionCtors;
}

