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
module onefile.hazard_eras;

class HazardErasOF
{
private:
    import core.atomic : atomicLoad, atomicStore, MemoryOrder;
    import std.container.array : Array;

    import onefile.internal.cache : CacheAligned;
    import onefile.stm : Request, TMStruct, TxId;
    import onefile.thread_registry : ThreadRegistry;

    enum ulong noEra = 0;
    enum int   thresholdR = 0;

    immutable uint maxThreads;
    CacheAligned!(shared ulong)[] he;
    Array!(CacheAligned!RListEntry)[] retiredList;
    Array!(CacheAligned!Request)[] retiredListTx;

    @nogc:

    public this(uint maxThreads)
    {
        import onefile.internal.allocator : allocator, makeArray;

        this.maxThreads = maxThreads;
        he = allocator.makeArray!(CacheAligned!(shared ulong))(maxThreads);
        retiredList = allocator.makeArray!(
            Array!(CacheAligned!RListEntry))(maxThreads);
        retiredListTx = allocator.makeArray!(
            Array!(CacheAligned!Request))(maxThreads);
    }

    ~this()
    {
        import onefile.internal.allocator : allocator, dispose;

        allocator.dispose(cast(CacheAligned!ulong[]) he);
        allocator.dispose(cast(Array!(CacheAligned!RListEntry)[]) retiredList);
        allocator.dispose(cast(Array!(CacheAligned!Request)[]) retiredListTx);
    }

    // Progress condition: wait-free bounded (by the number of threads)
    bool canDelete(ulong curEra, in ref TMStruct del)
    {
        // We can't delete objects from the current transaction
        if (del._delEra == curEra)
            return false;

        for (uint it = 0; it < ThreadRegistry.maxTID; ++it)
        {
            const era = he[it].value.atomicLoad!(MemoryOrder.acq);
            if (era == noEra || era < del._newEra || era > del._delEra)
                continue;

            return false;
        }

        return true;
    }

package:
    // Progress condition: wait-free population oblivious
    void clear(in short tid)
    in (ThreadRegistry.isMe(tid))
    {
        he[tid].value.atomicStore!(MemoryOrder.rel)(noEra);
    }

    // Progress condition: wait-free population oblivious
    void set(TxId trans, in short tid)
    in (ThreadRegistry.isMe(tid))
    {
        he[tid].value.atomicStore(trans.seq);
    }

    // Progress condition: wait-free population oblivious
    void addToRetiredList(RListEntry newdel, in short tid)
    in (ThreadRegistry.isMe(tid))
    {
        retiredList[tid].insertBack(CacheAligned!RListEntry(newdel));
    }

    // Progress condition: wait-free population oblivious
    void addToRetiredListTx(Request tx, in short tid)
    in (ThreadRegistry.isMe(tid))
    {
        retiredListTx[tid].insertBack(CacheAligned!Request(tx));
    }

    /**
     * Progress condition: bounded wait-free
     *
     * Attemps to delete the no-longer-in-use objects in the retired list.
     * We need to pass the currEra coming from the seq of the currTx so that
     * the objects from the current transaction don't get deleted.
     */
    void clean(ulong curEra, in short tid)
    in (ThreadRegistry.isMe(tid))
    {
        import onefile.internal.allocator : allocator, disposeNoGc;
        import std.algorithm.mutation : move;

        debug(PRINTF)
        {
            import core.stdc.stdio : printf;
            int n;
        }

        auto myRL = retiredList[tid];

        if (myRL.length < thresholdR)
            return;

        for (size_t iret = 0; iret < myRL.length;)
        {
            RListEntry del = myRL[iret];
            if (canDelete(curEra, del.tmStruct))
            {
                move(myRL[$ - 1], myRL[iret]);
                myRL.removeBack(1);
                // No need to call destructor because it was executed
                // as part of the transaction

                debug(PRINTF) ++n;
                allocator.deallocate(del.chunk);
                continue;
            }
            iret++;
        }

        debug(PRINTF)
        {
            printf("HE Deallocated %d objects\n", n);
            n = 0;
        }

        auto myRLTx = retiredListTx[tid];

        for (size_t iret = 0; iret < myRLTx.length;)
        {
            Request tx = myRLTx[iret];

            if (canDelete(curEra, tx._tm))
            {
                myRLTx[iret] = myRLTx[$ - 1];
                myRLTx.removeBack(1);
                allocator.disposeNoGc(tx);
                debug(PRINTF) ++n;
                continue;
            }
            iret++;
        }

        debug(PRINTF) printf("HE Deallocated %d requests\n", n);
    }
}

struct RListEntry
{
private:
    import onefile.internal.allocator : allocator, dispose, make;
    import onefile.stm : isTM, TMObject, TMStruct;
    import std.traits : Unqual;

    static struct Chunk
    {
        void[] chunk;
    }

    void* _obj;
    TypeInfo _ti;

@nogc nothrow:
package:

    pure
    this(T)(T* obj)
    if (isTM!T)
    {
        _obj = cast(void*) obj;
        _ti = typeid(T);
    }

    pure
    this(T)(T obj)
    if (is(Unqual!T : TMObject))
    {
        _obj = cast(void*) obj;
        _ti = obj.classinfo;
    }

    this(void[] chunk)
    {
        _obj = allocator.make!Chunk(chunk);
        _ti = typeid(Chunk);
    }

public:

    ~this()
    {
        if (_ti is typeid(Chunk))
            allocator.dispose(cast(Chunk*) _obj);
    }

pure:

    @property
    size_t allocSize()
    {
        if (auto tiCls = cast(TypeInfo_Class)_ti)
            return tiCls.m_init.length;
        else if (_ti is typeid(Chunk))
            return (cast(Chunk*)_obj).chunk.length;
        else
            return _ti.tsize;
    }

    @property
    void[] chunk()
    {
        if (_ti is typeid(Chunk))
            return (cast(Chunk*)_obj).chunk;
        else
            return _obj[0 .. allocSize];
    }

    @property
    ref TMStruct tmStruct()
    {
        if (_ti is typeid(Chunk))
            return *(cast(TMStruct*) (cast(Chunk*)_obj).chunk.ptr);
        else if (auto tmObj = cast(TMObject)_obj)
            return tmObj._tm;
        else
            return *(cast(TMStruct*)_obj);
    }
}


