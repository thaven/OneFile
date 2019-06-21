/*
 * Copyright 2017-2019
 *   Andreia Correia <andreia.veiga@unine.ch>
 *   Pedro Ramalhete <pramalhe@gmail.com>
 *   Pascal Felber <pascal.felber@unine.ch>
 *   Nachshon Cohen <nachshonc@gmail.com>
 *
 * Translated from C++ to D by Harry T. Vennik <htvennik@gmail.com>
 *
 * This work is published under the MIT license. See LICENSE.txt
 */

module onefile.stm.wf;

import onefile.util.allocator;
import onefile.util.bitarray;

import core.atomic;
import std.traits : Fields, isScalarType, ReturnType;

debug import core.stdc.stdio : printf;

struct Config
{
    ushort registryMaxThreads = 128;
    ulong txMaxStores = 40*1024;
    ulong hashBuckets = 1024;
    ulong txMaxAllocs = 10*1024;
    ulong txMaxRetires = 10*1024;
}

struct TxId
{
    private ulong _raw;

    @nogc nothrow pure @safe:

    this(ulong seq, ushort idx)
    {
        _raw = (seq << 10) | idx;
    }

    @property
    ulong seq() const
    {
        return _raw >> 10;
    }

    @property
    ushort idx() const
    {
        return cast(ushort) (_raw & 0x3ff); // 10 bits
    }
}

align(128)
struct ThreadRegistry
{
private:
    shared static ThreadRegistry g_instance;
    static short s_tid = -1;

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
    void deregisterThread(in short tid) shared
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
    static ushort maxThreads()
    {
        return cast(ushort) g_instance._usedTID.length;
    }

    // Progress condition: wait-free bounded (by the number of threads)
    static short getTID()
    {
        auto tid = g_instance.s_tid;
        return (tid > 0) ? tid : g_instance.registerThreadNew();
    }

    // Progress condition: wait-free bounded (by the number of threads)
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

struct TMStruct
{
private:
    ulong _newEra;
    ulong _delEra;
}

template isTM(T)
if (is(T == struct))
{
    enum isTM = is(T == TMStruct) || (.isTM!(Fields!T[0]) && 0 == () {
        T t;
        return t.tupleof[0].offsetof;
    } ());
}

template isTM(T)
if (!is(T == struct))
{
    enum isTM = false;
}

struct TransFunc
{
    TMStruct _tm;
    ulong delegate() func;
}

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
            alias _value this;

            this(T)(T value)
            {
                _value = value;
            }

            @property
            ref value() return
            {
                return _value;
            }
        }
    }
}

private class HazardErasOF
{
private:
    import std.container.array : Array;

    enum ulong noEra = 0;
    enum int   thresholdR = 0;

    immutable uint maxThreads;
    CacheAligned!(shared ulong)[] he;
    Array!(CacheAligned!(TMStruct*))[] retiredList;
    Array!(CacheAligned!(TransFunc*))[] retiredListTx;

    public this(uint maxThreads)
    {
        this.maxThreads = maxThreads;
        he = allocator.makeArray!(CacheAligned!(shared ulong))(maxThreads);
        retiredList = allocator.makeArray!(
            Array!(CacheAligned!(TMStruct*)))(maxThreads);
        retiredListTx = allocator.makeArray!(
            Array!(CacheAligned!(TransFunc*)))(maxThreads);
    }

    ~this()
    {
        allocator.dispose(cast(CacheAligned!ulong[]) he);
        allocator.dispose(cast(Array!(CacheAligned!(TMStruct*))[]) retiredList);
        allocator.dispose(cast(Array!(CacheAligned!(TransFunc*))[]) retiredListTx);
    }

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
    void addToRetiredList(TMStruct* newdel, in short tid)
    in (ThreadRegistry.isMe(tid))
    {
        retiredList[tid].insertBack(CacheAligned!(TMStruct*)(newdel));
    }

    // Progress condition: wait-free population oblivious
    void addToRetiredListTx(TransFunc* tx, in short tid)
    in (ThreadRegistry.isMe(tid))
    {
        retiredListTx[tid].insertBack(CacheAligned!(TransFunc*)(tx));
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
        auto myRL = retiredList[tid];

        if (myRL.length < thresholdR)
            return;

        for (size_t iret = 0; iret < myRL.length;)
        {
            TMStruct* del = myRL[iret];
            if (canDelete(curEra, del))
            {
                myRL[iret] = myRL[$ - 1];
                myRL.removeBack();
                // No need to call destructor because it was executed
                // as part of the transaction
                allocator.deallocate(del.toChunk);
                continue;
            }
            iret++;
        }

        auto myRLTx = retiredListTx[tid];

        for (size_t iret = 0; iret < myRLTx.length;)
        {
            TransFunc* tx = myRLTx[iret];
            if (canDelete(curEra, tx))
            {
                myRLTx[iret] = myRLTx[$ - 1];
                myRLTx.removeBack();
                allocator.dispose(tx);
                continue;
            }
            iret++;
        }
    }

    bool canDelete(T)(ulong curEra, T* del)
    if (!is(T == TMStruct) && isTM!T)
    {
        return canDelete(curEra, cast(TMStruct*)del);
    }

    // Progress condition: wait-free bounded (by the number of threads)
    bool canDelete(ulong curEra, TMStruct* del)
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
}

align(64)
class OneFileWF(Config config = Config.init)
{
private:
    // Its purpose is to hold thread-local data
    static struct OpData
    {
        private static OpData* tl_current;

        @property
        static OpData* current()
        {
            return tl_current;
        }

        @property
        static void current(OpData* value)
        {
            tl_current = value;
        }

        // Used during a transaction to keep the value of currTx read in
        // beginTx() (owner thread only)
        TxId curTx;

        // Can be moved to CLOSED by other threads, using a CAS
        shared(TxId) request;

        // Thread-local: Number of nested transactions
        ulong nestedTrans;

        // Number of calls to retire() in this transaction (owner thread only)
        ulong numRetires;

        // List of retired objects during the transaction (owner thread only)
        TMStruct*[config.txMaxRetires] rlog;

        // Number of calls to tmNew() in this transaction (owner thread only)
        ulong numAllocs;

        // List of newly allocated objects during the transaction
        // (owner thread only)
        Deletable[config.txMaxAllocs] alog;
    }

    // T is typically a pointer to a node, but it can be integers or other
    // stuff, as long as it fits in 64 bits
    align(16)
    static shared struct TMType(T)
    if (T.sizeof <= 8)
    {
        // Stores the actual value as an atomic
        ulong val;

        // Tx sequence number
        ulong seq = 1;

        // This is important for DCAS
        static assert(seq.offsetof == val.offsetof + val.sizeof);

        this(T initVal)
        {
            isolated_store(initVal);
        }

        // Copy constructor
        this(TMType other)
        {
            pstore(other.pload);
        }

        this(ulong val, ulong seq)
        {
            this.val = val;
            this.seq = seq;
        }

//        @disable this(this);

        // Assignment operator from a TMType
        void opAssign(TMType other) {
            pstore(other.pload());
        }

        // Assignment operator from a value
        void opAssign(T value) {
            pstore(value);
        }

        // Meant to be called when know we're the only ones touching
        // these contents, for example, in the constructor of an object,
        // before making the object visible to other threads.
        void isolated_store(T newVal) {
            val.atomicStore!(MemoryOrder.raw)(cast(ulong)newVal);
        }

        // Used only internally by updateTx() to determine if the request is
        // opened or not
        private ulong getSeq() const
        {
            return seq.atomicLoad!(MemoryOrder.acq);
        }

        // Used only internally by updateTx()
        private void rawStore(ref T newVal, ulong lseq)
        {
            val.atomicStore!(MemoryOrder.raw)(cast(ulong)newVal);
            seq.atomicStore!(MemoryOrder.rel)(lseq);
        }

        T pload() const shared
        {
            // We have to check if there is a new ongoing transaction and if
            // so, abort this execution immediately for two reasons:
            // 1. Memory Reclamation: the val we're returning may be a pointer
            //    to an object that has since been retired and deleted,
            //    therefore we can't allow user code to de-reference it;
            // 2. Invariant Conservation: The val we're reading may be from a
            //    newer transaction, which implies that it may break an
            //    invariant in the user code.
            //
            // See examples of invariant breaking in this post:
            // http://concurrencyfreaks.com/2013/11/stampedlocktryoptimisticread-and.html

            T lval = cast(T) val.atomicLoad!(MemoryOrder.acq);
            const myOpData = OpData.current;

            if (null is myOpData)
                return lval;

            auto lseq = seq.atomicLoad!(MemoryOrder.acq);

            if (lseq > myOpData.curTx.seq)
                throw new AbortedTx("Transaction aborted.");

            if (tl_isReadOnly)
                return lval;

            return cast(T) OneFileWF.g_instance
                    .writeSets[ThreadRegistry.s_tid]
                    .lookupAddr(&this, cast(ulong)lval);
        }

        alias pload this;

        private bool rawLoad(ref T keepVal, ref ulong keepSeq) const shared
        {
            // This method is meant to be used by the internal consensus
            // mechanism, not by the user.
            //
            // Returns true if the 'val' and 'seq' placed in 'keepVal' and
            // 'keepSeq' are consistent, i.e. linearizabile. We need to use
            // acquire-loads to keep order and re-check the 'seq' to make sure
            // it corresponds to the 'val' we're returning.

            keepSeq = seq.atomicLoad!(MemoryOrder.acq);
            keepVal = cast(T) val.atomicLoad!(MemoryOrder.acq);
            return (keepSeq == seq.atomicLoad!(MemoryOrder.acq));
        }

        void pstore(T newVal) shared
        {
            // We don't need to check currTx here because we're not
            // de-referencing the val. It's only after a load() that the val
            // may be de-referenced (in user code), therefore we do the check
            // on load() only.

            if (null is OpData.current)
            {
                // Looks like we're outside a transaction
                val.atomicStore!(MemoryOrder.raw)(cast(ulong)newVal);
            }
            else
            {
                OneFileWF.g_instance
                    .writeSets[ThreadRegistry.s_tid]
                    .addOrReplace(&this, cast(ulong)newVal);
            }
        }
    }

    /// A single entry in the write-set
    static struct WriteSetEntry
    {
        /// Address of value+sequence to change
        shared(TMType!ulong)* addr;

        /// Desired value to change to
        ulong val;

        /// Pointer to next node in the (intrusive) hash map
        WriteSetEntry* next;
    }

    /// The write-set is a log of the words modified during the transaction.
    /// This log is an array with an intrusive hashmap of size
    /// config.hashBuckets.
    static struct WriteSet
    {
        /// Beyond this, it seems to be faster to use the hashmap
        enum ulong maxArrayLookup = 30;

        /// Intrusive HashMap for fast lookup in large(r) transactions
        WriteSetEntry*[config.hashBuckets] buckets;

        /// Number of stores in the writeSet for the current transaction
        ulong numStores;

        /// Redo log of stores
        WriteSetEntry[config.txMaxStores] log;

    @nogc nothrow:

        /// Each address on a different bucket
        pure
        static ulong hash(in shared(TMType!ulong)* addr)
        {
            return ((cast(ulong)addr) >> 3) % config.hashBuckets;
        }

        /// Adds a modification to the redo log
        void addOrReplace(T)(shared(TMType!T)* addr, ulong val)
        if (!is(T == ulong))
        {
            this.addOrReplace(cast(shared(TMType!ulong)*) addr, val);
        }

        /// ditto
        void addOrReplace(shared(TMType!ulong)* addr, ulong val)
        {
            if (tl_isReadOnly)
                tl_isReadOnly = false;

            auto hashAddr = hash(addr);

            if (numStores < maxArrayLookup) {
                // Lookup in array
                for (size_t idx = 0; idx < numStores; ++idx)
                {
                    if (log[idx].addr is addr)
                    {
                        log[idx].val = val;
                        return;
                    }
                }
            } else {
                // Lookup in hashmap
                WriteSetEntry* be = buckets[hashAddr];
                if (be < &log[numStores] && hash(be.addr) == hashAddr)
                {
                    while (null !is be)
                    {
                        if (be.addr is addr)
                        {
                            be.val = val;
                            return;
                        }
                        be = be.next;
                    }
                }
            }

            // Add to array
            WriteSetEntry* e = &log[numStores++];
            assert(numStores < config.txMaxStores);
            e.addr = addr;
            e.val = val;

            // Add to hashmap
            WriteSetEntry* be = buckets[hashAddr];
            // Clear if entry is from previous tx
            e.next = (be < e && hash(be.addr) == hashAddr) ? be : null;
            buckets[hashAddr] = e;
        }

        /// Does a lookup on the WriteSet for an addr.
        /// If the numStores is lower than MAX_ARRAY_LOOKUP, the lookup is
        /// done on the log, otherwise, the lookup is done on the hashmap.
        /// If it's not in the write-set, return lval.
        ulong lookupAddr(in shared(TMType!ulong)* addr, ulong lval)
        {
            if (numStores < maxArrayLookup)
            {
                // Lookup in array
                for (size_t idx = 0; idx < numStores; ++idx)
                {
                    if (log[idx].addr is addr)
                        return log[idx].val;
                }
            } else {
                // Lookup in hashmap
                auto hashAddr = hash(addr);
                WriteSetEntry* be = buckets[hashAddr];
                if (be < &log[numStores] && hash(be.addr) == hashAddr)
                {
                    while (be != null)
                    {
                        if (be.addr is addr)
                            return be.val;

                        be = be.next;
                    }
                }
            }

            return lval;
        }

        ulong lookupAddr(T)(in shared(TMType!T)* addr, ulong lval)
        {
            return lookupAddr(cast(shared(TMType!ulong)*) addr, lval);
        }

        // Assignment operator, used when making a copy of a WriteSet to help
        // another thread
        void opAssign(scope ref WriteSet other)
        {
            numStores = other.numStores;

            for (size_t i = 0; i < numStores; ++i)
                log[i] = other.log[i];
        }

        // Applies all entries in the log as DCASes.
        // Seq must match for DCAS to succeed. This method is on the "hot-path".
        void apply(ulong seq, in short tid)
        {
            for (size_t i = 0; i < numStores; ++i)
            {
                // Use an heuristic to give each thread 8 consecutive DCAS to apply
                WriteSetEntry* e = &log[(tid*8 + i) % numStores];
                auto tmte = e.addr;
                auto ltmt = (*tmte).atomicLoad!(MemoryOrder.acq);

                if (ltmt.seq < seq)
                    tmte.cas(ltmt, TMType!ulong(e.val, seq));
            }
        }
    }

    // One entry in the log of allocations.
    // In case the transactions aborts, we can rollback our allocations,
    // hiding the type information inside the lambda.
    static struct Deletable
    {
        /// Object to be deleted
        void[] obj;

        /// A wrapper to keep the type of the underlying object
        void function(void[]) reclaim;
    }

    __gshared static OneFileWF g_instance;

    // Indicates if the current thread is only a reader
    static bool tl_isReadOnly;

    enum int maxReadTries = 4;


    align(64) struct
    {
    align(16):
        OpData[] opData;
        TMType!(TransFunc*)[] operations;
        TMType!ulong[] results;
        WriteSet[] writeSets;
    }

    HazardErasOF he;
    align(64) shared(TxId) curTx = TxId(1, 0);

public:
    shared static this()
    {
        g_instance = allocator.make!OneFileWF();
    }

    @property
    static instance()
    {
        return g_instance;
    }

    this()
    {
        if (!ThreadRegistry.instance.isInitialized)
            ThreadRegistry.instance.initialize(config.registryMaxThreads);

        immutable maxThreads = ThreadRegistry.maxThreads;

        he = allocator.make!(HazardErasOF)(cast() maxThreads);
        opData = allocator.makeArray!OpData(maxThreads);
        writeSets = allocator.makeArray!WriteSet(maxThreads);
        operations = allocator.makeArray!(TMType!(TransFunc*))(maxThreads);
        results = allocator.makeArray!(TMType!ulong)(maxThreads);

        // This replaces the WriteSet constructor in the original C++ code
        foreach (writeSet; writeSets)
            for (size_t i = 0; i < config.hashBuckets; ++i)
                writeSet.buckets[i] = &writeSet.log[config.txMaxStores - 1];

        // TODO: think of something smarter to override default 1 on seq
        foreach(ref op; operations)
            op.seq.atomicStore!(MemoryOrder.raw)(0UL);
    }

    ~this()
    {
        allocator.dispose(opData);
        allocator.dispose(writeSets);
        allocator.dispose(cast(void[]) operations);
        allocator.dispose(cast(void[]) results);
    }

    // Progress condition: wait-free population-oblivious
    // Attempts to publish our write-set (commit the transaction) and then
    // applies the write-set.
    // Returns true if my transaction was committed.
    bool commitTx(ref OpData myOpData, in short tid)
    {
        // If it's a read-only transaction, then commit immediately
        if (0 == writeSets[tid].numStores && 0 == myOpData.numRetires)
            return true;

        // Give up if the curTx has changed sinced our transaction started
        if (myOpData.curTx != curTx.atomicLoad!(MemoryOrder.acq))
            return false;

        // Move our request to OPEN, using the sequence of the previous
        // transaction +1
        auto seq = myOpData.curTx.seq;
        auto newTx = TxId(seq+1, tid);
        myOpData.request.atomicStore!(MemoryOrder.rel)(newTx);

        // Attempt to CAS curTx to our OpData instance (tid) incrementing the
        // seq in it
        auto lcurTx = myOpData.curTx;
        debug printf("tid=%i  attempting CAS on curTx from (%ld,%ld) to (%ld,%ld)\n",
            tid, lcurTx.seq, lcurTx.idx, seq + 1, cast(ulong)tid);

        if (!curTx.casByRef(lcurTx, newTx))
            return false;

        // Execute each store in the write-set using DCAS() and close the
        // request
        helpApply(newTx, tid);
        retireRetiresFromLog(myOpData, tid);
        myOpData.numAllocs = 0;
        debug printf("Committed transaction (%ld,%ld) with %ld stores\n",
            seq + 1, cast(ulong)tid, writeSets[tid].numStores);

        return true;
    }


    // Progress condition: wait-free (bounded by the number of threads)
    // Applies a mutative transaction or gets another thread with an ongoing
    // transaction to apply it.
    // If three 'seq' have passed since the transaction when we published our
    // function, then the worst-case scenario is: the first transaction does not
    // see our function; the second transaction transforms our function
    // but doesn't apply the corresponding write-set; the third transaction
    // guarantees that the log of the second transaction is applied.
    void innerUpdateTx(ref OpData myOpData, TransFunc* funcptr, in short tid)
    {
        ++myOpData.nestedTrans;

        debug printf("updateTx(tid=%d)\n", tid);

        // We need an era from before the 'funcptr' is announced, so as to
        // protect it
        auto firstEra = curTx.atomicLoad!(MemoryOrder.acq).seq;
        operations[tid].rawStore(funcptr, results[tid].getSeq());
        OpData.current = &myOpData;

        // Check 3x for the completion of our operation because we don't have a fence
        // on operations[tid].rawStore(), otherwise it would be just 2x.
        for (int iter = 0; iter < 4; ++iter)
        {
            // An update transaction is read-only until it does the first store()
            tl_isReadOnly = true;

            // Clear the logs of the previous transaction
            deleteAllocsFromLog(myOpData);
            writeSets[tid].numStores = 0;
            myOpData.numRetires = 0;
            myOpData.curTx = curTx.atomicLoad!(MemoryOrder.acq);

            // Optimization: if my request is answered, then my tx is committed
            if (results[tid].getSeq() > operations[tid].getSeq())
                break;

            helpApply(myOpData.curTx, tid);

            // Reset the write-set after (possibly) helping another transaction
            // complete
            writeSets[tid].numStores = 0;

            // Use HE to protect the objects we're going to access during the
            // transform phase
            he.set(myOpData.curTx, tid);
            if (myOpData.curTx != curTx.atomicLoad())
                continue;

            try
                if (!transformAll(myOpData.curTx, tid))
                    continue;
            catch (AbortedTx)
                continue;

            if (commitTx(myOpData, tid))
                break;
        }

        // Clean up
        deleteAllocsFromLog(myOpData);
        OpData.current = null;
        --myOpData.nestedTrans;
        he.clear(tid);
        retireMyFunc(tid, funcptr, firstEra);
    }

    // Update transaction with non-void return value
    static ReturnType!F updateTx(F)(F func)
    if (!is(ReturnType!F == void))
    {
        immutable tid = ThreadRegistry.getTID();
        OpData* myOpData = &instance.opData[tid];

        if (myOpData.nestedTrans > 0)
            return func();

        // Copy the lambda to a std::function<> and announce a request with the pointer to it
        g_instance.innerUpdateTx(myOpData, new TransFunc(() { // FIXME
            return cast(ulong)func();
        }), tid);

        return cast(ReturnType!F) instance.results[tid].pload();
    }


    // Update transaction with void return value
    static void updateTx(F)(F func)
    if (is(ReturnType!F == void))
    {
        immutable tid = ThreadRegistry.getTID();
        OpData* myOpData = &instance.opData[tid];

        if (myOpData.nestedTrans > 0)
        {
            func();
            return;
        }

        // Copy the lambda to a std::function<> and announce a request with the pointer to it
        instance.innerUpdateTx(myOpData, new TransFunc(() { // FIXME
            func();
            return 0;
        }), tid);
    }

    // Progress condition: wait-free
    // (bounded by the number of threads + maxReadTries)
    ReturnType!F readTransaction(F)(F func)
    {
        immutable tid = ThreadRegistry.getTID();
        OpData* myOpData = &opData[tid];

        if (myOpData.nestedTrans > 0)
            return func();

        ++myOpData.nestedTrans;
        OpData.current = myOpData;
        tl_isReadOnly = true;

        debug printf("readTx(tid=%d)\n", tid);

        ReturnType!F retval;
        writeSets[tid].numStores = 0;
        myOpData.numAllocs = 0;
        myOpData.numRetires = 0;

        for (int iter = 0; iter < maxReadTries; ++iter)
        {
            myOpData.curTx = curTx.atomicLoad(MemoryOrder.acq);
            helpApply(myOpData.curTx, tid);

            // Use HE to protect the objects we're going to access during the
            // simulation
            he.set(myOpData.curTx, tid);

            // Reset the write-set after (possibly) helping another transaction
            // complete
            writeSets[tid].numStores = 0;
            if (myOpData.curTx != curTx.atomicLoad)
                continue;

            try
                retval = func();
            catch (AbortedTx)
                continue;

            // Clean up
            --myOpData.nestedTrans;
            OpData.current = null;
            he.clear(tid);

            return retval;
        }

        debug printf("readTx() executed maxReadTries, posing as updateTx()\n");
        --myOpData.nestedTrans;

        // Tried too many times unsucessfully, pose as an updateTx()
        return updateTx(func);
    }

    static ReturnType!F readTx(F)(F func)
    {
        return instance.readTransaction(func);
    }

    // When inside a transaction, the user can't call "make" directly because
    // if the transaction fails, it would leak the memory of these allocations.
    // Instead, we provide an allocator that keeps pointers to these objects
    // in a log, and in the event of a failed commit of the transaction, it
    // will delete the objects so that there are no leaks.
    //
    // TODO:
    //    - add support for class types
    static T* tmMake(T, Args...)(Args args)
    if (isTM!T)
    {
        auto objPtr = allocator.make!T(args);
        (cast(TMStruct*)objPtr)._newEra = g_instance.curTx
                .atomicLoad!(MemoryOrder.acq).seq;

        OpData* myOpData = OpData.current;

        if (myOpData != null)
        {
            assert(myOpData.numAllocs != config.txMaxAllocs);
            Deletable* del = myOpData.alog[myOpData.numAllocs++];
            del.obj = objPtr[0 .. T.sizeof];
            // This func ptr to a lambda gives us a way to call the destructor
            // when a transaction aborts.
            del.reclaim = function void(void[] obj)
            in (obj.length == T.sizeof)
            {
                allocator.dispose(cast(T*)obj.ptr);
            };
        }
        return objPtr;
    }

    // The user can not directly delete objects in the transaction because the
    // transaction may fail and needs to be retried and other threads may be
    // using those objects.
    // Instead, it has to call retire() for the objects it intends to delete.
    // The retire() puts the objects in the rlog, and only when the transaction
    // commits, the objects are put in the Hazard Eras retired list.
    // The del._delEra is filled in retireRetiresFromLog().
    static void tmDispose(T)(T* obj)
    if (isTM!T)
    {
        if (obj is null)
            return;

        OpData* myOpData = OpData.current;
        if (myOpData is null)
        {
            // Outside a transaction, use regular dispose
            allocator.dispose(obj);
            return;
        }

        typeid(*obj).destroy(obj); // Execute destructor as part of the current transaction
        assert(myOpData.numRetires != config.txMaxRetires);
        myOpData.rlog[myOpData.numRetires++] = obj;
    }

    // We snap a TMStruct at the beginning of the allocation
    static void[] tmAllocate(in size_t size)
    {
        auto roundedSize = (size + 7) & ~7;
        auto chunk = allocator.alignedAllocate(
                roundedSize + TMStruct.sizeof, TMStruct.alignof);

        // We must reset the contents to zero to guarantee that if any
        // TMTypes are allocated inside, their 'seq' will be zero
        (cast(ulong[])chunk)[] = 0;
        (cast(TMStruct*)chunk.ptr)._newEra =
                g_instance.curTx.atomicLoad!(MemoryOrder.acq).seq;

        OpData* myOpData = OpData.current;
        if (myOpData !is null)
        {
            assert(myOpData.numAllocs != config.txMaxAllocs);
            Deletable* del = &myOpData.alog[myOpData.numAllocs++];
            del.obj = chunk;
            del.reclaim = function void(void[] obj) {
                allocator.deallocate(obj);
            };
        }

        return chunk[TMStruct.sizeof .. TMStruct.sizeof + size];
    }

    // We assume there is a TMStruct in the beginning of the allocation
    static void tmDeallocate(void[] chunk)
    {
        if (chunk is null)
            return;

        OpData* myOpData = OpData.current;
        auto tmChunk = (chunk.ptr - TMStruct.sizeof)[
                0 .. chunk.length + TMStruct.sizeof];

        if (myOpData is null)
        {
            // Outside a transaction, just deallocate the object
            allocator.deallocate(tmChunk);
            return;
        }

        assert(myOpData.numRetires != config.txMaxRetires);
        myOpData.rlog[myOpData.numRetires++] = cast(TMStruct*)tmChunk.ptr;
    }

private:
    // Progress condition: wait-free population oblivious
    void helpApply(in TxId lcurTx, in short tid)
    {
        immutable idx = lcurTx.idx;
        immutable seq = lcurTx.seq;
        OpData* opd = &opData[idx];

        // Nothing to apply unless the request matches the curTx
        if (lcurTx != opd.request.atomicLoad!(MemoryOrder.acq))
            return;

        if (idx != tid)
        {
            // Make a copy of the write-set and check if it is consistent
            writeSets[tid] = writeSets[idx];
            // Use HE to protect the objects the transaction touches
            he.set(lcurTx, tid);
            if (lcurTx != curTx.atomicLoad())
                return;

            // The published era is now protecting all objects alive in the
            // transaction lcurTx
            if (lcurTx != opd.request.atomicLoad!(MemoryOrder.acq))
                return;
        }

        debug printf("Applying %ld stores in write-set\n",
                writeSets[tid].numStores);

        writeSets[tid].apply(seq, tid);

        auto newReq = TxId(seq + 1, idx);

        if (idx == tid)
            opd.request.atomicStore!(MemoryOrder.rel)(newReq);
        else if (opd.request.atomicLoad!(MemoryOrder.acq) == lcurTx)
            opd.request.casByRef(lcurTx, newReq);
    }

    // This is called when the transaction fails, to undo all the allocations
    // done during the transaction
    void deleteAllocsFromLog(ref OpData myOpData)
    {
        for (size_t i = 0; i < myOpData.numAllocs; ++i)
            myOpData.alog[i].reclaim(myOpData.alog[i].obj);

        myOpData.numAllocs = 0;
    }

    // My transaction was successful, it's my duty to cleanup any retired
    // objects. This is called by the owner thread when the transaction
    // succeeds, to pass the retired objects to Hazard Eras. We can't delete
    // the objects immediately because there might be other threads trying to
    // apply our log which may (or may not) contain addresses inside the
    // objects in this list.
    void retireRetiresFromLog(ref OpData myOpData, in short tid)
    {
        immutable lseq = curTx.atomicLoad!(MemoryOrder.acq).seq;

        // First, add all the objects to the list of retired/zombies
        for (size_t i = 0; i < myOpData.numRetires; ++i)
        {
            myOpData.rlog[i]._delEra = lseq;
            he.addToRetiredList(myOpData.rlog[i], tid);
        }

        // Second, start a cleaning phase, scanning to see which objects can be removed
        he.clean(lseq, tid);
        myOpData.numRetires = 0;
    }

    void retireMyFunc(in short tid, TransFunc* myfunc, ulong firstEra)
    {
        myfunc._tm._newEra = firstEra;
        myfunc._tm._delEra = curTx.atomicLoad!(MemoryOrder.acq).seq + 1; // Do we really need the +1 ?
        he.addToRetiredListTx(myfunc, tid);
    }

    // Aggregate all the functions of the different thread's writeTransaction()
    // and transform them into to a single log (the current thread's log).
    // Returns true if all active TransFunc were transformed
    bool transformAll(in TxId lcurrTx, in short tid)
    {
        for (size_t i = 0; i < ThreadRegistry.maxTID; ++i)
        {
            // Check if the operation of thread i has been applied (has a
            // matching result)
            TransFunc* txfunc;
            ulong res, operationsSeq, resultSeq;
            if (!operations[i].rawLoad(txfunc, operationsSeq))
                continue;

            if (!results[i].rawLoad(res, resultSeq))
                continue;

            if (resultSeq > operationsSeq)
                continue;

            // Operation has not yet been applied, check that transaction
            // identifier has not changed

            if (lcurrTx != curTx.atomicLoad!(MemoryOrder.acq))
                return false;

            // Apply the operation of thread i and save result in results[i],
            // with this store being part of the transaction itself.
            results[i] = txfunc.func();
        }

        return true;
    }
}

class AbortedTx : Exception
{
    import std.exception : basicExceptionCtors;

    ///
    mixin basicExceptionCtors;
}

//
// Wrapper methods to the global TM instance. The user should use these:
//
ReturnType!F updateTx(F)(F func)
if (!is(ReturnType!F == void))
{
    return OneFileWF.instance.updateTx(func);
}

ReturnType!F readTx(F)(F func)
if (!is(ReturnType!F == void))
{
    return OneFileWF.instance.readTx(func);
}

void updateTx(F)(F func)
if (is(ReturnType!F == void))
{
    OneFileWF.instance.updateTx(func);
}

void readTx(F)(F func)
if (is(ReturnType!F == void))
{
    OneFileWF.instance.readTx(func);
}

alias tmMake = OneFileWF!().tmMake;
alias tmDispose = OneFileWF!().tmDispose;
alias tmAllocate = OneFileWF!().tmAllocate;
alias tmDeallocate = OneFileWF!().tmDeallocate;

private void[] toChunk(T)(T* obj)
if (is(T == struct) || isScalarType!T)
{
    return cast(void[])(obj[0 .. 1]);
}
