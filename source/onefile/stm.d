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
module onefile.stm;

import onefile.internal.allocator;
import onefile.internal.config : config;
import onefile.thread_registry : ThreadRegistry;

import core.atomic;
import std.algorithm.mutation : move;
import std.traits : Fields, hasFunctionAttributes, isCallable, isFunction,
        isPointer, isScalarType, Parameters, PointerTarget, ReturnType, Unqual;

debug(PRINTF) import core.stdc.stdio : printf;

struct TxId
{
private:
    ulong _raw;

@nogc nothrow pure @safe:

    this(ulong seq, ushort idx)
    {
        _raw = (seq << 10) | idx;
    }

public:
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

struct TMStruct
{
package:
    ulong _newEra;
    ulong _delEra;
}

template isTM(T)
if (is(T == struct))
{
    enum isTM = is(T == TMStruct) || is(T == shared(TMStruct))
            || (.isTM!(Fields!T[0]) && 0 == T.tupleof[0].offsetof);
}

template isTM(T)
if (!is(T == struct))
{
    enum isTM = false;
}

/++
    Base class for classes that need to be (de)allocated transactionally
+/
abstract class TMObject
{
package:
    TMStruct _tm;
}

package abstract class Request : TMObject
{
    @nogc:

    protected abstract ulong execute();
    ~this() { }
}

private final class DelegateRequest(DG) : Request
if (is(DG == delegate)
        && 0 == Parameters!DG.length
        && hasFunctionAttributes!(DG, "@nogc"))
{
private:
    DG _func;

public @nogc:
    this(DG func)
    in (null !is func)
    {
        _func = func;
    }

    override ulong execute()
    {
        static if (is(ReturnType!DG == void))
        {
            _func();
            return 0UL;
        }
        else
            return cast(ulong) _func();
    }
}

private final class SpecializedRequest(alias func) : Request
{
private:
    import std.traits :
            STC = ParameterStorageClass,
            ParameterStorageClassTuple;

    import std.meta : AliasSeq;

    enum bool funcHasParameters = Parameters!func.length > 0;

    static if (funcHasParameters)
    {
        alias FP = Parameters!func;
        alias fpStc = ParameterStorageClassTuple!func;
        static assert (FP.length == fpStc.length);

        template RefAsPtr(size_t i)
        if (i < FP.length)
        {
            static if (fpStc[i] & (STC.ref_ | STC.out_))
                alias RefAsPtr = FP[i]*;
            else
                alias RefAsPtr = FP[i];
        }

        template RefAsPtrAcc(size_t i)
        if (i < FP.length)
        {
            static if (i < FP.length - 1)
                alias RefAsPtrAcc = AliasSeq!(RefAsPtr!i, RefAsPtrAcc!(i + 1));
            else
                alias RefAsPtrAcc = RefAsPtr!i;
        }

        // AliasSeq is necessary here to ensure _args is always a tuple
        AliasSeq!(RefAsPtrAcc!0) _args;
    }

    static if (funcHasParameters)
    {
        enum _code_callFunc = () {
            import std.format : format;
            import std.string : join;

            assert (__ctfe);

            string[] expandedArgs;

            static foreach (i; 0 .. FP.length)
            {
                expandedArgs ~= format("%s_args[%d]",
                        (fpStc[i] & (STC.ref_ | STC.out_)) ? "*" : null, i);
            }

            return format("func(%s)", expandedArgs.join(", "));
        } ();
    } else {
        enum _code_callFunc = "func()";
    }

public @nogc:
    static if (funcHasParameters)
    this(ref Parameters!func args)
    {
        static foreach (size_t i, arg; args)
        {
            static if (fpStc[i] & (STC.ref_ | STC.out_))
                _args[i] = &arg;
            else
                _args[i] = arg;
        }
    }

    override ulong execute()
    {
        static if (is(ReturnType!func == void))
        {
            (mixin(_code_callFunc));
            return 0UL;
        }
        else static if (is(ReturnType!func == class)
                || is(ReturnType!func == interface))
            return cast(ulong) cast(void*) mixin(_code_callFunc);
        else
            return cast(ulong) mixin(_code_callFunc);
    }
}

// Provides work-around for Phobos bug
//         (ERROR: forward reference to variable hasUnsharedAliasing)
private template safeHasUnsharedAliasing(T)
{
    import std.traits : hasUnsharedAliasing;

    static if (is(T == shared))
        enum bool safeHasUnsharedAliasing = false;
    else static if (isPointer!T && is(PointerTarget!T == shared))
        enum bool safeHasUnsharedAliasing = false;
    else
        alias safeHasUnsharedAliasing = hasUnsharedAliasing!T;
}

/++
Denotes a transactional memory location

A TMType has a storage capacity of 64 bits.

`T` is the type of value to be stored. This is typically a pointer to a node,
but it can be an integer or other stuff, as long as it fits in 64 bits.

`TMType!T` will try to behave like `T` as much as possible. In cases where it
doesn't, you'll probably need to add an explicit `.pload()`.
+/
align(16)
static shared struct TMType(T)
if (T.sizeof <= ulong.sizeof && (!safeHasUnsharedAliasing!T || is(T == Request)))
{
    static if (is(T == ulong))
        private struct Val
        {
            ulong untyped;
            alias typed = untyped;
            alias untyped this;
        }
    else static if (!is(T == shared))
        private union Val
        {
            T _typed;
            ulong untyped;
            alias untyped this;

            @nogc nothrow @property:

            ref inout(T) typed() inout
            {
                return _typed;
            }

            ref inout(T) typed() inout shared
            {
                return *(cast(inout T*) &_typed);
            }
        }
    else
        private union Val
        {
            T typed;
            ulong untyped;
            alias untyped this;
        }

    // Stores the actual value as an atomic
    Val val;

    // Tx sequence number
    ulong seq = 1;

    // This is important for DCAS
    static assert(ulong.sizeof * 2 == TMType.sizeof);

    @nogc
    {
        /++
        Construct a TMType initialized with a specific value

        Params:
            initVal = the initial value for this TMType
        +/
        this(T initVal)
        {
            if (__ctfe)
                cast() val.typed = cast() initVal;
            else
                isolated_store(initVal);
        }

        /++
        Construct a TMType initialized with a value obtained from another TMType

        Params:
            other = the TMType whose value is to be copied into this new TMType
        +/
        this(TMType other)
        {
            pstore(other.pload);
        }

        private this(ulong val, ulong seq)
        {
            this.val.untyped = val;
            this.seq = seq;
        }

        /++
        Convert this to a typed instance

        Only valid on `TMType!ulong`

        Returns: a reference to this TMType, typed as requested
        +/
        @property
        ref inout(TMType!U) typed(U)() inout
        if (is(T == ulong) && is(TMType!U))
        {
            return *(cast(inout(TMType!U)*) &this);
        }

        /++
        Convert this to an untyped instance

        For `TMType!ulong`, this is a noop.

        Returns: a reference to this TMType, typed as a TMType!ulong
        +/
        @property
        ref inout(TMType!ulong) untyped() inout
        {
            return *(cast(inout(TMType!ulong)*) &this);
        }

        // Assignment operator from a TMType
        void opAssign(TMType other)
        {
            pstore(other.pload());
        }

        // Assignment operator from a value
        void opAssign(T value)
        {
            pstore(value);
        }
    }

    T opOpAssign(string op)(TMType lhs)
    {
        auto result = mixin("pload() " ~ op ~ " lhs.pload()");
        pstore(result);
        return result;
    }

    T opOpAssign(string op)(T lhs)
    {
        auto result = mixin("pload() " ~ op ~ " lhs");
        pstore(result);
        return result;
    }

    auto opUnary(string op)()
    {
        return mixin(op ~ "(pload())");
    }

    auto opBinary(string op)(T rhs)
    {
        return mixin("pload() " ~ op ~ " rhs");
    }

    auto opBinary(string op)(TMType rhs)
    {
        return mixin("pload() " ~ op ~ " rhs.pload()");
    }

    auto opBinaryRight(string op)(T lhs)
    {
        return mixin("lhs " ~ op ~ " pload()");
    }

    auto opBinaryRight(string op)(TMType lhs)
    {
        return mixin("lhs.pload() " ~ op ~ " pload()");
    }

    bool opEquals(T rhs) const
    {
        return pload() == rhs;
    }

    bool opEquals(TMType rhs) const
    {
        return pload() == rhs.pload();
    }

    // TODO: comparison operators (opCmp)

    @nogc:

    /++
    Isolated store

    Meant to be called when we know we're the only ones touching these contents,
    for example, in the constructor of an object, before making the object
    visible to other threads.

    An `isolated_store` is faster than a `pstore`, but is not transactionally
    safe.

    Params:
        newVal = the new value for this TMType
    +/
    void isolated_store(T newVal)
    {
        Val lNewVal;
        cast() lNewVal.typed = cast() newVal;
        val.untyped.atomicStore!(MemoryOrder.raw)(lNewVal.untyped);
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
        Val lNewVal;
        cast() lNewVal.typed = cast() newVal;
        val.untyped.atomicStore!(MemoryOrder.raw)(lNewVal.untyped);
        seq.atomicStore!(MemoryOrder.rel)(lseq);
    }

    /++
    Gets the value of this TMType as seen in the current transaction

    If called outside a transaction, it returns the latest committed value.

    If another transaction committed a write to this TMType after the current
    transaction started, `pload` will abort the current transaction.

    If the current transaction has written to this TMType already, that
    uncommitted value is returned.
    +/
    inout(T) pload() inout shared
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

        auto lval = val.atomicLoad!(MemoryOrder.acq);

        const myOpData = OneFileWF.OpData.current;

        if (null is myOpData)
            return cast(inout) lval.typed;

        auto lseq = seq.atomicLoad!(MemoryOrder.acq);

        if (lseq > myOpData.curTx.seq)
            throw new AbortedTx("Transaction aborted.");

        if (OneFileWF.tl_isReadOnly)
            return cast(inout) lval.typed;

        lval.untyped = OneFileWF.g_instance
                .writeSets[ThreadRegistry.s_tid]
                .lookupAddr(&this, lval);

        return cast(inout) lval.typed;
    }

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
        cast() keepVal = cast() val.atomicLoad!(MemoryOrder.acq).typed;
        return (keepSeq == seq.atomicLoad!(MemoryOrder.acq));
    }

    /++
    Transactional store

    Adds the specified value to the write set of the current transaction. This
    TMType itself will get updated when the write set is applied during
    transaction commit.

    If called outside a transaction, just updates the TMType, much like
    `isolated_store`. Such may break invariants of a transaction executing in
    parallel.

    Params:
        newVal = the new value for this TMType
    +/
    void pstore(T newVal) shared
    {
        // We don't need to check currTx here because we're not
        // de-referencing the val. It's only after a load() that the val
        // may be de-referenced (in user code), therefore we do the check
        // on load() only.

        Val lNewVal;
        cast() lNewVal.typed = cast() newVal;

        if (null is OneFileWF.OpData.current)
        {
            // Looks like we're outside a transaction
            untyped.val.untyped.atomicStore!(MemoryOrder.raw)(lNewVal.untyped);
        }
        else
        {
            OneFileWF.g_instance
                .writeSets[ThreadRegistry.s_tid]
                .addOrReplace(&this, lNewVal);
        }
    }

    @property
    void opDispatch(string fname, V)(auto ref V value) shared
    if (__traits(hasMember, val.typed, fname)
            && !isFunction!(__traits(getMember, val.typed, fname))
            && is(isAssignable!(V, typeof(__traits(getMember, val.typed, fname)))))
    {
        Val lval = { untyped: untyped.pload() };

        immutable orgUntypedValue = lval.untyped;
        __traits(getMember, lval.typed, fname) = value;

        if (lval.untyped != orgUntypedValue)
            untyped.pstore(lval.untyped);
    }

    @property
    auto opDispatch(string fname)() inout shared
    if (__traits(hasMember, val.typed, fname)
            && !isFunction!(__traits(getMember, val.typed, fname)))
    {
        inout Val lval = { untyped: untyped.pload() };
        return __traits(getMember, lval.typed, fname);
    }

    auto opDispatch(string fname, Args ...)(auto ref Args args) shared
    if (__traits(hasMember, val.typed, fname)
            && isFunction!(__traits(getMember, val.typed, fname)))
    {
        import core.internal.traits : Unconst;
        import std.meta : Filter;

        Val lval;
        lval.typed = pload();

        template isMatchingOverload(alias fn)
        {
            enum bool isMatchingOverload = is(Args == Parameters!fn); // FIXME
        }

        alias F = Filter!(isMatchingOverload, __traits(getOverloads, lval.typed, fname, true))[0];
        alias R = typeof(__traits(getMember, lval.typed, fname)(args));

        static if (hasFunctionAttributes!(F, "const")
            || hasFunctionAttributes!(F, "inout"))
        {
            static if (is(R == void))
                __traits(getMember, lval.typed, fname)(args);
            else
                return __traits(getMember, lval.typed, fname)(args);
        }
        else
        {
            static if (is(R == void))
            {
                immutable orgUntypedValue = lval.untyped;
                __traits(getMember, lval.typed, fname)(args);

                if (lval.untyped != orgUntypedValue)
                    untyped.pstore(lval.untyped);
            }
            else
            {
                immutable orgUntypedValue = lval.untyped;
                auto retVal = __traits(getMember, lval.typed, fname)(args);

                if (lval.untyped != orgUntypedValue)
                    untyped.pstore(lval.untyped);

                return retVal;
            }
        }
    }

    auto opDispatch(string fname, Args ...)(auto ref Args args) inout shared
    if (__traits(hasMember, val.typed, fname)
            && isFunction!(__traits(getMember, val.typed, fname)))
    {
        inout Val lval = { untyped: untyped.pload() };

        static if (!isFunction!(__traits(getMember, lval.typed, fname)))
        {
            static assert(0 == Args.length);
            return __traits(getMember, lval.typed, fname);
        }
        else
        {
            alias R = typeof(__traits(getMember, lval.typed, fname)(args));

            if (is(R == void))
                __traits(getMember, lval.typed, fname)(args);
            else
                return __traits(getMember, lval.typed, fname)(args);
        }
    }
}

align(64)
class OneFileWF
{
private:
    import onefile.hazard_eras : HazardErasOF;

    // Its purpose is to hold thread-local data
    static struct OpData
    {
        import onefile.hazard_eras : RListEntry;

        private static OpData* tl_current;

        @nogc
        nothrow
        @property
        static OpData* current()
        {
            return tl_current;
        }

        @nogc
        nothrow
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
        RListEntry[config.txMaxRetires] rlog;

        // Number of calls to tmNew() in this transaction (owner thread only)
        ulong numAllocs;

        // List of newly allocated objects during the transaction
        // (owner thread only)
        ALogEntry[config.txMaxAllocs] alog;
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
    static struct ALogEntry
    {
        /// Object to be deleted
        void[] obj;

        /// A wrapper to keep the type of the underlying object
        void function(void[]) @nogc reclaim;
    }

    __gshared static OneFileWF g_instance;

    // Indicates if the current thread is only a reader
    static bool tl_isReadOnly;

    enum int maxReadTries = 4;

    align(64) struct
    {
    align(16):
        OpData[] opData;
        TMType!Request[] operations;
        TMType!ulong[] results;
        WriteSet[] writeSets;
    }

    HazardErasOF he;
    align(64) shared(TxId) curTx = TxId(1, 0);

    @nogc
    shared static this()
    {
        g_instance = allocator.make!OneFileWF();
    }

    // Progress condition: wait-free population-oblivious
    // Attempts to publish our write-set (commit the transaction) and then
    // applies the write-set.
    // Returns true if my transaction was committed.
    @nogc
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
        debug(PRINTF) printf("tid=%i  attempting CAS on curTx from (%ld,%ld) to (%ld,%ld)\n",
            tid, lcurTx.seq, lcurTx.idx, seq + 1, cast(ulong)tid);

        if (!(&curTx).cas(lcurTx, newTx))
        {
            debug(PRINTF) printf("Failed to commit transaction (%ld,%ld)\n",
                seq + 1, cast(ulong)tid);
            return false;
        }

        // Execute each store in the write-set using DCAS() and close the
        // request
        helpApply(newTx, tid);
        retireRetiresFromLog(myOpData, tid);
        myOpData.numAllocs = 0;
        debug(PRINTF) printf("Committed transaction (%ld,%ld) with %ld stores\n",
            seq + 1, cast(ulong)tid, writeSets[tid].numStores);

        return true;
    }


    // Progress condition: wait-free (bounded by the number of threads)
    // Applies a mutative transaction or gets another thread with an ongoing
    // transaction to apply it.
    // If three 'seq' have passed since the transaction when we published our
    // function, then the worst-case scenario is: the first transaction does
    // not see our function; the second transaction transforms our function
    // but doesn't apply the corresponding write-set; the third transaction
    // guarantees that the log of the second transaction is applied.
    @nogc
    void innerUpdateTx(
        ref OpData myOpData, Request request, in short tid)
    {
        ++myOpData.nestedTrans;

        debug(PRINTF) printf("updateTx(tid=%d)\n", tid);

        // We need an era from before the 'funcptr' is announced, so as to
        // protect it
        auto firstEra = curTx.atomicLoad!(MemoryOrder.acq).seq;
        operations[tid].rawStore(request, results[tid].getSeq());
        OpData.current = &myOpData;

        // Check 3x for the completion of our operation because we don't
        // have a fence on operations[tid].rawStore(), otherwise it would be
        // just 2x.
        for (int iter = 0; iter < 4; ++iter)
        {
            // An update transaction is read-only until it does the first
            // store()
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
        retireRequest(tid, request, firstEra);
    }

public:
    @nogc
    @property
    static instance()
    {
        return g_instance;
    }

    @nogc
    this()   // Somehow the constructor needs to be public
    {
        if (!ThreadRegistry.instance.isInitialized)
            ThreadRegistry.instance.initialize(config.registryMaxThreads);

        immutable maxThreads = ThreadRegistry.maxThreads;

        he = allocator.make!(HazardErasOF)(cast() maxThreads);
        opData = allocator.makeArray!OpData(maxThreads);
        writeSets = allocator.makeArray!WriteSet(maxThreads);
        operations = allocator.makeArray!(TMType!Request)(maxThreads);
        results = allocator.makeArray!(TMType!ulong)(maxThreads);

        // This replaces the WriteSet constructor in the original C++ code
        foreach (ref writeSet; writeSets)
            for (size_t i = 0; i < config.hashBuckets; ++i)
                writeSet.buckets[i] = &writeSet.log[config.txMaxStores - 1];

        // TODO: think of something smarter to override default 1 on seq
        foreach(ref op; operations)
            op.seq.atomicStore!(MemoryOrder.raw)(0UL);
    }

    @nogc
    ~this()
    {
        allocator.dispose(opData);
        allocator.dispose(writeSets);
        allocator.dispose(cast(void[]) operations);
        allocator.dispose(cast(void[]) results);
    }

    // Update transaction
    @nogc
    ReturnType!func updateTx(alias func)(auto ref Parameters!func args)
    {
        import std.traits : hasFunctionAttributes;

        // Just to provide an understandable error message
        static assert(hasFunctionAttributes!(func, "@nogc"),
                "Non-@nogc callable " ~ func.stringof ~
                " cannot be used as a transaction function.");

        enum bool isVoid = is(ReturnType!func == void);

        static if (!isVoid)
        {
            static assert(is(ReturnType!func == class)
                    || is(ReturnType!func == interface)
                    || __traits(compiles, {
                        ReturnType!func v;
                        return cast(ulong) v;
                    }), ReturnType!func.stringof ~
                    " is not a valid return type for a transaction function.");
        }

        immutable tid = ThreadRegistry.getTID();
        OpData* myOpData = &opData[tid];

        if (myOpData.nestedTrans > 0)
        {
            static if (isVoid)
            {
                func(args);
                return;
            }
            else
                return func(args);
        }

        // Announce a request with func
        innerUpdateTx(*myOpData,
                allocator.make!(SpecializedRequest!func)(args), tid);

        static if (!isVoid)
            return results[tid].typed!(ReturnType!func).pload();
    }

    @nogc
    ReturnType!DG updateTx(DG)(scope DG func)
    if (is(DG == delegate)
            && 0 == Parameters!DG.length
            && hasFunctionAttributes!(DG, "@nogc"))
    {
        enum bool isVoid = is(ReturnType!DG == void);

        static if (!isVoid)
        {
            static assert(is(ReturnType!func == class)
                    || is(ReturnType!func == interface)
                    || __traits(compiles, {
                        ReturnType!func v;
                        return cast(ulong) v;
                    }), ReturnType!func.stringof ~
                    " is not a valid return type for a transaction function.");
        }

        immutable tid = ThreadRegistry.getTID();
        OpData* myOpData = &opData[tid];

        if (myOpData.nestedTrans > 0)
        {
            static if (isVoid)
            {
                func();
                return;
            }
            else
                return func();
        }

        // Announce a request with func
        innerUpdateTx(*myOpData,
                allocator.make!(DelegateRequest!DG)(func), tid);

        static if (!isVoid)
            return results[tid].typed!(ReturnType!DG).pload();
    }

    // Progress condition: wait-free
    // (bounded by the number of threads + maxReadTries)
    @nogc
    ReturnType!func readTx(alias func)(auto ref Parameters!func args)
    if (isCallable!func && !is(ReturnType!func == void))
    {
        import std.traits : Unqual;
        import std.typecons : UnqualRef;

        immutable tid = ThreadRegistry.getTID();
        OpData* myOpData = &opData[tid];

        if (myOpData.nestedTrans > 0)
            return func(args);

        ++myOpData.nestedTrans;
        OpData.current = myOpData;
        tl_isReadOnly = true;

        debug(PRINTF) printf("readTx(tid=%d)\n", tid);

        static if (is(ReturnType!func == class)
                || is(ReturnType!func == interface))
            UnqualRef!(ReturnType!func) retval;
        else
            Unqual!(ReturnType!func) retval;

        writeSets[tid].numStores = 0;
        myOpData.numAllocs = 0;
        myOpData.numRetires = 0;

        for (int iter = 0; iter < maxReadTries; ++iter)
        {
            myOpData.curTx = curTx.atomicLoad!(MemoryOrder.acq);
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
                retval = func(args);
            catch (AbortedTx)
                continue;

            // Clean up
            --myOpData.nestedTrans;
            OpData.current = null;
            he.clear(tid);

            return retval;
        }

        debug(PRINTF) printf("readTx() executed %d times, posing as updateTx()\n",
                maxReadTries);

        --myOpData.nestedTrans;

        // Tried too many times unsucessfully, pose as an updateTx()
        return updateTx!(func)(args);
    }


    // Progress condition: wait-free
    // (bounded by the number of threads + maxReadTries)
    @nogc
    ReturnType!DG readTx(DG)(scope DG func)
    if (is(DG == delegate)
            && 0 == Parameters!DG.length
            && hasFunctionAttributes!(DG, "@nogc"))
    {
        import std.traits : Unqual;
        import std.typecons : UnqualRef;

        immutable tid = ThreadRegistry.getTID();
        OpData* myOpData = &opData[tid];

        if (myOpData.nestedTrans > 0)
            return func();

        ++myOpData.nestedTrans;
        OpData.current = myOpData;
        tl_isReadOnly = true;

        debug(PRINTF) printf("readTx(tid=%d)\n", tid);

        static if (is(ReturnType!func == class)
                || is(ReturnType!func == interface))
            UnqualRef!(ReturnType!func) retval;
        else
            Unqual!(ReturnType!func) retval;

        writeSets[tid].numStores = 0;
        myOpData.numAllocs = 0;
        myOpData.numRetires = 0;

        for (int iter = 0; iter < maxReadTries; ++iter)
        {
            myOpData.curTx = curTx.atomicLoad!(MemoryOrder.acq);
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

        debug(PRINTF) printf("readTx() executed %d times, posing as updateTx()\n",
                maxReadTries);

        --myOpData.nestedTrans;

        // Tried too many times unsucessfully, pose as an updateTx()
        return updateTx(func);
    }

    @nogc
    @property
    static bool isInTx()
    {
        return null !is OpData.current;
    }

    // When inside a transaction, the user can't call "make" directly because
    // if the transaction fails, it would leak the memory of these allocations.
    // Instead, we provide an allocator that keeps pointers to these objects
    // in a log, and in the event of a failed commit of the transaction, it
    // will delete the objects so that there are no leaks.
    //
    // TODO:
    //    - improve support for class types
    static tmMake(T, Args...)(Args args)
    if (isTM!T || is(Unqual!T : TMObject)) // FIXME: class must be derived from TMObject
    {
        auto objPtr = allocator.make!T(args);

        static if (is(T == class))
            auto tmsPtr = &(cast(TMObject)objPtr)._tm;
        else
            auto tmsPtr = cast(TMStruct*)objPtr;

        tmsPtr._newEra = g_instance.curTx.atomicLoad!(MemoryOrder.acq).seq;

        OpData* myOpData = OpData.current;

        if (myOpData !is null)
        {
            assert(myOpData.numAllocs != config.txMaxAllocs);
            ALogEntry* del = &myOpData.alog[myOpData.numAllocs++];

            // del.reclaim is set to a func ptr to a lambda. this gives us a
            // way to call the destructor when a transaction aborts.
            static if (is(T == class))
            {
                enum instanceSize = __traits(classInstanceSize, T);
                del.obj = (cast(void*)objPtr)[0 .. instanceSize];
                del.reclaim = function void(void[] obj)
                in (obj.length == instanceSize)
                in (null !is cast(T)obj.ptr)
                {
                    allocator.disposeNoGc(cast(T)(obj.ptr));
                };
            }
            else
            {
                del.obj = cast(void[])(objPtr[0 .. 1]);
                del.reclaim = function void(void[] obj)
                in (obj.length == T.sizeof)
                {
                    allocator.dispose(cast(T*)obj.ptr);
                };
            }
        }

        static if (is(T == class))
            return objPtr;
        else
            // cast is a work around if T is an unshared 'shared struct'
            return cast(T*) objPtr;
    }

    static tmMake(T, Args...)(Args args)
    if (!is(T == class) && !isTM!T)
    {
        import std.conv : emplace;

        return tmAllocate(T.sizeof).emplace!T(args);
    }

    // The user can not directly delete objects in the transaction because the
    // transaction may fail and needs to be retried and other threads may be
    // using those objects.
    // Instead, it has to call retire() for the objects it intends to delete.
    // The retire() puts the objects in the rlog, and only when the transaction
    // commits, the objects are put in the Hazard Eras retired list.
    // The del._delEra is filled in retireRetiresFromLog().
    static void tmDispose(T)(auto ref T* obj)
    if (isTM!T)
    {
        import std.traits : hasElaborateDestructor;
        import onefile.hazard_eras : RListEntry;

        if (obj is null)
            return;

        OpData* myOpData = OpData.current;
        if (myOpData is null)
        {
            // Outside a transaction, use regular dispose
            allocator.dispose(obj);
            return;
        }

        static if (hasElaborateDestructor!T)
            obj.__dtor(); // Execute destructor as part of the current transaction

        assert(myOpData.numRetires != config.txMaxRetires);

        auto rle = RListEntry(obj);
        move(rle, myOpData.rlog[myOpData.numRetires++]);

        static if (__traits(isRef, obj))
            obj = null;
    }

    static void tmDispose(T)(auto ref T obj)
    if (is(Unqual!T : TMObject))
    {
        import onefile.hazard_eras : RListEntry;

        if (obj is null)
            return;

        OpData* myOpData = OpData.current;
        if (myOpData is null)
        {
            // Outside a transaction, use regular dispose
            allocator.disposeNoGc(obj);
            return;
        }

        static if (__traits(hasMember, T, "__dtor"))
            obj.__dtor();

        assert(myOpData.numRetires != config.txMaxRetires);

        auto rle = RListEntry(obj);
        move(rle, myOpData.rlog[myOpData.numRetires++]);

        static if (__traits(isRef, obj))
            obj = null;
    }

    static void tmDispose(T)(auto ref T* obj)
    if (!is(T == class) && !isTM!T)
    {
        static if (is(T == struct))
            destroy!false(*obj);

        tmDeallocate(cast(void[]) obj[0 .. 1]);
    }

    // We snap a TMStruct at the beginning of the allocation
    @nogc
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
            ALogEntry* del = &myOpData.alog[myOpData.numAllocs++];
            del.obj = chunk;
            del.reclaim = function void(void[] obj) {
                allocator.deallocate(obj);
            };
        }

        return chunk[TMStruct.sizeof .. TMStruct.sizeof + size];
    }

    // We assume there is a TMStruct in the beginning of the allocation
    @nogc
    static void tmDeallocate(void[] chunk)
    {
        import onefile.hazard_eras : RListEntry;

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

        auto rle = RListEntry(tmChunk);
        move(rle, myOpData.rlog[myOpData.numRetires++]);
    }

    @nogc:
    static bool isUncommittedTMAllocation(PTR)(PTR ptr)
    if (is(Unqual!PTR : TMObject))
    {
        OpData* myOpData = OpData.current;

        if (null is myOpData)
            return false;

        myOpData.alog[].any!(e => e.obj is cast(void*) ptr);
    }

    @nogc:
    static bool isUncommittedTMAllocation(PTR)(PTR ptr)
    if (!is(T == class) && !isTM!T)
    {
        OpData* myOpData = OpData.current;

        if (null is myOpData)
            return false;

        myOpData.alog[].any!(e => e.obj is ptr);
    }

    @nogc:
    static bool isUncommittedTMAllocation(PTR)(PTR ptr)
    if (!isTM!(PointerTarget!PTR))
    {
        return isUncommittedTMAllocation(
                cast(TMStruct*) (ptr - TMStruct.sizeof));
    }

private @nogc:
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

        debug(PRINTF) printf("Applying %ld stores in write-set\n",
                writeSets[tid].numStores);

        writeSets[tid].apply(seq, tid);

        auto newReq = TxId(seq + 1, idx);

        if (idx == tid)
            opd.request.atomicStore!(MemoryOrder.rel)(newReq);
        else if (opd.request.atomicLoad!(MemoryOrder.acq) == lcurTx)
            (&opd.request).cas(lcurTx, newReq);
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
            myOpData.rlog[i].tmStruct._delEra = lseq;
            he.addToRetiredList(myOpData.rlog[i], tid);
        }

        // Second, start a cleaning phase, scanning to see which objects can be removed
        he.clean(lseq, tid);
        myOpData.numRetires = 0;
    }

    void retireRequest(in short tid, Request request, ulong firstEra)
    {
        request._tm._newEra = firstEra;
        request._tm._delEra = curTx.atomicLoad!(MemoryOrder.acq).seq + 1; // Do we really need the +1 ?
        he.addToRetiredListTx(request, tid);
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
            Request request;
            ulong res, operationsSeq, resultSeq;
            if (!operations[i].rawLoad(request, operationsSeq))
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
            results[i] = request.execute();
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

@nogc {
    /++
    Perform a read transaction.

    Use a readTx when you are sure that func will not try to modify any
    transactional data. Usually `readTx` is faster than `updateTx` with the same
    function.

    Transactions can safely be nested, as long as an update transaction is never
    nested inside a read transaction.

    Trying to modify transactional data inside a read transaction results in
    undefined behavior.

    Parameters:
        func = (delegate to a) function that implements the transaction to be
            executed.
    +/
    ReturnType!DG readTx(DG)(scope DG func)
    if (!is(ReturnType!DG == void) && 0 == Parameters!func.length)
    {
        return OneFileWF.instance.readTx(func);
    }

    /// ditto
    ReturnType!func readTx(alias func)(auto ref Parameters!func args)
    if (!is(ReturnType!func == void))
    {
        return OneFileWF.instance.readTx!func(args);
    }

    /++
    Perform an update transaction.

    Transactions can safely be nested, as long as an update transaction is never
    nested inside a read transaction.

    Parameters:
        func = (delegate to a) function that implements the transaction to be
            executed.
    +/
    ReturnType!DG updateTx(DG)(scope DG func)
    if (!is(ReturnType!DG == void) && 0 == Parameters!func.length)
    {
        return OneFileWF.instance.updateTx(func);
    }

    /// ditto
    ReturnType!func updateTx(alias func)(auto ref Parameters!func args)
    if (!is(ReturnType!func == void))
    {
        return OneFileWF.instance.updateTx!func(args);
    }

    void updateTx(DG)(scope DG func)
    if (is(ReturnType!DG == void) && 0 == Parameters!func.length)
    {
        OneFileWF.instance.updateTx(func);
    }

    void updateTx(alias func)(auto ref Parameters!func args)
    if (is(ReturnType!func == void))
    {
        OneFileWF.instance.updateTx!func(args);
    }

    alias tmMake = OneFileWF.tmMake;
    alias tmDispose = OneFileWF.tmDispose;
    alias tmAllocate = OneFileWF.tmAllocate;
    alias tmDeallocate = OneFileWF.tmDeallocate;

    alias isInTx = OneFileWF.isInTx;
}


// --- Some private helper functions
private:

void[] toChunk(T)(T* obj)
if (is(T == struct) || isScalarType!T)
{
    return cast(void[])(obj[0 .. 1]);
}

void[] toChunk(T)(T obj)
if (is(T == class))
{
    return (cast(void*)obj)[0 .. obj.classinfo.init.length];
}

