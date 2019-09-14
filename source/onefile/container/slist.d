/++
Linked list implementation using OneFile.

Provides roughly the same interface as Phobos' SList.

Copyright:
    Copyright © 2019 Harry T. Vennik <htvennik@gmail.com>

    Might still contain some traces of the C++ implementation, which is
    Copyright © 2017-2018
        Andreia Correia <andreia.veiga@unine.ch>
        Pedro Ramalhete <pramalhe@gmail.com>
        Pascal Felber <pascal.felber@unine.ch>
        Nachshon Cohen <nachshonc@gmail.com>

License:
    This work is published under the MIT license. See LICENSE.txt

See also:
    https://github.com/pramalhe/OneFile/blob/46eb4c757f72a5c1dbc1ded43a86eb88bcc356dd/datastructures/linkedlists/OFWFLinkedListSet.hpp
+/
module onefile.container.slist;

import onefile.stm.wf :
        isInTx, readTx, tmDispose, tmMake, TMStruct, TMType, updateTx;

import std.algorithm.iteration : each;
import std.range : ElementType, isInputRange, Take;
import std.traits : isInstanceOf, Unqual;

struct SList(T)
{
private:
    shared static struct Root
    {
    private:
        TMStruct _tm;

        TMType!(shared(Node)*) _head;
        TMType!(shared(Node)*) _tail;
        TMType!ulong _refCnt = 1UL;

    public @nogc:

        ~this()
        {
            updateTx({
                assert(0 == _refCnt);

                Node* node = head;

                _head = null;
                _tail = null;

                while (null != node)
                {
                    Node* next = node.next;
                    tmDispose(node);
                    node = next;
                }
            });
        }

        @property
        auto head() inout
        {
            return _head.pload();
        }

        @property
        void head(shared(Node)* value)
        {
            _head = value;
        }

        @property
        void head(ref typeof(_head) value)
        {
            _head = value;
        }

        @property
        auto tail() inout
        {
            return _tail.pload();
        }

        @property
        void tail(shared(Node)* value)
        {
            _tail = value;
        }

        @property
        void tail(ref typeof(_head) value)
        {
            _tail = value;
        }
    }

    shared static struct Node
    {
        private TMStruct _tm;
        TMType!(shared(Node)*) _next;
        T _content;

        @nogc:

        this(T content)
        {
            _content = content;
        }

        this(T content, shared(Node)* next)
        {
            this(content);
            _next = next;
        }

        @property
        auto next() inout
        {
            return _next.pload();
        }

        @property
        void next(shared(Node)* value)
        {
            _next = value;
        }

        @property
        void next(ref typeof(_next) value)
        {
            _next = value;
        }
    }

    // Range iterating over SList.
    //
    // A range MUST NOT outlive the transaction it was created in!
    static struct RangeImpl(N)
    if (is(shared(Unqual!N) == Node))
    {
    private:
        N* _frontNode;

    public @nogc:
        bool empty() const
        {
            return null is _frontNode;
        }

        auto front()
        {
            return _frontNode._content;
        }

        void popFront()
        {
            _frontNode = _frontNode.next;
        }

        void seekToSameAs(in Range r)
        {
            if (r.empty)
            {
                this._frontNode = null;
                return;
            }

            while (this._frontNode !is r._frontNode)
            {
                this.popFront();
                assert(!this.empty, "Invalid seek: r is before this, or " ~
                        "either range is outdated, or these ranges are not " ~
                        "from the same list");
            }
        }

        void seekToOneBefore(R)(in R r)
        if (isInstanceOf!(SList.RangeImpl, R))
        {
            while (this._frontNode.next !is r._frontNode)
            {
                this.popFront();
                assert(!this.empty, "Invalid seek: r is before this, or " ~
                        "either range is outdated, or these ranges are not " ~
                        "from the same list");
            }
        }

        @property
        RangeImpl save()
        {
            return this;
        }
    }

    alias Range = RangeImpl!Node;
    alias ConstRange = RangeImpl!(const Node);

    template isValidStuff(Stuff)
    {
        import std.range.primitives : isInputRange, ElementType;
        import std.traits : isImplicitlyConvertible;

        enum isValidStuff = (isImplicitlyConvertible!(Stuff, T)) ||
                (isInputRange!Stuff && isImplicitlyConvertible!(
                ElementType!Stuff, T));
    }

    shared(Root)* _root;

    @nogc:

    void initialize()
    {
        if (null !is _root)
            return;

        _root = updateTx!({
            return tmMake!(shared Root)();
        });
    }

public:
    this(Stuff)(Stuff stuff)
    if (isValidStuff!Stuff)
    {
        insertFront(stuff);
    }

    this(this)
    {
        if (null is _root)
            return;

        updateTx({
            _root._refCnt += 1;
        });
    }

    ~this()
    {
        if (null is _root)
            return;

        updateTx({
            auto lRefCnt = (_root._refCnt -= 1);

            if (0 == lRefCnt)
                tmDispose(_root);
        });

        _root = null;
    }

    void clear()
    {
        if (null is _root)
            return;

        updateTx({
            remove(this[]);
        });
    }

    @property
    bool empty() const
    {
        return null is _root || readTx!((in ref SList me) {
            return null is me._root.head;
        }) (this);
    }

    @property
    SList dup()
    {
        // Not using a copy constructor because we need to slice this, which
        // must be done inside a transaction and we cannot return an SList from
        // a transaction.

        SList l;

        updateTx!((ref SList me, ref SList l) {
            l.insertFront(me[]);
        }) (this, l);

        return l;
    }

    @property
    T front() const
    in (!empty)
    {
        return readTx({
            return cast() _root.head._content;
        });
    }

    bool opEquals(const SList rhs) const
    {
        return readTx({
            import std.algorithm.comparison : equal;
            return this[].equal(rhs[]);
        });
    }

    SList opBinary(string op, Stuff)(Stuff rhs)
    if (op == "~" && is(typeof(SList(rhs))))
    {
        updateTx({
            import std.range : chain;
            return SList(this[].chain(rhs));
        });
    }

    SList opBinaryRight(string op, Stuff)(Stuff lhs)
    if (op == "~" && !is(typeof(lhs.opBinary!"~"(this))) && is(typeof(SList(lhs))))
    {
        updateTx({
            import std.range : chain;
            return SList(lhs.chain(this[]));
        });
    }

    Range opSlice() return
    in (isInTx, "Cannot slice when not in a transaction")
    {
        return Range(null !is _root ? _root.head : null);
    }

    ConstRange opSlice() const return
    in (isInTx, "Cannot slice when not in a transaction")
    {
        return ConstRange(null !is _root ? _root.head : null);
    }

    /++
        Inserts stuff after range, which must be a range previously extracted
        from this container. Given that all ranges for a list end at the end of
        the list, this function essentially appends to the list if range is not
        empty. If range is empty, stuff will be inserted at the front of the
        list.

        Returns: the number of elements inserted
    +/
    size_t insertAfter(R, Stuff)(R range, Stuff stuff)
    if (isInstanceOf!(RangeImpl, R) && isValidStuff!Stuff)
    in (isInTx && (!this.empty || range.empty))
    {
        static if (isInputRange!Stuff)
            if (stuff.empty)
                return;

        if (range.empty)
            return this.insertFront(stuff);

        return this.insertBack(stuff);
    }

    /++
        Similar to insertAfter above, but accepts a range bounded in count, and
        thus may insert somewhere in the middle of the list. For fast insertions
        after a specified position `r`, use `insertAfter(take(r, 1), stuff)`.

        Returns: the number of elements inserted
    +/
    size_t insertAfter(R, Stuff)(Take!R range, Stuff stuff)
    if (isInstanceOf!(RangeImpl, R) && isValidStuff!Stuff)
    in (isInTx && (!this.empty || range.empty))
    {
        import std.range.primitives : popFrontN;

        static if (isInputRange!Stuff)
            if (stuff.empty)
                return;

        if (range.empty)
            return this.insertFront(stuff);

        range.popFrontN(range.maxLength - 1);

        if (range.empty || range.source._frontNode is _root.tail)
            return this.insertBack(stuff);

        TMType!(shared(Node)*)* prevNext;

        version (assert)
        {
            // If asserts are enabled we do a seek to assert that range
            // references a node that is part of this list.
            auto rb = this[];
            rb.seekToSameAs(range.source);
            prevNext = &rb._frontNode._next;
        }
        else
        {
            // If asserts are disabled, let's just trust range so we can
            // optimize for performance by skipping the seek.
            prevNext = &range.source._frontNode._next;
        }

        static if (isInputRange!Stuff)
        {
            size_t n;
            Node* node;
            Node* afterStuff = *prevNext;

            // afterStuff can not be null, because in that case, we should have
            // called insertBack. Let's assert that, so we can safely assume we
            // do not have to update the tail pointer.
            assert (null !is afterStuff);

            stuff.each!({
                node = tmMake!Node(stuff);
                *prevNext = node;
                prevNext = &node._next;
                ++n;
            });

            *prevNext = afterStuff;

            return n;
        }
        else
        {
            *prevNext = tmMake!Node(stuff, (*prevNext).pload());
            return 1;
        }
    }

    size_t insertBack(Stuff)(Stuff stuff)
    if (isValidStuff!Stuff)
    {
        initialize();

        return updateTx({
            size_t n;
            auto prevNext = !empty ? &_root.tail._next : &_root._head;
            Node* node;

            static if (isInputRange!Stuff)
            {
                if (stuff.empty)
                    return 0;

                stuff.each!((ElementType!Stuff el) {
                    node = tmMake!Node(el);
                    *prevNext = node;
                    prevNext = &node._next;
                    ++n;
                });
            }
            else
            {
                node = tmMake!Node(stuff);
                *prevNext = node;
                n = 1;
            }

            _root._tail = node;
            return n;
        });
    }

    size_t insertFront(Stuff)(Stuff stuff)
    if (isValidStuff!Stuff)
    {
        initialize();

        return updateTx({
            immutable bool wasEmpty = empty;
            size_t n;
            Node* node;

            static if (isInputRange!Stuff)
            {
                auto prevNext = &_root._head;

                stuff.each!((ElementType!Stuff el) {
                    node = tmMake!Node(el, (*prevNext).pload());
                    *prevNext = node;
                    prevNext = &node._next;
                    ++n;
                });
            }
            else
            {
                node = tmMake!Node(stuff, _root.head);
                _root._head = node;
                n = 1;
            }

            if (wasEmpty)
                _root._tail = node;

            return n;
        });
    }

    void removeFront()
    in (!empty)
    {
        updateTx({
            Node* oldHead = _root.head;

            if (null !is oldHead)
            {
                _root.head = oldHead.next;
                tmDispose(oldHead);
            }
        });
    }

    void removeFront(size_t howMany)
    in (!empty)
    {
        updateTx({
            import std.range : take;
            linearRemove(this[].take(howMany));
        });
    }

    alias stableRemoveFront = removeFront;

    void linearRemove(scope Range r)
    in (isInTx && !empty)
    {
        if (r.empty)
            return;

        Node* ltail = _root.tail;

        if (_root.head is r._frontNode)
        {
            _root.head = null;
            _root.tail = null;
        }
        else
        {
            auto rb = this[];
            rb.seekToOneBefore(r);
            _root.tail = rb._frontNode;
        }

        while (!r.empty)
        {
            auto prev = r._frontNode;
            r.popFront();
            tmDispose(prev);
        }
    }

    void linearRemove(scope Take!Range r)
    in (isInTx && !empty)
    {
        if (r.empty)
            return;

        TMType!(Node*)* linkPtr;
        Node* possibleTail;

        if (_root.head is r.source._frontNode)
            linkPtr = &_root._head;
        else
        {
            auto rb = this[];
            rb.seekToOneBefore(r.source);
            linkPtr = &rb._frontNode._next;
            possibleTail = rb._frontNode;
        }

        while (!r.empty)
        {
            auto prev = r.source._frontNode;
            r.popFront();
            tmDispose(prev);
        }

        *linkPtr = r.source._frontNode;

        if (null is r.source._frontNode)
            _root._tail = possibleTail;
    }

    alias remove = linearRemove;

    bool linearRemoveElement(T value)
    {
        return updateTx({
            if (empty)
                return false;

            auto prevNext = &_root._head;
            Node* node = prevNext.pload();

            while (node !is null)
            {
                if (value == node._content)
                {
                    *prevNext = node._next;
                    tmDispose(node);
                    return true;
                }

                prevNext = &node._next;
                node = node.next;
            }

            return false;
        });
    }

    alias removeElement = linearRemoveElement;

    bool removeAll(T value)
    {
        return updateTx({
            if (empty)
                return false;

            auto prevNext = &_root._head;
            Node* node = prevNext.pload();
            bool isChanged;

            while (node !is null)
            {
                auto next = node.next;

                if (value == node._content)
                {
                    *prevNext = next;
                    tmDispose(node);
                    isChanged = true;
                }
                else
                    prevNext = &node._next;

                node = next;
            }

            return isChanged;
        });
    }

    void reverse()
    {
        if (!empty)
            updateTx({
                Node* prev;
                Node* lhead = _root.head;

                _root.tail = lhead;

                while (lhead)
                {
                    auto next = lhead.next;
                    lhead._next = prev;
                    prev = lhead;
                    lhead = next;
                }

                _root.head = prev;
            });
    }
}

@nogc unittest
{
    import std.range : iota, take;
    import std.algorithm.searching : canFind, count, find;

    alias List = SList!uint;

/+
    alias printList = readTx!((ref List l) {
        import core.stdc.stdio : printf;

        uint i;
        printf("l = [");

        l[].each!((v) {
            printf("%4d", v);
            i = v;
        });

        printf(" ]\n");
        return 0;
    });
+/

    auto l = List(iota(1, 101));

    assert(100 == readTx({
        uint n;
        l[].each!((v) {
            ++n;
            assert(v == n);
        });

        return n;
    }));

    assert(readTx(() => l[].canFind(50)));
    l.linearRemoveElement(50);
    assert(!readTx(() => l[].canFind(50)));

    l.reverse();

    assert(50 == updateTx({
        auto r = l[].find(51);
        l.insertAfter(r.take(1), 50);
        r.popFront();
        return r.front;
    }));

    assert(0 == readTx({
        uint n = 100;
        l[].each!((v) {
            assert(v == n);
            --n;
        });

        return n;
    }));

    l.insertBack(iota(2, 101));

    assert(199 == readTx(() => l[].count()));

    assert(true == l.removeAll(100));

    assert(197 == readTx(() => l[].count()));
}

unittest {
    import core.atomic;
    import core.thread : Thread, thread_joinAll;

    import onefile.stm.wf : ThreadRegistry;

    debug (PRINTF) import std.stdio : write, writef, writefln, writeln;

    alias List = SList!uint;

    List l;
    shared static bool t2Done;

    new Thread(() @nogc {
        import core.time : msecs;

        scope(exit) ThreadRegistry.deregisterMe();

        debug (PRINTF) writeln("Thread 1 delaying start...");

        Thread.sleep(50.msecs);

        debug (PRINTF) writeln("Thread 1 starts work");

        for (uint i = 100; i > 0; i -= 2)
        {
            l.insertFront(i);
            debug (PRINTF) writefln("Thread 1 inserted %d", i);

            if (0 == i % 10)
                Thread.yield();
        }

        debug (PRINTF) writeln("Thread 1 done!");
    }).start();

    new Thread(() @nogc {
        scope(exit) ThreadRegistry.deregisterMe();

        debug (PRINTF) writeln("Thread 2 entering wait loop");

        while (l.empty) { }

        debug (PRINTF) writeln("Thread 2 starts work");

        bool f, m;
        uint i;

        do
        {
            ++i;
            m = false;

            if (2 == l.front)
            {
                l.insertFront(1);
                debug (PRINTF) writeln("Thread 2 inserted 1");
                f = true;
            }

            updateTx(() @nogc {
                for (auto r = l[]; !r.empty; r.popFront())
                {
                    auto s = r;
                    s.popFront();

                    auto j = r.front + 1;
                    j += (~j & 1);
                    if (j < 100 && (s.empty || (s.front > j)))
                    {
                        import std.range : take;

                        l.insertAfter(r.take(1), j);
                        debug (PRINTF) writefln("Thread 2 inserted %d", j);
                        m = true;
                    }
                }
            });

            debug (PRINTF) writefln("Thread 2 iteration %4d done.", i);

            if (!m)
                Thread.yield();
        }
        while(m || !f);

        debug (PRINTF) writeln("Thread 2 done!");

        t2Done.atomicStore(true);
    }).start();

    new Thread(() @nogc {
        scope(exit) ThreadRegistry.deregisterMe();

        debug (PRINTF) writeln("Thread 3 entering wait loop");

        while (l.empty) { }

        debug (PRINTF) writeln("Thread 3 starts work");

        bool allowStop, m;
        uint i;

        do
        {
            ++i;
            allowStop = t2Done.atomicLoad();
            m = false;

            updateTx(() @nogc {
                for (auto r = l[]; !r.empty; r.popFront())
                {
                    auto j = r.front;

                    if (0 == j % 3)
                    {
                        import std.range : take;

                        l.remove(r.take(1));
                        debug (PRINTF) writefln("Thread 3 removed %d", j);
                        m = true;
                    }
                }
            });

            debug (PRINTF) writefln("Thread 3 iteration %4d done.", i);

            if (!m)
                Thread.yield();
        }
        while(m || !allowStop);

        debug (PRINTF) writeln("Thread 3 done!");
    }).start();

    thread_joinAll();

    {
        import std.format : format;

        assert (!l.empty, "List is empty. Inserts don't work, apparently.");

        assert(readTx(() @nogc {
            uint i;
            bool correct = true;

            foreach (e; l[])
            {

                debug (PRINTF)
                {
                    ++i;

                    if (0 == i % 3)
                    {
                        write("   -");

                        if (0 == i % 10)
                            writeln();

                        ++i;
                    }

                    writef(" %3d", e);

                    if (0 == i % 10)
                        writeln();
                }
                else
                    i += (2 == i % 3) ? 2 : 1;

                correct = correct && e == i;
            }

            return correct;
        }), "List ain't correct");
    }
}
