/*
 * Copyright 2019
 *   Harry T. Vennik <htvennik@gmail.com>
 *
 * This work is published under the MIT license. See LICENSE.txt
 */
module onefile.internal.allocator;

version (Have_stdx_allocator)
{
    package(onefile) import stdx.allocator;
    import stdx.allocator.mallocator : AlignedMallocator;
}
else
{
    package(onefile) import std.experimental.allocator;
    import std.experimental.allocator.mallocator : AlignedMallocator;
}

package(onefile):

alias allocator = AlignedMallocator.instance;

template isNoGcDestroyable(T)
if (is(T == class))
{
    import std.traits : hasFunctionAttributes;

    static if (__traits(hasMember, T, "__dtor"))
        enum bool isNoGcDestroyable = hasFunctionAttributes!(T.__dtor, "@nogc");
    else
        enum bool isNoGcDestroyable = true;
}

@nogc
void disposeNoGc(A, T)(auto ref A alloc, auto ref T obj)
if (is(T == class))
{
    import std.traits : fullyQualifiedName, hasFunctionAttributes;

    static assert(hasFunctionAttributes!(A.deallocate, "@nogc"),
            "Cannot use disposeNoGc with GC reliant allocator");

    static assert(isNoGcDestroyable!T,
            "Destructor of " ~ fullyQualifiedName!T ~ "is not @nogc");

    (cast(void function(ref A, ref T) @nogc) (ref A alloc, ref T obj) {
        alloc.dispose(obj);
    })(alloc, obj);
}

