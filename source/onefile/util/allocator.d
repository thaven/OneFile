/*
 * Copyright 2019
 *   Harry T. Vennik <htvennik@gmail.com>
 *
 * This work is published under the MIT license. See LICENSE.txt
 */
module onefile.util.allocator;

version (Have_stdx_allocator)
{
    package(onefile) import stdx.allocator : dispose, expandArray, make, makeArray, shrinkArray;
    import stdx.allocator.mallocator : AlignedMallocator;
}
else
{
    package(onefile) import std.experimental.allocator :
            dispose, expandArray, make, makeArray, shrinkArray;
    import std.experimental.allocator.mallocator : AlignedMallocator;
}

package(onefile) alias allocator = AlignedMallocator.instance;
