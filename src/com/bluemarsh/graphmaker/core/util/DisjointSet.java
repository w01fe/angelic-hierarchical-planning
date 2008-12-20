/*
 * The contents of this file are subject to the terms of the Common Development
 * and Distribution License (the License). You may not use this file except in
 * compliance with the License.
 *
 * You can obtain a copy of the License at http://www.netbeans.org/cddl.html
 * or http://www.netbeans.org/cddl.txt.
 *
 * When distributing Covered Code, include this CDDL Header Notice in each file
 * and include the License file at http://www.netbeans.org/cddl.txt.
 * If applicable, add the following below the CDDL Header, with the fields
 * enclosed by brackets [] replaced by your own identifying information:
 * "Portions Copyrighted [year] [name of copyright owner]"
 *
 * The Original Software is GraphMaker. The Initial Developer of the Original
 * Software is Nathan L. Fiedler. Portions created by Nathan L. Fiedler
 * are Copyright (C) 1999-2008. All Rights Reserved.
 *
 * Contributor(s): Nathan L. Fiedler.
 *
 * $Id: DisjointSet.java 12 2008-05-10 08:26:17Z nathanfiedler $
 */

package com.bluemarsh.graphmaker.core.util;

import java.lang.reflect.Array;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.List;
import java.util.ListIterator;
import java.util.NoSuchElementException;

/**
 * Implements a disjoint set data type. The elements of the set begin
 * unconnected with each element in its own set. You can join elements
 * together into larger sets of elements, where every element has a root
 * element. You can check if two elements are in the same set by testing
 * if their root elements are the same, using the find method. Each element
 * in the set can have an object associated with it. Use the set() and get()
 * methods to store objects in the set. Each object will be associated with
 * an element based on the offset at which the object is stored.
 *
 * <p><b>Note that this implementation is not synchronized.</b> If multiple
 * threads access a set concurrently, and at least one of the threads modifies
 * the set, it <i>must</i> be synchronized externally. This is typically
 * accomplished by synchronizing on some object that naturally encapsulates
 * the set. If no such object exists, the set should be "wrapped" using the
 * <code>Collections.synchronizedList</code> method. This is best done at
 * creation time, to prevent accidental unsynchronized access to the set:</p>
 *<pre>
 *     List l = Collections.synchronizedList(new DisjointSet(...));
 *</pre>
 *
 * @author  Nathan Fiedler
 */
public class DisjointSet implements Cloneable, List {
    /** The disjoint set of elements. The numbers stored in this array
     * point to the root element of the array element. If the number is
     * less than zero then it is a root and its absolute value is the
     * height of the tree. */
    private int[] disjointSet;
    /** The set of objects represented in the disjoint set. */
    private Object[] objectSet;
    /** Number of disjoint trees in the set. */
    private int treeCount;
    /** Number of non-null elements stored in the set. */
    private int elementCount;

    /**
     * Creates a new instance of DisjointSet.
     *
     * @param  size  number of elements to be stored in the set.
     */
    public DisjointSet(int size) {
        if (size < 0) {
            throw new IllegalArgumentException("size cannot be negative");
        }
        init(size);
    }

    /**
     * This method is not supported.
     *
     * @param  o  object to be added.
     */
    public boolean add(Object o) {
        throw new UnsupportedOperationException();
    }

    /**
     * This method is not supported.
     */
    public void add(int index, Object element) {
        throw new UnsupportedOperationException();
    }

    /**
     * This method is not supported.
     */
    public boolean addAll(Collection c) {
        throw new UnsupportedOperationException();
    }

    /**
     * This method is not supported.
     */
    public boolean addAll(int index, Collection c) {
        throw new UnsupportedOperationException();
    }

    public void clear() {
        init(objectSet.length);
    }

    @Override
    public Object clone() {
        try {
            return super.clone();
        } catch (CloneNotSupportedException cnse) {
            // This cannot happen
            cnse.printStackTrace();
            return null;
        }
    }

    public boolean contains(Object o) {
        for (int ii = 0; ii < objectSet.length; ii++) {
            if (objectSet[ii] != null && o.equals(objectSet[ii])) {
                return true;
            }
        }
        return false;
    }

    public boolean containsAll(Collection c) {
        Iterator iter = c.iterator();
        while (iter.hasNext()) {
            if (!contains(iter.next())) {
                return false;
            }
        }
        return true;
    }

    @Override
    public boolean equals(Object o) {
        return o == this;
    }

    /**
     * Find the root of the given element. You can use this to test if
     * two elements are in the same set by testing if their roots are
     * the same. Running time: O(n)
     *
     * @param  index  element to find the root of.
     * @return  index of the root element.
     * @exception  IndexOutOfBoundsException
     *             if 'index' is out of bounds.
     */
    public int find(int index) {
        // Handle case where index is out of bounds.
        if (index < 0 || index > disjointSet.length) {
            throw new IndexOutOfBoundsException();
        }
        // If the element value is less than zero then we've found the
        // root. Otherwise keep looking by calling ourselves recursively.
        // This will automatically shorten the tree.
        if (disjointSet[index] < 0) {
            return(index);
        } else {
            disjointSet[index] = find(disjointSet[index]);
            return(disjointSet[index]);
        }
    }

    public Object get(int index) {
        if (index < 0 || index >= objectSet.length) {
            throw new IndexOutOfBoundsException();
        }
        return objectSet[index];
    }

    @Override
    public int hashCode() {
        return System.identityHashCode(this);
    }

    public int indexOf(Object o) {
        return indexOf(o, 0);
    }

    /**
     * Find the index in the set of the given object.
     *
     * @param  o  object to look for in set.
     * @param  i  starting offset to begin searching from.
     * @return  the zero-based offset into set where object was first
     *          found after starting index index, or -1 if not found.
     */
    public int indexOf(Object o, int i) {
        for (int idx = i; idx < objectSet.length; idx++) {
            if (objectSet[idx].equals(o)) {
                return idx;
            }
        }
        return -1;
    }

    /**
     * Initialize the data structure to hold <code>size</code> elements.
     *
     * @param  size  number of elements to hold.
     */
    protected void init(int size) {
        // Simply allocate an integer array of the given size.
        // Be sure to clear out the set, making all the elements
        // the roots of their own individual sets (i.e. they are
        // in trees of height one).
        disjointSet = new int[size];
        objectSet = new Object[size];
        for (int i = 0; i < size; i++) {
            disjointSet[i] = -1;
        }
        treeCount = size;
        elementCount = 0;
    }

    public boolean isEmpty() {
        return elementCount == 0;
    }

    public Iterator iterator() {
        return new Iter(objectSet);
    }

    public int lastIndexOf(Object o) {
        for (int ii = objectSet.length - 1; ii > -1; ii--) {
            if (objectSet[ii].equals(o)) {
                return ii;
            }
        }
        return -1;
    }

    public ListIterator listIterator() {
        return new ListIter(objectSet);
    }

    public ListIterator listIterator(int index) {
        if (index < 0 || index >= objectSet.length) {
            throw new IndexOutOfBoundsException();
        }
        return new ListIter(objectSet, index);
    }

    /**
     * Returns the total number of elements in this set. This number
     * is the same throughout the life of the set and is equal to the
     * number passed to the constructor.
     *
     * @return  number of elements in the set
     */
    public int numberOfElements() {
        return elementCount;
    }

    /**
     * Returns the number of disjoint elements in the set. If all the
     * elements are separate then this method will return the number of
     * elements in the entire set. If all the elements are joined into
     * one tree then this method will return 1.
     *
     * @return  number of trees in the set
     */
    public int numberOfTrees() {
        return treeCount;
    }

    /**
     * This method is not supported.
     */
    public Object remove(int index) {
        throw new UnsupportedOperationException();
    }

    /**
     * This method is not supported.
     */
    public boolean remove(Object o) {
        throw new UnsupportedOperationException();
    }

    /**
     * This method is not supported.
     */
    public boolean removeAll(Collection c) {
        throw new UnsupportedOperationException();
    }

    /**
     * This method is not supported.
     */
    public boolean retainAll(Collection c) {
        throw new UnsupportedOperationException();
    }

    public Object set(int index, Object element) {
        if (index < 0 || index >= objectSet.length) {
            throw new IndexOutOfBoundsException();
        }
        Object old = objectSet[index];
        objectSet[index] = element;
        if (element != null) {
            // Increment the number of non-null elements.
            elementCount++;
        } else if (old != null) {
            // Decrement the number of non-null elements.
            elementCount--;
        }
        return old;
    }

    public int size() {
        return numberOfElements();
    }

    @SuppressWarnings("unchecked")
    public List subList(int fromIndex, int toIndex) {
        ArrayList list = new ArrayList(toIndex - fromIndex);
        for (int ii = fromIndex; ii < toIndex; ii++) {
            list.add(objectSet[ii]);
        }
        return list;
    }

    public Object[] toArray() {
        Object[] copy = new Object[objectSet.length];
        System.arraycopy(objectSet, 0, copy, 0, objectSet.length);
        return copy;
    }

    public Object[] toArray(Object a[]) {
        // Get the elements into an array.
        Object[] result = toArray();

        // Copy the elements into the array of the desired type.
        int size = size();
        if (a.length < size) {
            a = (Object[]) Array.newInstance(
                a.getClass().getComponentType(), size);
        }
        for (int ii = 0; ii < size; ii++) {
            a[ii] = result[ii];
        }
        if (a.length > size) {
            a[size] = null;
        }
        return a;
    }

    @Override
    public String toString() {
        StringBuffer sb = new StringBuffer("DisjointSet=[");
        sb.append(objectSet[0]);
        for (int i = 1; i < objectSet.length; i++) {
            sb.append(", ");
            sb.append(objectSet[i]);
        }
        sb.append("]");
        return sb.toString();
    }

    /**
     * Join two trees together within the set. It makes the tree that is
     * less deep become a child of the deeper tree. This keeps the
     * resulting tree as shallow as possible thus improving the runtime
     * of the find operation. This operation decrements the number of
     * disjoint trees by one.
     *
     * @param  root1  root of the first tree.
     * @param  root2  root of the second tree.
     */
    public void union(int root1, int root2) {
        // Check for invalid input.
        if (root1 < 0 || root1 > disjointSet.length) {
            throw new IndexOutOfBoundsException("root1 out of bounds");
        }
        if (root2 < 0 || root2 > disjointSet.length) {
            throw new IndexOutOfBoundsException("root2 out of bounds");
        }
        // Make sure the passed indices are in fact roots.
        // Exit immediately if the roots are the same.
        root1 = find(root1);
        root2 = find(root2);
        if (root1 == root2) {
            return;
        }

        // If second tree is deeper, make it the root of the
        // first tree. Else, if the two trees are of equal
        // depth, make the first tree the root of the second
        // tree and update the depth appropriately.
        if (disjointSet[root2] < disjointSet[root1]) {
            // Root2 is deeper set, make it the new root. This does
            // not require any changes to the height of either tree.
            disjointSet[root1] = root2;
        } else {
            // They're the same height, so update appropriately.
            if (disjointSet[root2] == disjointSet[root1]) {
                // Set the height of the tree by decrementing by one.
                disjointSet[root1]--;
            }
            // Make root1 the new root.
            disjointSet[root2] = root1;
        }
        // Decrement number of disjoint trees in set.
        treeCount--;
    }

    /**
     * Iterates a disjoint set. This iterator does not care if the
     * elements within the disjoint set change, as it really does not
     * matter.
     */
    protected class Iter implements Iterator {
        /** Reference to the object set. */
        protected Object[] set;
        /** Index within the set. */
        protected int index;

        /**
         * Constructs an iterator for the given object array.
         *
         * @param  set  object set to iterate over.
         */
        public Iter(Object[] set) {
            this.set = set;
        }

        public boolean hasNext() {
            return index < set.length;
        }

        public Object next() {
            if (hasNext()) {
                return set[index++];
            } else {
                throw new NoSuchElementException();
            }
        }

        public void remove() {
            throw new UnsupportedOperationException();
        }
    }

    /**
     * Iterates a disjoint set. This iterator does not care if the
     * elements within the disjoint set change. It really does not
     * matter anyway.
     */
    protected class ListIter extends Iter implements ListIterator {

        /**
         * Constructs an iterator for the given object array.
         *
         * @param  set  object set to iterate over.
         */
        public ListIter(Object[] set) {
            this(set, 0);
        }

        /**
         * Constructs an iterator for the given object array.
         *
         * @param  set  object set to iterate over.
         * @param  idx  initial index into the set.
         */
        public ListIter(Object[] set, int idx) {
            super(set);
            index = idx;
        }

        /**
         * This method is not supported.
         *
         * @param  o  object to be added.
         */
        public void add(Object o) {
            throw new UnsupportedOperationException();
        }

        public boolean hasPrevious() {
            return index > 0;
        }

        public int nextIndex() {
            return index;
        }

        public Object previous() {
            if (hasPrevious()) {
                return set[--index];
            } else {
                throw new NoSuchElementException();
            }
        }

        public int previousIndex() {
            return index - 1;
        }

        /**
         * This method is not supported.
         */
        @Override
        public void remove() {
            throw new UnsupportedOperationException();
        }

        public void set(Object o) {
            set[index] = o;
        }
    }
}
