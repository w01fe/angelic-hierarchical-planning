/**
 *   Copyright (c) Rich Hickey. All rights reserved.
 *   The use and distribution terms for this software are covered by the
 *   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
 *   which can be found in the file epl-v10.html at the root of this distribution.
 *   By using this software in any fashion, you are agreeing to be bound by
 * 	 the terms of this license.
 *   You must not remove this notice, or any other, from this software.
 *
 *   Created largely from from ASeq.java by Jason Wolfe.
 **/

package edu.berkeley.angel.util;
import clojure.lang.*;

import java.util.*;

public class DelayedSeq extends Obj implements IPersistentList, Collection{
	final private static ISeq sentinel = new Cons(null, null);
	private IFn f;
	private ISeq seq;
	
	public DelayedSeq(IFn f){
		this.f = f;
		this.seq = sentinel;
	}
	
	public DelayedSeq(IPersistentMap meta, ISeq seq){
		super(meta);
		this.f = null;
		this.seq = seq;
	}	

	public DelayedSeq withMeta(IPersistentMap meta){
		if(meta != meta())
			return new DelayedSeq(meta, seq);
		return this;
	}
	
	public ISeq seq(){
		if (seq == sentinel) {	
			try {
				seq = RT.seq(f.invoke());
			} catch(Exception ex) {
				throw new RuntimeException(ex);
			}
			f = null;
		} 
		return seq;
	}

	// Begin copies from ASeq
	transient int _hash = -1;

	public String toString(){
		return RT.printString(this);
	}

	public IPersistentCollection empty(){
		return null;
	}

	public boolean equals(Object obj){

		if(!(obj instanceof Sequential))
			return false;
		ISeq ms = ((IPersistentCollection) obj).seq();
		for(ISeq s = seq(); s != null; s = s.rest(), ms = ms.rest())
			{
			if(ms == null || !Util.equal(s.first(), ms.first()))
				return false;
			}
		if(ms != null)
			return false;

		return true;
	}

	public int hashCode(){
		if(_hash == -1)
			{
			int hash = 0;
			for(ISeq s = seq(); s != null; s = s.rest())
				{
				hash = Util.hashCombine(hash, Util.hash(s.first()));
				}
			this._hash = hash;
			}
		return _hash;
	}

	//public Object reduce(IFn f) throws Exception{
	//	Object ret = first();
	//	for(ISeq s = rest(); s != null; s = s.rest())
	//		ret = f.invoke(ret, s.first());
	//	return ret;
	//}
	//
	//public Object reduce(IFn f, Object start) throws Exception{
	//	Object ret = f.invoke(start, first());
	//	for(ISeq s = rest(); s != null; s = s.rest())
	//		ret = f.invoke(ret, s.first());
	//	return ret;
	//}

	public Object peek(){
		return seq().first();
	}

	public IPersistentStack pop(){
		throw new UnsupportedOperationException("DelayedSeqs cannot be popped.");
	}

	public int count(){
		int i = 0;
		for(ISeq s = seq(); s != null; s = s.rest(), i++)
			;
		return i;
	}

	public ISeq cons(Object o){
		return new Cons(o, seq());
	}

	// java.util.Collection implementation

	public Object[] toArray(){
		return RT.seqToArray(seq());
	}

	public boolean add(Object o){
		throw new UnsupportedOperationException();
	}

	public boolean remove(Object o){
		throw new UnsupportedOperationException();
	}

	public boolean addAll(Collection c){
		throw new UnsupportedOperationException();
	}

	public void clear(){
		throw new UnsupportedOperationException();
	}

	public boolean retainAll(Collection c){
		throw new UnsupportedOperationException();
	}

	public boolean removeAll(Collection c){
		throw new UnsupportedOperationException();
	}

	public boolean containsAll(Collection c){
		for(Object o : c)
			{
			if(!contains(o))
				return false;
			}
		return true;
	}

	public Object[] toArray(Object[] a){
		if(a.length >= count())
			{
			ISeq s = seq();
			for(int i = 0; s != null; ++i, s = s.rest())
				{
				a[i] = s.first();
				}
			if(a.length > count())
				a[count()] = null;
			return a;
			}
		else
			return toArray();
	}

	public int size(){
		return count();
	}

	public boolean isEmpty(){
		return count() == 0;
	}

	public boolean contains(Object o){
		for(ISeq s = seq(); s != null; s = s.rest())
			{
			if(Util.equal(s.first(), o))
				return true;
			}
		return false;
	}


	public Iterator iterator(){
		return new SeqIterator(seq());
	}

	public IStream stream() throws Exception {
	    return new Stream(seq());
	}

	    static class Stream implements IStream{
	    ISeq s;

	    public Stream(ISeq s) {
	        this.s = s;
	    }

	    synchronized public Object next() throws Exception {
	        if(s != null)
	            {
	            Object ret = s.first();
	            s = s.rest();
	            return ret;
	            }
	        return RT.eos();
	    }
	}
}

