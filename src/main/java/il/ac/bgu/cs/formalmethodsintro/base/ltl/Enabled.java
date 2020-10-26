package il.ac.bgu.cs.formalmethodsintro.base.ltl;

public class Enabled<L> extends LTL<L>{

    private String inner;

    public Enabled(String inner) {
        this.setInner(inner);
    }


    public String getInner() {
        return inner;
    }

    public void setInner(String inner) {
        this.inner = "e("+inner+")";
    }

    @Override
    public String toString() {
        return inner;
    }

    /* (non-Javadoc)
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((inner == null) ? 0 : inner.hashCode());
        return result;
    }

    /* (non-Javadoc)
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (!(obj instanceof Not)) {
            return false;
        }
        Enabled<?> other = (Enabled<?>) obj;
        if (inner == null) {
            if (other.inner != null) {
                return false;
            }
        } else if (!inner.equals(other.inner)) {
            return false;
        }
        return true;
    }

}
