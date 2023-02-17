import java.util.Arrays;

class KnuthMorrisPratt {
    public static void main(String[] args) {
        char[] pattern = "AAAAA".toCharArray();
        char[] text = "AAABAABAABBAAB".toCharArray();
        int[] border = border(pattern);
        //System.out.println(Arrays.toString(border));

        pattern = "AABAA".toCharArray();
        text = "AAABAABAABBAAB".toCharArray();
        border = border(pattern);
        //System.out.println(Arrays.toString(border));
        //System.out.println(Arrays.toString(border));
        boolean[] matches = search(text, pattern, border);
        //System.out.println(Arrays.toString(matches));

        pattern = "A".toCharArray();
        text = "AAAA".toCharArray();
        border = border(pattern);
        //System.out.println(Arrays.toString(border));
        matches = naiveSearch(text, pattern);
        matches = search(text, pattern, border);
        //System.out.println(Arrays.toString(matches));

        pattern = "ABBB".toCharArray();
        text = "ABBAXXXX".toCharArray();
        border = border(pattern);
        //System.out.println(Arrays.toString(border));
        matches = search(text, pattern, border);
    }
    
    public static int[] border(char[] pattern) {
        int[] b = new int[pattern.length + 1];
        b[0] = -1;
        int i = b[0];
        for (int j = 1; j < b.length; j++) {
            while (i >= 0 && pattern[i] != pattern[j - 1]) {
                i = b[i];
            }
            i++;
            b[j] = i;
        }
        return b;
    }

    /*@ public normal_behaviour
      @  requires text != null && pattern != null;
      @  requires text.length >= pattern.length;
      @  requires pattern.length > 0;
      @  assignable \nothing;
      @  ensures \result.length == text.length;
      @  ensures (\forall int i; 0 <= i && i <= text.length - pattern.length; \result[i] == (\forall int j; 0 <= j && j < pattern.length; text[i + j] == pattern[j]));
      @*/
    public static boolean[] naiveSearch(char[] text, char[] pattern) {
        boolean[] matched = new boolean[text.length];

        /*@ loop_invariant
         @  i >= 0 && i <= text.length - pattern.length + 1 &&
         @   (\forall int k; 0 <= k && k < i; matched[k] == (\forall int j; 0 <= j && j < pattern.length; text[k + j] == pattern[j]));
         @
         @  assignable matched[*];
         @  decreases text.length - i;
         @*/
        for (int i = 0; i <= text.length - pattern.length; i++) {
            int j = 0;
            boolean mismatch = false;
            /*@ loop_invariant
             @   j >= 0 && j <= pattern.length &&
             @   ((!mismatch) ==> (\forall int k; 0 <= k && k < j; text[i + k] == pattern[k])) &&
             @   (mismatch ==> (\exists int k; 0 <= k && k < pattern.length; text[i + k] != pattern[k]));
             @
             @  assignable j, mismatch;
             @  decreases pattern.length - j;
             @*/
            for (j = 0; j < pattern.length; j++) {
                if (text[i + j] != pattern[j]) {
                    mismatch = true;
                    break;
                }
            }
            matched[i] = !mismatch;
        }
        return matched;
    }

    /**
          @  requires (\forall int j; 0 <= j && j < border.length;
      @    (\forall int b; 0 <= b && b >= border[j] && b <= j - 1;
      @    (\exists int i; 0 <= i && i < b; pattern[i] != pattern[j - border[j] + i])));
     */

    /**
     * @  requires (\forall int j; 0 < j && j < border.length;
     *       @    (\forall int i; i >= border[j] && i <= j - 1;
     *       @    (\exists int k; 0 <= k && k < i; pattern[k] != pattern[j - i + k])));
     *
     */

    /*@ public normal_behaviour
      @  requires text != null && pattern != null && border != null;
      @  requires text.length >= pattern.length;
      @  requires pattern.length > 0;
      @  requires border.length == pattern.length + 1;
      @  requires (\forall int j; 0 <= j && j < border.length;
      @    (\forall int i; 0 <= i && i < border[j]; pattern[i] == pattern[j - border[j] + i]));
      @  requires (\forall int j; 0 < j && j < border.length;
      @    (\forall int i; i >= border[j] && i <= j - 1;
      @    (\exists int k; 0 <= k && k < i; pattern[k] != pattern[j - i + k])));
      @  requires (\forall int j; 0 <= j && j < border.length;
      @    border[j] >= -1);
      @  requires (\forall int j; 0 < j && j < border.length;
      @    border[j] >= 0);
      @  requires (\forall int j; 0 <= j && j < border.length;
      @    border[j] <= j - 1);
      @
      @  assignable \nothing;
      @
      @  ensures \result.length == text.length;
      @  ensures (\forall int i; 0 <= i && i <= text.length - pattern.length; \result[i] == (\forall int j; 0 <= j && j < pattern.length; text[i + j] == pattern[j]));
      @*/
    public static boolean[] search(char[] text, char[] pattern, int[] border) {
        boolean[] matched = new boolean[text.length];

        // ... @   (\forall int k; k >= valid_upto && k < i && k <= text.length - pattern.length; (\exists int l; l >= 0 && l < pattern.length && k + l < text.length; text[k + l] != pattern[l])) &&

        int i = 0;
        int j = 0;
        //@ ghost int valid_upto = 0;
        /*@ loop_invariant
         @  i >= 0 && i <= text.length &&
         @  j >= 0 && j < pattern.length &&
         @  valid_upto >= 0 && valid_upto <= text.length - pattern.length + 1 &&
         @  valid_upto <= i &&
         @   (\forall int k; k >= valid_upto && k < i && k <= text.length - pattern.length; matched[k] == (\forall int j; 0 <= j && j < pattern.length; text[k + j] == pattern[j])) &&
         @   (\forall int k; 0 <= k && k < valid_upto; (k <= text.length - pattern.length) ==> (matched[k] == (\forall int j; 0 <= j && j < pattern.length; text[k + j] == pattern[j]))) &&
         @   (\forall int k; 0 <= k && k < j; (i + k < text.length) ==> (text[i + k] == pattern[k])) &&
         @   (\forall int k; k > valid_upto && k < matched.length; matched[k] == false);
         @
         @  assignable i, j, valid_upto, matched[*];
         @  decreases text.length - i;
         @  decreases text.length - valid_upto;
         @*/
        while (i <= text.length - pattern.length) { // && valid_upto <= text.length - pattern.length) {
            boolean mismatch = false;
            /*@ loop_invariant
             @   j >= 0 && j <= pattern.length &&
             @   (\forall int k; 0 <= k && k < j; text[i + k] == pattern[k]) &&
             @   (mismatch ==> (\exists int k; 0 <= k && k < pattern.length; text[i + k] != pattern[k]));
             @
             @  assignable j, mismatch;
             @  decreases pattern.length - j;
             @*/
            for (; j < pattern.length; j++) {
                if (text[i + j] != pattern[j]) {
                    mismatch = true;
                    break;
                }
            }
            matched[i] = !mismatch;
            //@ set valid_upto = i + 1;

            i += j - border[j];
            j = Math.max(0, border[j]);
        }
        return matched;
    }
}
