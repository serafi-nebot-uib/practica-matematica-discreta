import java.lang.AssertionError;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.function.BiPredicate;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.stream.Stream;

/*
 * Aquesta entrega consisteix en implementar tots els mètodes annotats amb "// TODO". L'enunciat de
 * cada un d'ells és al comentari de la seva signatura i exemples del seu funcionament als mètodes
 * `Tema1.tests`, `Tema2.tests`, etc.
 *
 * L'avaluació consistirà en:
 *
 * - Si el codi no compila, la nota del grup serà un 0.
 *
 * - Si heu fet cap modificació que no sigui afegir un mètode, afegir proves als mètodes "tests()" o
 *   implementar els mètodes annotats amb "// TODO", la nota del grup serà un 0.
 *
 * - Principalment, la nota dependrà del correcte funcionament dels mètodes implemnetats (provant
 *   amb diferents entrades).
 *
 * - Tendrem en compte la neteja i organització del codi. Un estandard que podeu seguir és la guia
 *   d'estil de Google per Java: https://google.github.io/styleguide/javaguide.html . Algunes
 *   consideracions importants:
 *    + Entregau amb la mateixa codificació (UTF-8) i finals de línia (LF, no CR+LF)
 *    + Indentació i espaiat consistent
 *    + Bona nomenclatura de variables
 *    + Declarar les variables el més aprop possible al primer ús (és a dir, evitau blocs de
 *      declaracions).
 *    + Convé utilitzar el for-each (for (int x : ...)) enlloc del clàssic (for (int i = 0; ...))
 *      sempre que no necessiteu l'índex del recorregut.
 *
 * Per com està plantejada aquesta entrega, no necessitau (ni podeu) utilitzar cap `import`
 * addicional, ni qualificar classes que no estiguin ja importades. El que sí podeu fer és definir
 * tots els mètodes addicionals que volgueu (de manera ordenada i dins el tema que pertoqui).
 *
 * Podeu fer aquesta entrega en grups de com a màxim 3 persones, i necessitareu com a minim Java 10.
 * Per entregar, posau a continuació els vostres noms i entregau únicament aquest fitxer.
 * - Nom 1: Serafí Nebot Ginard
 * - Nom 2:
 * - Nom 3:
 *
 * L'entrega es farà a través d'una tasca a l'Aula Digital que obrirem abans de la data que se us
 * hagui comunicat i vos recomanam que treballeu amb un fork d'aquest repositori per seguir més
 * fàcilment les actualitzacions amb enunciats nous. Si no podeu visualitzar bé algun enunciat,
 * assegurau-vos de que el vostre editor de texte estigui configurat amb codificació UTF-8.
 */
class Entrega {
  /*
   * Aquí teniu els exercicis del Tema 1 (Lògica).
   *
   * La majoria dels mètodes reben de paràmetre l'univers (representat com un array) i els predicats
   * adients (per exemple, `Predicate<Integer> p`). Per avaluar aquest predicat, si `x` és un
   * element de l'univers, podeu fer-ho com `p.test(x)`, que té com resultat un booleà (true si
   * `P(x)` és cert). Els predicats de dues variables són de tipus `BiPredicate<Integer, Integer>` i
   * similarment s'avaluen com `p.test(x, y)`.
   *
   * En cada un d'aquests exercicis (excepte el primer) us demanam que donat l'univers i els
   * predicats retorneu `true` o `false` segons si la proposició donada és certa (suposau que
   * l'univers és suficientment petit com per poder provar tots els casos que faci falta).
   */
  static class Tema1 {
    static int pow(int base, int exp) {
      int r = 1;
      for (int i = 0; i < exp; i++) r *= base;
      return r;
    }
    /*
     * Donat n > 1, en quants de casos (segons els valors de veritat de les proposicions p1,...,pn)
     * la proposició (...((p1 -> p2) -> p3) -> ...) -> pn és certa?
     *
     * Vegeu el mètode Tema1.tests() per exemples.
     */
    static int exercici1(int n) {
      int prev = 1;
      for (int i = 2; i <= n; i++) {
        int tmp = (pow(2, i - 1) - prev) * 2;
        prev = tmp + (pow(2, i) - tmp) / 2;
      }
      return prev;
    }

    /*
     * És cert que ∀x : P(x) -> ∃!y : Q(x,y) ?
     */
    static boolean exercici2(int[] universe, Predicate<Integer> p, BiPredicate<Integer, Integer> q) {
      for (int x : universe) {
        // if P(x) is false the implication is true, therefore we can skip the rest of the implication
        if (!p.test(x)) continue;
        boolean unique = false;
        for (int y : universe) {
          if (q.test(x, y)) {
            // if Q(x, y) is true and we have already found a different element for which it is also true
            // the conclusion of the implication is false and because we have already checked that the predicate is true
            // the whole implication fails and there's no need to check for any more cases
            if (unique) return false;
            unique = true;
          }
        }
        // no element y was found for which the implication was true, the whole predicate fails
        if (!unique) return false;
      }
      return true;
    }

    /*
     * És cert que ∃x : ∀y : Q(x, y) -> P(x) ?
     */
    static boolean exercici3(int[] universe, Predicate<Integer> p, BiPredicate<Integer, Integer> q) {
      for (int x : universe) {
        boolean yvalid = true;
        for (int y : universe) {
          // if a single y fails the implication, the predicate ∀y : Q(x, y) -> P(x) is false for the current x
          // skip the remaining elements in the universe and check for another x
          if (q.test(x, y) && !p.test(x)) { // !(Q -> P) = !(!Q ∨ P) = !!Q ∨ !P = Q ∨ !P
            yvalid = false;
            break;
          }
        }
        // all elements y have passed the predicate ∀y : Q(x, y) -> P(x) for the current x
        // which means the whole predicate is true
        if (yvalid) return true;
      }
      // no element x has passed the whole predicate
      return false;
    }

    /*
     * És cert que ∃x : ∃!y : ∀z : P(x,z) <-> Q(y,z) ?
     */
    static boolean exercici4(int[] universe, BiPredicate<Integer, Integer> p, BiPredicate<Integer, Integer> q) {
      for (int x : universe) {
        boolean unique = false;
        for (int y : universe) {
          boolean zvalid = true;
          for (int z : universe) {
            // !(P <-> Q) = !((P ∧ Q) ∨ (!P ∧ !Q)) = !(P ∧ Q) ∧ !(!P ∧ !Q) = (!P ∨ !Q) ∧ (P ∨ Q)
            boolean pval = p.test(x, z);
            boolean qval = q.test(y, z);
            if ((!pval || !qval) && (pval || qval)) {
              zvalid = false;
              break;
            }
          }
          if (zvalid)
            if (!(unique = !unique)) break;
        }
        if (unique) return true;
      }
      return false;
    }

    /*
     * Aquí teniu alguns exemples i proves relacionades amb aquests exercicis (vegeu `main`)
     */
    static void tests() {
      // Exercici 1

      // p1 -> p2 és cert exactament a 3 files
      // p1 p2
      // 0  0  <-
      // 0  1  <-
      // 1  0
      // 1  1  <-
      assertThat(exercici1(2) == 3);

      // (p1 -> p2) -> p3 és cert exactament a 5 files
      // p1 p2 p3
      // 0  0  0
      // 0  0  1  <-
      // 0  1  0
      // 0  1  1  <-
      // 1  0  0  <-
      // 1  0  1  <-
      // 1  1  0
      // 1  1  1  <-
      assertThat(exercici1(3) == 5);

      // Exercici 2
      // ∀x : P(x) -> ∃!y : Q(x,y)
      assertThat(
          exercici2(
            new int[] { 1, 2, 3 },
            x -> x % 2 == 0,
            (x, y) -> x+y >= 5
          )
      );

      assertThat(
          !exercici2(
            new int[] { 1, 2, 3 },
            x -> x < 3,
            (x, y) -> x-y > 0
          )
      );

      // Exercici 3
      // És cert que ∃x : ∀y : Q(x, y) -> P(x) ?
      assertThat(
          exercici3(
            new int[] { 1, 2, 3, 4, 5, 6, 7, 8, 9 },
            x -> x % 3 != 0,
            (x, y) -> y % x == 0
          )
      );

      assertThat(
          exercici3(
            new int[] { 1, 2, 3, 4, 5, 6, 7, 8, 9 },
            x -> x % 4 != 0,
            (x, y) -> (x*y) % 4 != 0
          )
      );

      // Exercici 4
      // És cert que ∃x : ∃!y : ∀z : P(x,z) <-> Q(y,z) ?
      assertThat(
          exercici4(
            new int[] { 0, 1, 2, 3, 4, 5 },
            (x, z) -> x*z == 1,
            (y, z) -> y*z == 2
          )
      );

      assertThat(
          !exercici4(
            new int[] { 2, 3, 4, 5 },
            (x, z) -> x*z == 1,
            (y, z) -> y*z == 2
          )
      );
    }
  }

  /*
   * Aquí teniu els exercicis del Tema 2 (Conjunts).
   *
   * Per senzillesa tractarem els conjunts com arrays (sense elements repetits). Per tant, un
   * conjunt de conjunts d'enters tendrà tipus int[][].
   *
   * Les relacions també les representarem com arrays de dues dimensions, on la segona dimensió
   * només té dos elements. Per exemple
   *   int[][] rel = {{0,0}, {0,1}, {1,1}, {2,2}};
   * i també donarem el conjunt on està definida, per exemple
   *   int[] a = {0,1,2};
   * Als tests utilitzarem extensivament la funció generateRel definida al final (també la podeu
   * utilitzar si la necessitau).
   *
   * Les funcions f : A -> B (on A i B son subconjunts dels enters) les representam o bé amb el seu
   * graf o amb un objecte de tipus Function<Integer, Integer>. Sempre donarem el domini int[] a, el
   * codomini int[] b. En el cas de tenir un objecte de tipus Function<Integer, Integer>, per aplicar
   * f a x, és a dir, "f(x)" on x és d'A i el resultat f.apply(x) és de B, s'escriu f.apply(x).
   */
  static class Tema2 {
    static int max(int[] src) {
      if (src == null || src.length == 0) return 0;
      int r = Integer.MIN_VALUE;
      for (int x : src) if (x > r) r = x;
      return r;
    }

    static boolean isElementOf(int e, int[] u, int size) {
      for (int i = 0; i < size; i++) if (e == u[i]) return true;
      return false;
    }

    static boolean isElementOf(int e, int[] u) {
      return isElementOf(e, u, u.length);
    }

    static boolean isEqual(int[] e, int[] u) {
      if (e.length != u.length) return false;
      for (int i = 0; i < e.length; i++) if (e[i] != u[i]) return false;
      return true;
    }

    static boolean isElementOf(int[] e, int[][] u, int size) {
      for (int i = 0; i < size; i++) if (isEqual(e, u[i])) return true;
     return false;
    }

    static boolean isElementOf(int[] e, int[][] u) {
      return isElementOf(e, u, u.length);
    }

    static int[] union(int[] a, int[] b) {
      int[] m = minus(b, a);
      int[] dst = new int[a.length + m.length];
      int i = 0;
      for (int x : a) dst[i++] = x;
      for (int x : m) dst[i++] = x;
      return dst;
    }

    static int[][] dot(int[] a, int[] b) {
      int[][] dst = new int[a.length * b.length][2]; // create destination array with theoretical maximum number of elements
      int i = 0; // destination array index
      {
        int[] tmp = new int[2];
        for (int x : a) {
          for (int y : b) {
            tmp[0] = x;
            tmp[1] = y;
            if (!isElementOf(tmp, dst, i)) dst[i++] = tmp.clone();
          }
        }
      }
      if (dst.length == i) return dst; // no need to copy, destination array is already to size
      // resize array to actual length by making a copy
      int[][] tmp = new int[i][2];
      for (int j = 0; j < i; j++) tmp[j] = dst[j];
      return tmp;
    }

    static int[] minus(int[] a, int[] b) {
      int[] dst = new int[a.length]; // create destination array with theoretical maximum number of elements
      int i = 0;
      for (int x : a) if (!isElementOf(x, b)) dst[i++] = x; // copy elements of b which are not in dst
      if (dst.length == i) return dst; // no need to copy, destination array is already to size
      // resize array to actual length by making a copy
      int[] tmp = new int[i];
      for (int j = 0; j < i; j++) tmp[j] = dst[j];
      return tmp;
    }

    static int pow(int base, int exp) {
      int r = 1;
      for (int i = 0; i < exp; i++) r *= base;
      return r;
    }

    static int[][] union(int[][] a, int[][] b) {
      int[][] dst = new int[a.length + b.length][a[0].length];
      int idx = 0;
      for (int[] x : a) dst[idx++] = x.clone();
      for (int[] x : b) if (!isElementOf(x, a)) dst[idx++] = x.clone();
      if (dst.length == idx) return dst; // no need to copy, destination array is already to size
      // resize array to actual length by making a copy
      int[][] tmp = new int[idx][dst[0].length];
      for (int j = 0; j < idx; j++) tmp[j] = dst[j];
      return tmp;
    }

    static int[][] reflexiveClosure(int[] a, int[][] rel) {
      int[][] dst = new int[a.length][2];
      for (int i = 0; i < a.length; i++) {
        dst[i][0] = a[i];
        dst[i][1] = a[i];
      }
      return union(dst, rel);
    }

    static int[][] symmetricClosure(int[][] rel) {
      int[][] dst = new int[rel.length * 2][2];
      int[] tmp = new int[2];
      int idx = 0;
      for (int[] x : rel) {
        tmp[0] = x[1];
        tmp[1] = x[0];
        if (!isElementOf(x, dst, idx)) dst[idx++] = x.clone();
        if (!isElementOf(tmp, dst, idx)) dst[idx++] = tmp.clone();
      }
      if (dst.length == idx) return dst; // no need to copy, destination array is already to size
      // resize array to actual length by making a copy
      int[][] res = new int[idx][dst[0].length];
      for (int j = 0; j < idx; j++) res[j] = dst[j];
      return res;
    }

    static int[][] transitiveClosure(int[] a, int[][] rel) {
      int[][] dst = new int[pow(a.length, 2)][2];
      int[] tmp = new int[2];
      int idx = 0;
      for (int[] x : rel) dst[idx++] = x.clone();
      for (int i = 0; i < idx; i++) {
        for (int j = 0; j < idx; j++) {
          if (dst[i][1] == dst[j][0]) {
            tmp[0] = dst[i][0];
            tmp[1] = dst[j][1];
            if (!isElementOf(tmp, dst, idx)) dst[idx++] = tmp.clone();
          }
        }
      }
      if (dst.length == idx) return dst; // no need to copy, destination array is already to size
      // resize array to actual length by making a copy
      int[][] res = new int[idx][dst[0].length];
      for (int j = 0; j < idx; j++) res[j] = dst[j];
      return res;
    }

    static String arrToStr(int[] a, String sep) {
      String s = "";
      for (int i = 0; i < a.length; i++) {
        s += String.valueOf(a[i]);
        if (i < a.length - 1) s += sep;
      }
      return s;
    }

    static String arrToStr(int[] a) {
      return arrToStr(a, ",");
    }

    static String arrToStr(int[][] a, String sep) {
      String s = "";
      for (int i = 0; i < a.length; i++) {
        s += arrToStr(a[i]);
        if (i < a.length - 1) s += sep;
      }
      return s;
    }

    static String arrToStr(int[][] a) {
      return arrToStr(a, " ");
    }

    static String matToStr(int[][] a) {
      String s = "";
      for (int i = 0; i < a.length; i++) {
        s += arrToStr(a[i], " ");
        if (i < a.length - 1) s += "\n";
      }
      return s;
    }

    static boolean isReflexive(int[] a, int[][] rel) {
      int[] tmp = new int[2];
      for (int x : a) {
        tmp[0] = x;
        tmp[1] = x;
        if (!isElementOf(tmp, rel)) return false;
      }
      return true;
    }

    static boolean isAntisymmetric(int[][] rel) {
      for (int[] x : rel)
        for (int[] y : rel)
          if (x[0] == y[1] && x[1] == y[0])
            if (x[0] != x[1]) return false;
      return true;
    }

    static boolean isTransitive(int[][] rel) {
      int[] tmp = new int[2];
      for (int[] x : rel) {
        for (int[] y : rel) {
          if (x[1] == y[0]) {
            tmp[0] = x[0];
            tmp[1] = y[1];
            if (!isElementOf(tmp, rel)) return false;
          }
        }
      }
      return true;
    }

    static int[] pathCount(int[][] rel, int org, int dst) {
      if (org == dst) return new int[]{0};
      int[] cnt = new int[rel.length];
      int idx = 0;
      for (int[] x : rel) {
        if (x[0] != org) continue;
        if (x[1] == dst) cnt[idx++] = 1;
        else if (x[0] != x[1]) for (int y : pathCount(rel, x[1], dst)) cnt[idx++] = y + 1;
      }
      if (cnt.length == idx) return cnt; // no need to copy, destination array is already to size
      // resize array to actual length by making a copy
      int[] res = new int[idx];
      for (int j = 0; j < idx; j++) res[j] = cnt[j];
      return res;
    }

    static boolean isFunctionForDomain(int[] dom, int[] codom, int[][] rel) {
      if (dom.length != rel.length) return false;
      for (int i = 0; i < rel.length; i++) {
        // check that both elements are in domain
        if (!isElementOf(rel[i][0], dom) || !isElementOf(rel[i][1], codom)) return false;
        // check that there aren't any repeated elements (a function cannot have a different image for the same element)
        for (int j = 0; j < i; j++) if (rel[i][0] == rel[j][0]) return false;
      }
      return true;
    }

    /*
     * Calculau el nombre d'elements del conjunt de parts de (a u b) × (a \ c)
     *
     * Podeu soposar que `a`, `b` i `c` estan ordenats de menor a major.
     */
    static int exercici1(int[] a, int[] b, int[] c) {
      return dot(union(a, b), minus(a, c)).length;
    }

    /*
     * La clausura d'equivalència d'una relació és el resultat de fer-hi la clausura reflexiva, simètrica i
     * transitiva simultàniament, i, per tant, sempre és una relació d'equivalència.
     *
     * Trobau el cardinal d'aquesta clausura.
     *
     * Podeu soposar que `a` i `rel` estan ordenats de menor a major (`rel` lexicogràficament).
     */
    static int exercici2(int[] a, int[][] rel) {
      return transitiveClosure(a, symmetricClosure(reflexiveClosure(a, rel))).length;
    }

    /*
     * Comprovau si la relació `rel` és un ordre total sobre `a`. Si ho és retornau el nombre
     * d'arestes del seu diagrama de Hasse. Sino, retornau -2.
     *
     * Podeu soposar que `a` i `rel` estan ordenats de menor a major (`rel` lexicogràficament).
     */
    static int exercici3(int[] a, int[][] rel) {
      if (!isReflexive(a, rel) || !isAntisymmetric(rel) || !isTransitive(rel)) return -2;
      int cnt = 0;
      for (int i = 0; i < rel.length; i++) if (max(pathCount(rel, rel[i][0], rel[i][1])) == 1) cnt++;
      return cnt;
    }

    /*
     * Comprovau si les relacions `rel1` i `rel2` són els grafs de funcions amb domini i codomini
     * `a`. Si ho son, retornau el graf de la composició `rel2 ∘ rel1`. Sino, retornau null.
     *
     * Podeu soposar que `a`, `rel1` i `rel2` estan ordenats de menor a major (les relacions,
     * lexicogràficament).
     */
    static int[][] exercici4(int[] a, int[][] rel1, int[][] rel2) {
      if (!isFunctionForDomain(a, a, rel1) || !isFunctionForDomain(a, a, rel2)) return null;
      int[][] r = new int[rel1.length][2];
      for (int i = 0; i < r.length; i++) {
        r[i][0] = rel1[i][0];
        for (int[] y : rel2) if (rel1[i][1] == y[0]) r[i][1] = y[1];
      }
      return r;
    }

    /*
     * Comprovau si la funció `f` amb domini `dom` i codomini `codom` té inversa. Si la té, retornau
     * el seu graf (el de l'inversa). Sino, retornau null.
     */
    static int[][] exercici5(int[] dom, int[] codom, Function<Integer, Integer> f) {
      if (dom.length != codom.length) return null;
      int[][] rel = new int[dom.length][2];
      int[][] inv = new int[dom.length][2];
      for (int i = 0; i < rel.length; i++) {
        rel[i][0] = dom[i];
        rel[i][1] = f.apply(dom[i]);
        inv[i][1] = dom[i];
        inv[i][0] = f.apply(dom[i]);
      }
      if (!isFunctionForDomain(dom, codom, rel)) return null;
      return inv;
    }

    /*
     * Aquí teniu alguns exemples i proves relacionades amb aquests exercicis (vegeu `main`)
     */
    static void tests() {
      // Exercici 1
      // |(a u b) × (a \ c)|

      assertThat(
          exercici1(
            new int[] { 0, 1, 2 },
            new int[] { 1, 2, 3 },
            new int[] { 0, 3 }
          )
          == 8
      );

      assertThat(
          exercici1(
            new int[] { 0, 1 },
            new int[] { 0 },
            new int[] { 0 }
          )
          == 2
      );

      // Exercici 2
      // nombre d'elements de la clausura d'equivalència

      final int[] int08 = { 0, 1, 2, 3, 4, 5, 6, 7, 8 };

      assertThat(exercici2(int08, generateRel(int08, (x, y) -> y == x + 1)) == 81);

      final int[] int123 = { 1, 2, 3 };

      assertThat(exercici2(int123, new int[][] { {1, 3} }) == 5);

      // Exercici 3
      // Si rel és un ordre total, retornar les arestes del diagrama de Hasse

      final int[] int05 = { 0, 1, 2, 3, 4, 5 };

      assertThat(exercici3(int05, generateRel(int05, (x, y) -> x >= y)) == 5);
      assertThat(exercici3(int08, generateRel(int05, (x, y) -> x <= y)) == -2);

      // Exercici 4
      // Composició de grafs de funcions (null si no ho son)

      assertThat(
          exercici4(
            int05,
            generateRel(int05, (x, y) -> x*x == y),
            generateRel(int05, (x, y) -> x == y)
          )
          == null
      );


      var ex4test2 = exercici4(
          int05,
          generateRel(int05, (x, y) -> x + y == 5),
          generateRel(int05, (x, y) -> y == (x + 1) % 6)
        );

      assertThat(
          Arrays.deepEquals(
            lexSorted(ex4test2),
            generateRel(int05, (x, y) -> y == (5 - x + 1) % 6)
          )
      );

      // Exercici 5
      // trobar l'inversa (null si no existeix)

      assertThat(exercici5(int05, int08, x -> x + 3) == null);

      assertThat(
          Arrays.deepEquals(
            lexSorted(exercici5(int08, int08, x -> 8 - x)),
            generateRel(int08, (x, y) -> y == 8 - x)
          )
      );
    }

    /**
     * Ordena lexicogràficament un array de 2 dimensions
     * Per exemple:
     *  arr = {{1,0}, {2,2}, {0,1}}
     *  resultat = {{0,1}, {1,0}, {2,2}}
     */
    static int[][] lexSorted(int[][] arr) {
      if (arr == null)
        return null;

      var arr2 = Arrays.copyOf(arr, arr.length);
      Arrays.sort(arr2, Arrays::compare);
      return arr2;
    }

    /**
     * Genera un array int[][] amb els elements {a, b} (a de as, b de bs) que satisfàn pred.test(a, b)
     * Per exemple:
     *   as = {0, 1}
     *   bs = {0, 1, 2}
     *   pred = (a, b) -> a == b
     *   resultat = {{0,0}, {1,1}}
     */
    static int[][] generateRel(int[] as, int[] bs, BiPredicate<Integer, Integer> pred) {
      var rel = new ArrayList<int[]>();

      for (int a : as) {
        for (int b : bs) {
          if (pred.test(a, b)) {
            rel.add(new int[] { a, b });
          }
        }
      }

      return rel.toArray(new int[][] {});
    }

    /// Especialització de generateRel per a = b
    static int[][] generateRel(int[] as, BiPredicate<Integer, Integer> pred) {
      return generateRel(as, as, pred);
    }
  }

  /*
   * Aquí teniu els exercicis del Tema 3 (Grafs).
   *
   * Els (di)grafs vendran donats com llistes d'adjacència (és a dir, tractau-los com diccionaris
   * d'adjacència on l'índex és la clau i els vèrtexos estan numerats de 0 a n-1). Per exemple,
   * podem donar el graf cicle d'ordre 3 com:
   *
   * int[][] c3dict = {
   *   {1, 2}, // veïns de 0
   *   {0, 2}, // veïns de 1
   *   {0, 1}  // veïns de 2
   * };
   *
   * **NOTA: Els exercicis d'aquest tema conten doble**
   */
  static class Tema3 {
    static String arrToStr(int[] a, String sep) {
      String s = "";
      for (int i = 0; i < a.length; i++) {
        s += String.valueOf(a[i]);
        if (i < a.length - 1) s += sep;
      }
      return s;
    }

    static String arrToStr(int[] a) {
      return arrToStr(a, ",");
    }

    static String arrToStr(int[][] a, String sep) {
      String s = "";
      for (int i = 0; i < a.length; i++) {
        s += arrToStr(a[i]);
        if (i < a.length - 1) s += sep;
      }
      return s;
    }

    static String arrToStr(int[][] a) {
      return arrToStr(a, "\n");
    }

    static String matToStr(int[][] a) {
      String s = "";
      for (int i = 0; i < a.length; i++) {
        s += arrToStr(a[i], " ");
        if (i < a.length - 1) s += "\n";
      }
      return s;
    }

    static int indexOf(int s, int[] a) {
      for (int i = 0; i < a.length; i++) if (a[i] == s) return i;
      return -1;
    }

    static int[][] matmul(int[][] a, int[][] b) {
      if (a[0].length != b.length) return null;
      int[][] r = new int[a.length][b[0].length];
      for (int i = 0; i < r.length; i++)
        for (int j = 0; j < r[0].length; j++)
          for (int k = 0; k < r.length; k++)
            r[i][j] += a[i][k] * b[k][j];
      return r;
    }

    /*
     * BFS (Breadth-First-Search): https://en.wikipedia.org/wiki/Breadth-first_search
     * returns a boolean array indicating which nodes the origin node is connected to
     */
    static boolean[] bfsSearch(int[][] g, int org) {
      boolean[] explored = new boolean[g.length];
      if (g.length == 0) return explored;
      explored[org] = true;
      int[] queue = new int[g.length];
      int qs = 0, qe = 0; // queue start index, queue end index
      queue[qe++] = org;
      while (qs < qe) { // qs < qe means there's an unprocessed item in the queue
        int node = queue[qs++]; // pop the next node from the queue
        // enqueue current node childs that haven't been explored yet
        for (int i = 0; i < g.length; i++) {
          if (g[node][i] == 1 && !explored[i]) {
            queue[qe++] = i;
            explored[i] = true;
          }
        }
      }
      return explored;
    }

    static boolean isConnected(int[][] g) {
      // if all nodes from bfsSearch have been visited from any node (i.e. 0) then the graph is connected
      for (boolean x : bfsSearch(g, 0)) if (!x) return false;
      return true;
    }

    /*
     * Determinau si el graf és connex. Podeu suposar que `g` no és dirigit.
     */
    static boolean exercici1(int[][] g) {
      int[][] mat = new int[g.length][g.length];
      for (int i = 0; i < g.length; i++) {
        for (int j : g[i]) {
          mat[i][j] = 1;
          mat[j][i] = 1;
        }
      }
      return isConnected(mat);
    }

    /*
     * Donat un tauler d'escacs d'amplada `w` i alçada `h`, determinau quin és el mínim nombre de
     * moviments necessaris per moure un cavall de la casella `i` a la casella `j`.
     *
     * Les caselles estan numerades de `0` a `w*h-1` per files. Per exemple, si w=5 i h=2, el tauler
     * és:
     *   0 1 2 3 4
     *   5 6 7 8 9
     *
     * Retornau el nombre mínim de moviments, o -1 si no és possible arribar-hi.
     */
    static int exercici2(int w, int h, int i, int j) {
      int size = w * h;
      // horse movement positions relative to the current position ordered in the width and height direction
      int[][] hm = new int[][]{{-2, -1}, {-2, 1}, {-1, -2}, {-1, 2}, {1, -2}, {1, 2}, {2, -1}, {2, 1}};
      int[][] mat = new int[size][size]; // adjacent matrix
      for (int c = 0; c < size; c++) {
        // find current position's x and y coordinates
        int y = c / w;
        int x = c % w;
        // find all the possible horse movements from the current position
        for (int[] pos : hm) {
          int posx = x - pos[0];
          int posy = y - pos[1];
          // check if destination cell is inside the board
          if (0 <= posx && posx < w && 0 <= posy && posy < h) mat[c][posy * w + posx] = 1;
        }
      }
      // check if the destination cell is accessible from the origin cell
      if (!bfsSearch(mat, i)[j]) return -1;
      // multiply the adjacent matrix by itself to find the number of paths available from origin to destination
      int k = 1;
      int[][] tmp = mat.clone();
      for (; tmp[i][j] == 0; k++) tmp = matmul(tmp, mat);
      return k;
    }

    /*
    * Depth-First-Search (https://en.wikipedia.org/wiki/Depth-first_search), adapted to return the order
    * in which the nodes are explored
    */
    static int[] preorder(int[][] g, int root) {
      int[] order = new int[g.length];
      if (g.length == 0) return order;
      int[] stack = new int[g.length];
      int si = 0; // stack index
      stack[si++] = root;
      boolean[] explored = new boolean[g.length];
      int oi = 0; // order index
      while (si > 0) { // continue as long as there are items in the stack
        int node = stack[--si]; // pop the last item in the stack
        order[oi++] = node; // add the current to the order array
        if (explored[node]) continue;
        explored[node] = true;
        // reverse order because it's a stack (LIFO)
        for (int i = g.length - 1; i >= 0; i--) if (g[node][i] == 1 && !explored[i]) stack[si++] = i;
      }
      return order;
    }

    /*
     * Donat un arbre arrelat (graf dirigit `g`, amb arrel `r`), decidiu si el vèrtex `u` apareix
     * abans (o igual) que el vèrtex `v` al recorregut en preordre de l'arbre.
     */
    static boolean exercici3(int[][] g, int r, int u, int v) {
      // create adjacent matrix from g
      int[][] mat = new int[g.length][g.length];
      for (int i = 0; i < g.length; i++)
        for (int j : g[i]) mat[i][j] = 1;
      // get the preorder of the graph and check whether u or v comes first
      for (int x : preorder(mat, r)) {
        if (x == u) return true;
        if (x == v) return false;
      }
      return false;
    }

    static int max(int a, int b) {
      return a > b ? a : b;
    }

    /*
     * Donat un recorregut en preordre (per exemple, el primer vèrtex que hi apareix és `preord[0]`)
     * i el grau de cada vèrtex (per exemple, el vèrtex `i` té grau `d[i]`), trobau l'altura de
     * l'arbre corresponent.
     *
     * L'altura d'un arbre arrelat és la major distància de l'arrel a les fulles.
     */
    static int exercici4(int[] preord, int[] d) {
      if (preord.length == 0 || d[0] == 0) return 0;
      int[] stack = new int[preord.length];
      int si = -1, m = 1;
      stack[++si] = d[0];
      for (int i = 1; i < d.length; i++) {
        if (d[preord[i]] == 0) --stack[si];
        while (stack[si] == 0 && si > 0) --stack[--si];
        if (d[preord[i]] > 0) {
          stack[++si] = d[preord[i]];
          m = max(m, si + 1);
        }
      }
      return m;
    }

    /*
     * Aquí teniu alguns exemples i proves relacionades amb aquests exercicis (vegeu `main`)
     */
    static void tests() {
      // Exercici 1
      // G connex?

      final int[][] B2 = { {}, {} };

      final int[][] C3 = { {1, 2}, {0, 2}, {0, 1} };

      final int[][] C3D = { {1}, {2}, {0} };

      assertThat(exercici1(C3));
      assertThat(!exercici1(B2));

      // Exercici 2
      // Moviments de cavall

      // Tauler 4x3. Moviments de 0 a 11: 3.
      // 0  1   2   3
      // 4  5   6   7
      // 8  9  10  11
      assertThat(exercici2(4, 3, 0, 11) == 3);

      // Tauler 3x2. Moviments de 0 a 2: (impossible).
      // 0 1 2
      // 3 4 5
      assertThat(exercici2(3, 2, 0, 2) == -1);

      // Exercici 3
      // u apareix abans que v al recorregut en preordre (o u=v)

      final int[][] T1 = {
        {1, 2, 3, 4},
        {5},
        {6, 7, 8},
        {},
        {9},
        {},
        {},
        {},
        {},
        {10, 11},
        {},
        {}
      };

      assertThat(exercici3(T1, 0, 5, 3));
      assertThat(!exercici3(T1, 0, 6, 2));

      // Exercici 4
      // Altura de l'arbre donat el recorregut en preordre

      final int[] P1 = { 0, 1, 5, 2, 6, 7, 8, 3, 4, 9, 10, 11 };
      final int[] D1 = { 4, 1, 3, 0, 1, 0, 0, 0, 0, 2,  0,  0 };

      final int[] P2 = { 0, 1, 2, 3, 4, 5, 6, 7, 8 };
      final int[] D2 = { 2, 0, 2, 0, 2, 0, 2, 0, 0 };

      assertThat(exercici4(P1, D1) == 3);
      assertThat(exercici4(P2, D2) == 4);
    }
  }

  /*
   * Aquí teniu els exercicis del Tema 4 (Aritmètica).
   *
   * En aquest tema no podeu:
   *  - Utilitzar la força bruta per resoldre equacions: és a dir, provar tots els nombres de 0 a n
   *    fins trobar el que funcioni.
   *  - Utilitzar long, float ni double.
   *
   * Si implementau algun dels exercicis així, tendreu un 0 d'aquell exercici.
   */
  static class Tema4 {
    static int min(int a, int b) {
      return a < b ? a : b;
    }

    static int max(int a, int b) {
      return a > b ? a : b;
    }

    static int abs(int a) {
      return a >= 0 ? a: a * -1;
    }

    static int gcd(int a, int b) {
      int tmp = b;
      if (abs(a) < abs(b)) {
        b = a;
        a = tmp;
      }
      while (b != 0) {
        tmp = a % b;
        a = b;
        b = tmp;
      }
      return abs(a);
    }

    static int lcd(int a, int b) {
      return abs(a * b / gcd(a, b));
    }

    static int idxWrap(int i, int len) {
      return i < 0 ? len + i : i;
    }

    static int[] gcdExt(int a, int b) {
      boolean inv = abs(a) < abs(b);
      if (inv) {
        int tmp = b;
        b = a;
        a = tmp;
      }

      int[][] st = new int[][]{{a, 0, 1, 0}, {b, a / b, 0, 1}, {0, 0, 0, 0}};
      int i = 1;
      while (st[i][0] != 0) {
        i = (i + 1) % st.length;
        int i1 = idxWrap(i - 2, st.length);
        int i2 = idxWrap(i - 1, st.length);
        int i3 = i;
        st[i2][1] = st[i1][0] / st[i2][0];
        st[i3][0] = st[i1][0] % st[i2][0];
        st[i3][2] = st[i1][2] - st[i2][1] * st[i2][2];
        st[i3][3] = st[i1][3] - st[i2][1] * st[i2][3];
      }

      i = idxWrap(i - 1, st.length);
      return inv ? new int[]{st[i][0], st[i][3], st[i][2]} : new int[]{st[i][0], st[i][2], st[i][3]};
    }

    /*
     * Calculau el mínim comú múltiple de `a` i `b`.
     */
    static int exercici1(int a, int b) {
      return lcd(a, b);
    }

    /*
     * Trobau totes les solucions de l'equació
     *
     *   a·x ≡ b (mod n)
     *
     * donant els seus representants entre 0 i n-1.
     *
     * Podeu suposar que `n > 1`. Recordau que no no podeu utilitzar la força bruta.
     */
    static int[] exercici2(int a, int b, int n) {
      int[] r = gcdExt(a, n);
      int gcd = r[0], x0 = r[1];
      int m = b / gcd;
      int[] res = new int[gcd];
      int idx = 0;
      for (int i = 0; i < n; i++) {
        int x = x0 * m + i * m;
        if (0 <= x && x < n && a * x % n == b) res[idx++] = x;
      }
      return res;
    }

    /*
     * Donats `a != 0`, `b != 0`, `c`, `d`, `m > 1`, `n > 1`, determinau si el sistema
     *
     *   a·x ≡ c (mod m)
     *   b·x ≡ d (mod n)
     *
     * té solució.
     */
    static boolean exercici3(int a, int b, int c, int d, int m, int n) {
      int gcd1 = gcd(a, m);
      int gcd2 = gcd(b, n);
      if (c % gcd1 != 0 || d % gcd2 != 0) return false;
      c /= gcd1;
      m /= gcd1;
      d /= gcd2;
      n /= gcd2;
      return (d - c) % gcd(m, n) == 0;
    }

    static int pow(int base, int exp) {
      int r = 1;
      for (int i = 0; i < exp; i++) r *= base;
      return r;
    }

    static int mod(int a, int b) {
      a %= b;
      return a < 0 ? a + b : a;
    }

    /*
     * Donats `n` un enter, `k > 0` enter, i `p` un nombre primer, retornau el residu de dividir n^k
     * entre p.
     *
     * Alerta perquè és possible que n^k sigui massa gran com per calcular-lo directament.
     * De fet, assegurau-vos de no utilitzar cap valor superior a max{n, p²}.
     *
     * Anau alerta també abusant de la força bruta, la vostra implementació hauria d'executar-se en
     * qüestió de segons independentment de l'entrada.
     */
    static int exercici4(int n, int k, int p) {
      return pow(n, k % (p - 1)) % p;
    }

    /*
     * Aquí teniu alguns exemples i proves relacionades amb aquests exercicis (vegeu `main`)
     */
    static void tests() {
      // Exercici 1
      // mcm(a, b)

      assertThat(exercici1(35, 77) == 5*7*11);
      assertThat(exercici1(-8, 12) == 24);

      // Exercici 2
      // Solucions de a·x ≡ b (mod n)

      assertThat(Arrays.equals(exercici2(2, 2, 4), new int[] { 1, 3 }));
      assertThat(Arrays.equals(exercici2(3, 2, 4), new int[] { 2 }));

      // Exercici 3
      // El sistema a·x ≡ c (mod m), b·x ≡ d (mod n) té solució?

      assertThat(exercici3(3, 2, 2, 2, 5, 4));
      assertThat(!exercici3(3, 2, 2, 2, 10, 4));

      // Exercici 4
      // n^k mod p

      assertThat(exercici4(2018, 2018, 5) == 4);
      assertThat(exercici4(-2147483646, 2147483645, 679389209) == 145738906);
    }
  }

  /**
   * Aquest mètode `main` conté alguns exemples de paràmetres i dels resultats que haurien de donar
   * els exercicis. Podeu utilitzar-los de guia i també en podeu afegir d'altres (no els tendrem en
   * compte, però és molt recomanable).
   *
   * Podeu aprofitar el mètode `assertThat` per comprovar fàcilment que un valor sigui `true`.
   */
  public static void main(String[] args) {
    Tema1.tests();
    Tema2.tests();
    Tema3.tests();
    Tema4.tests();
  }

  /// Si b és cert, no fa res. Si b és fals, llança una excepció (AssertionError).
  static void assertThat(boolean b) {
    if (!b)
      throw new AssertionError();
  }
}

// vim: set textwidth=100 shiftwidth=2 expandtab :
