/*
    Bfind by Leo Fisher.
    Based off of afind by Eugene Langvagen.
*/

// -*- compile-command: "g++ -Wall -pedantic -O3 bfind.cc -o bfind" -*-

/*
  "afind.cc" originates at http://plife.sourceforge.net/

  For details on program design, see David Eppsten's article at http://arxiv.org/abs/cs.AI/0004003
  The differences from "gfind" include (optionally enabled) floating rows, exhaustive double look-ahead,
  ability to search for knightships and (alas) lack of diagonal symmetry modes.
*/

//---------------------------------------------------------------------------
#define PROGRAM "bfind-0.5"

#define FLOATING_ROWS	// enables floating rows; 
// #define REVERSE		// for dealing with negative offset; slide is ignored in this case

#define BACKGROUND
// #define PROFILE

//---------------------------------------------------------------------------
// #include <ciso646>		// uncomment if the tokens "and", "or" etc. are not C++ keywords
#include <cassert>
#include <cctype>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <ctime>          //TODO: Deprecated, replace with chrono
//include <chrono>
#include <exception>
#include <stdexcept>
#include <vector>

#include <inttypes.h>

#include <sys/timeb.h>
#include <sys/types.h>
#include <sys/stat.h>

#ifdef BACKGROUND
#include <sys/time.h>
#include <sys/resource.h>
#include <unistd.h>
#endif // BACKGROUND

//---------------------------------------------------------------------------
typedef uint32_t row_t, hash_t, index_t, mask_t;

//---------------------------------------------------------------------------
// input data:
static char rule_string[32] = "b3/s23";

static mask_t birth_mask = 8;
static mask_t stay_mask = 12;

static int width = 5;
static int period = 4;
static int offset = 1;		// the y offset
static int slide = 0;		// the x offset

enum { asym, odd_sym, even_sym } mode = odd_sym;

static int left_edge = 0;

#ifdef FLOATING_ROWS
static int floating_rows = 1;
#else
static int floating_rows = 0;
#endif // FLOATING_ROWS

static int queue_bits = 25, hash_bits = 25;

struct param_t { char *name; void *addr; char type; };

param_t input_params[] = {
	{ "rule",          rule_string,    's' },
	{ "width",         &width,         'i' },
	{ "period",        &period,        'i' },
	{ "offset",        &offset,        'i' },
	{ "slide",         &slide,         'i' },
	{ "mode",          &mode,          'i' },
	{ "left_edge",     &left_edge,     'i' },
	{ "floating_rows", &floating_rows, 'i' },
	{ "queue_bits",    &queue_bits,    'i' },
	{ "hash_bits",     &hash_bits,     'i' },
	{ NULL,            NULL,           'i' }
};

//---------------------------------------------------------------------------
#ifdef PROFILE
static uintmax_t some_counter = 0;
#endif // PROFILE

//---------------------------------------------------------------------------
static mask_t LT[1 << 18];		// lookup table for row matching
static mask_t LT_start[1 << 11];	// common starting conditions on left edge (copied from one of the above)

static mask_t edge_mask_0[] = { 0xffff, 0x5555, 0x1111, 0x101, 1 };
static mask_t edge_mask_1[] = { 1, 3, 0xf, 0xff, 0xffff};

//---------------------------------------------------------------------------
class row_finder {
	static const int max_top = sizeof (row_t) * 2;

	index_t base_index[max_top];
	mask_t  base_mask [max_top];
	mask_t  mask[max_top];
	row_t   tile[max_top];
	row_t   base_row[max_top];

	int x0, top0;
	int x1, top1;
 	int top;
public:
	operator row_t& () { return row; }

	row_t row;

	void init (row_t b0, row_t b1, row_t a); // => find such b2 that a = evolve (b0, b1, b2)
	bool next ();
};

//---------------------------------------------------------------------------
inline int min (int a, int b) { return (a < b) ? a : b; }
inline int max (int a, int b) { return (a > b) ? a : b; }

// m becomes equal to the positoin of lowest/highest bit in bits
// x86 specific :(
#define get_lowest_bit(m,bits)  asm ("bsfl %1, %0" : "=r" (m) : "r" (bits))
#define get_highest_bit(m,bits) asm ("bsrl %1, %0" : "=r" (m) : "r" (bits))

//---------------------------------------------------------------------------
static inline int count_bits (mask_t bits)
{
	int num;
	for (num = 0; bits; bits >>= 1)
		num += (bits & 1);
	return num;
}

static inline int evolve (bool self, int num)
{
	return ((!self) and ((1 << num) & birth_mask)) or (self and ((1 << num) & stay_mask));
}

static inline row_t evolve (row_t a, row_t b, row_t c)
{
	row_t d = 0;
	switch (mode) {
	case odd_sym:  d = evolve (bool (b & 1),
				   2 * count_bits (b & 2) + 2 * count_bits (a & 2) + 2 * count_bits (c & 2) + 
				   count_bits (a & 1) + count_bits (c & 1));
		break;
	case even_sym: d = evolve (bool (b & 1),
				   count_bits (b & 2) + count_bits (b & 1) + 2 * count_bits (a & 1) +
				   2 * count_bits (c & 1) + count_bits (a & 2) + count_bits (c & 2));
		break;
	case asym: d = 0;
		break;
	}

	for (unsigned int k = 1; k < 8 * sizeof (row_t); k++)
		d += (1 << k) * evolve (b & (1 << k),
					count_bits (a & (7 << (k - 1))) +
					count_bits (b & (5 << (k - 1))) +
					count_bits (c & (7 << (k - 1))));
	return d;
}

//---------------------------------------------------------------------------
/*
1. If "index" holds the bits <abHIJK ghijkl mnopqr> (here lower bits go first), then
   LT[index] is a mask for all 4-cells <cdef> that the evolution is correct:
    abcdef    ......
    ghijkl -> .HIJK.
    mnopqr    ......

2. If "index" is <efgh ijkl EFG>, then
   LT_odd[index]  is the mask for all possible <abcd> with correct evolution:
    dcbabcd    .......
    hgfefgh -> .GFEFG.
    lkjijkl    .......

3. If "index" is <efgh ijkl EFG>, then
   LT_even[index] is the mask for all possible <abcd> with correct evolution:
    dcbaabcd    ........
    hgfeefgh -> .GFEEFG.
    lkjiijkl    ........

4. If "index" is <efgh ijkl EFG>, then
   LT_null[index] is the mask for all possible <abcd> with correct evolution:
    0abcd    .....
    0efgh -> 0EFG.
    0ijkl    .....

5. LT_start is one of LT_odd, LT_even or LT_null according to symmetry mode
*/
void fill_lookup_tables ()
{
	index_t rect, index;
	mask_t center, corner;

	memset (LT, 0, sizeof (LT));
	memset (LT_start, 0, sizeof (LT_start));

	for (rect = 0; rect < 0x40000; rect++) {
		center = 0;
		for (int k = 0; k < 4; k++)
			center += evolve (rect & (0x80 << k), count_bits (rect & (0x7147 << k))) << k;

		corner = rect & 0x3c;
		index = rect - corner + (center << 2);

		corner >>= 2;
		LT[index] |= 1 << corner;
	}

	switch (mode) {
	case asym:
		for (index = 0; index < 0x800; index++) {
			LT_start[index] = LT[((index & 0xf) << 8) + ((index & 0xf0) << 10) + ((index & 0x700) >> 5)];
		} break;
	case odd_sym:
		for (rect = 0; rect < 0x1000; rect++) {
			corner = rect & 0xf;
			center = evolve (rect & 0x10, count_bits (rect & 0x323) + count_bits (rect & 0x222));
			for (int k = 0; k < 2; k++)
				center += evolve (rect & (0x20 << k), count_bits (rect & (0x757 << k))) << (k + 1);
			index = (rect >> 4) + (center << 8);
			LT_start[index] |= (1 << corner);
		} break;
	case even_sym:
		for (rect = 0; rect < 0x1000; rect++) {
			corner = rect & 0xf;
			center = evolve (rect & 0x10, count_bits (rect & 0x323) + count_bits (rect & 0x111));
			for (int k = 0; k < 2; k++)
				center += evolve (rect & (0x20 << k), count_bits (rect & (0x757 << k))) << (k + 1);
			index = (rect >> 4) + (center << 8);
			LT_start[index] |= (1 << corner);
		} break;
	}
}

//---------------------------------------------------------------------------
void parse_rule_string (char *s)
{
	if (!s) 
		return;

	mask_t *p = &stay_mask;
	char c;

	birth_mask = stay_mask = 0;

	while ((c = tolower (*s))) {
		if (isdigit (c))
			(*p) |= 1 << (c - '0');
		if (c == 's') p = &stay_mask;
		if (c == 'b') p = &birth_mask;
		if (c == '/') p = &birth_mask;
		s++;
	}
}

//---------------------------------------------------------------------------
inline void row_finder::init (row_t b0, row_t b1, row_t a)
{
#ifdef FLOATING_ROWS
	int low = 8 * sizeof (row_t);
	int high = 0;

	int m;
	if (a)  { get_lowest_bit (m, a);  low = min (low, m); get_highest_bit (m, a);  high = max (high, m + 1); }
	if (b0) { get_lowest_bit (m, b0); low = min (low, m); get_highest_bit (m, b0); high = max (high, m); }
	if (b1) { get_lowest_bit (m, b1); low = min (low, m); get_highest_bit (m, b1); high = max (high, m); }

	if (!(a | b0 | b1)) {
		low = 0;
		high = left_edge + 2 * width;
	}

// x is in [x0, x1), i.e. x1 is not included
	x0 = max (left_edge, min (low, high - width) - 2);
	x1 = max (high + 1, low + width) + 2;
#else
	x0 = left_edge;
	x1 = left_edge + width;
#endif // FLOATING_ROWS

// top is in [top0, top1] which is an inclusive range
	top0 = (x0 - 2) / 4;
	top1 = (x1 + 2) / 4;

	base_index[0] = (b1 & 0xf) + ((b0 & 0xf) << 4) + ((a & 7) << 8);
	for (int k = 1; k <= top1; k++) {
		base_index[k] = ((b1 & 0xfc) << 4) + ((b0 & 0xfc) << 10) + ((a & 0x78) >> 1);
		b1 >>= 4; b0 >>= 4; a >>= 4;
	}

	base_mask[top1] = base_mask[top0] = 1;
	for (int k = top0 + 1; k < top1; k++)
		base_mask[k] = 0xffff;

	base_mask[x0 / 4] = edge_mask_0[x0 % 4];
	base_mask[x1 / 4] = edge_mask_1[x1 % 4];

	mask[0] = LT_start[base_index[0]] & base_mask[0];
	if (top0) mask[top0] = LT[base_index[top0]] & base_mask[top0];

	tile[top0] = (row_t) -1;
	base_row[top0] = 0;

	top = top0;
	row = 0;
}

//---------------------------------------------------------------------------
inline bool row_finder::next ()
{
	while (top >= top0) {
		if (mask[top] == 0) { top--; continue; }

		int m;
		get_lowest_bit (m, mask[top]);

		mask[top] >>= m + 1;
		tile[top] += m + 1;

		row = base_row[top] + (tile[top] << (4 * top));

#ifdef FLOATING_ROWS
		int l, h;
		get_lowest_bit (l, row);
		get_highest_bit (h, row);
		if (row and (h - l >= width))
			continue;
#endif // FLOATING_ROWS

		if (top == top1) {
			return true;
		} else {
			top++;
			mask[top] = LT[base_index[top] + tile[top - 1] / 4] & base_mask[top];
			tile[top] = (row_t) -1;
			base_row[top] = row;
		}
	}
	return false;
}

//---------------------------------------------------------------------------
class finder {
//	enum event { queue_full, enough_for_now };

	struct vertex_t;

	index_t queue_size, hash_size;

	vertex_t *V;			// the queue of vertices
	hash_t *hash;

	int *F, *B, *FF, *BB, *D;

	int rows_in_state;
	int wrap;
	int full_width;

	index_t head, tail, next_depth_start;
	int head_depth;

	int depth_step, prev_depth, depth_limit;

	int counter;
	int X, Y;			// current output coordinates
	int rounded_width, gap;		// for pretty printing

	int num_cycles, num_hits;

	bool compare (index_t p, index_t q, row_t a);
	bool compare_last_phase (index_t p, index_t q);

	int vertex_depth (index_t p);
	bool build_state (index_t p, row_t *state);

	void print_queue ();
	void print_path (index_t p);
	void pretty_fprint (FILE *output, index_t p);
	void fprint_banner (FILE *output);

	void clear_hash ();	// fill hash with 0xff

	bool compactify ();	// returns false if the search is over
	void collapse_gaps ();	// collapse the gaps consisting of empty nodes after compaction
	void regenerate ();	// called to restore hash, head_depth etc. after loading or compaction

	void input_sanity_check ();	// check the input data
	void queue_sanity_check ();	// check the search context and queue

	void build_hash ();
	hash_t hash_value (index_t p, row_t a, int depth);
	bool find_matching_rows  (index_t parent, int parent_depth);
	int depth_limited_search (index_t parent, int parent_depth, int depth_limit);

// administrative things:
	static const char *context_format;

	bool ready;

	char *filename;

	void load (const char *ifn);

	void prepare () throw (std::bad_alloc);	// to be called as soon as the input data is known
	void reset_search ();			// can be called at any time to reset the search

	int difference (index_t p);		// take the last phase of branch p and find the number of
						// bits in its initial and its (period)-th generation
public:
	finder (const char *ifn);
	~finder ();

	void search ();
	void show_levels ();
//	void asymmetrize (const char *ofn);
//	void widen_left (const char *ofn);
	void truncate (const char *ofn);

	bool save (const char *ofn, bool full_save = true);
	void save_preview (const char *ofn);
	void save_best (const char *ofn);
};

//---------------------------------------------------------------------------
void fprint_row (FILE *output, row_t row);

struct finder::vertex_t {
	row_t row;
	index_t parent;

	inline bool is_empty () { return parent == (index_t) (-1); }
	inline void make_empty () { row = 0; parent = (index_t) (-1); }

	inline void clear () { row = 0; parent = 0; }
	inline void print () { fprint_row (stdout, row); fprintf (stdout, " [%d]\n", parent); }
};

//---------------------------------------------------------------------------
// utility functions:
static bool file_exists (const char *filename)
{
	struct stat st;
	return (stat (filename, &st) == 0);
}

//---------------------------------------------------------------------------
static void goto_next_line (FILE *input)
{
	int c;
	do c = getc (input); while ((c != EOF) && (c != '\n'));
}

static void fput_chars (FILE *output, int c, int n)
{
	for (int k = 0; k < n; k++)
		putc (c, output);
}

static char *current_time ()
{
	struct timeb tb;
	ftime (&tb);
	return ctime (&tb.time);
}
//---------------------------------------------------------------------------
// strip any numeric extension from "fn" and return the result in a statically allocated string
static char *base_file_name (const char *fn)
{
	if (!fn) return NULL;
	if (strlen (fn) > 1000) return NULL;

	static char base_fn[1024];

	int k = strlen (fn) - 1;
	strcpy (base_fn, fn);
	for (; k >= 0; k--)
		if (!isdigit (fn[k]))
			break;
	if (k > 0)
		if (fn[k] == '.')
			k--;
	base_fn[k + 1] = 0;

	return base_fn;
}

// generate a non-occupied file name with base "fn" and return it in a statically allocated string
static char *safe_file_name (const char *fn)
{
	if (!fn) return NULL;
	if (strlen (fn) > 1000) return NULL;

	static char safe_fn[1024];

	int k = 0;
	strcpy (safe_fn, fn);
	while (file_exists (safe_fn))
		sprintf (safe_fn, "%s.%d", fn, ++k);

	return safe_fn;
}

//---------------------------------------------------------------------------
static inline int gcd (int a, int b)
{
	if (a < 0) a = -a;
	if (b < 0) b = -b;

	while (a and b) {
		if (a > b)
			a = a % b;
		else
			b = b % a;
	}
	return a + b;
}

static inline int round_up (int n, int factor) { return ((n + factor - 1) / factor) * factor; }

static int compare_ints (const void *p, const void *q)
{
	const int a = * ((const int *) p);
	const int b = * ((const int *) q);

	return (a > b) - (b > a);
}

//---------------------------------------------------------------------------
void fprint_row (FILE *output, row_t row)
{
	row_t a = row, b = row;

	int k1 = 8 * sizeof (row_t);

	switch (mode) {
	case asym: break;
	case odd_sym:
		putc ('.', output);
		for (int k = k1 - 1; k >= 1; k--)
			putc ((a & (1 << k)) ? '*' : '.', output);
		break;
	case even_sym:
		for (int k = k1 - 1; k >= 0; k--)
			putc ((a & (1 << k)) ? '*' : '.', output);
		break;
	}
	for (int k = 0; k < k1; k++)
		putc ((b & (1 << k)) ? '*' : '.', output);
}

//---------------------------------------------------------------------------
// check if there can possibly be such "b2" that a = evolve (b0, b1, b2)
inline bool check_ahead (row_t b0, row_t b1, row_t a)
{
	row_finder s;
	s.init (b0, b1, a);
	return (s.next ());
}

//---------------------------------------------------------------------------
// Are there such c3, c4 and b2 that (we already have a0)
// b0 = evolve (c0, c1, c2)
// b1 = evolve (c1, c2, c3)
// b2 = evolve (c2, c3, c4)
// and a = evolve (b0, b1, b2)?

inline bool check_ahead (row_t c1, row_t c2, row_t b0, row_t b1, row_t a)
{
	row_finder s2, s3, s4;

	s2.init (b0, b1, a);	// search for b2

	while (s2.next ()) {
		s3.init (c1, c2, b1); // search for c3
		while (s3.next ()) {
			s4.init (c2, s3, s2);
			if (s4.next ())
				return true;
		}
	}
	return false;
}

//---------------------------------------------------------------------------
inline hash_t finder::hash_value (index_t p, row_t a, int depth)
{
	hash_t value = (depth % wrap) << 5;
	for (int k = 0; k < rows_in_state; k++) {
		value = (value * 257) + a;
		a = V[p].row;
		p = V[p].parent;
	}
	value += (value >> 16) * 263;
	value += (value >> 8)  * 267;
	return value & (hash_size - 1);
}

//---------------------------------------------------------------------------
void finder::clear_hash ()
{
	memset (hash, 0xff, sizeof (hash_t) * hash_size);
}

//---------------------------------------------------------------------------
void finder::build_hash ()
{
	if (!hash_bits) return;

	clear_hash ();

	index_t p0 = 0;
	int depth = -1;
	for (index_t p = 0; p < tail; p++) {
		if (V[p].parent == p0) {
			depth++;
			p0 = p;
		}
//		assert (vertex_depth (p) == depth);
		hash[hash_value (V[p].parent, V[p].row, depth)] = p;
	}
}

//---------------------------------------------------------------------------
// test (p == q + a)
inline bool finder::compare (index_t p, index_t q, row_t a)
{
	for (int k = 0; k < rows_in_state; k++) {
		if (a != V[p].row)
			return false;
		a = V[q].row;

		p = V[p].parent;
		q = V[q].parent;
	}
	return true;
}

//---------------------------------------------------------------------------
inline int finder::vertex_depth (index_t p)
{
	int depth = 0;
	while (p != 0) {
		p = V[p].parent;
		depth++;
	}
	return depth;
}

//---------------------------------------------------------------------------
void finder::print_queue ()
{
	for (index_t p = head; p < tail; p++) {
		printf ("%u:\t", p);
		V[p].print ();
	}
}

//---------------------------------------------------------------------------
void finder::print_path (index_t p)
{
	int depth = 0;

	while (p) {
		printf ("%u ", p);
		p = V[p].parent;
		depth++;
	}

	printf ("(depth = %d)\n", depth);

	fflush (stdout);
}	

//---------------------------------------------------------------------------
void finder::pretty_fprint (FILE *output, index_t p)
{
	while ((V[p].row == 0) and p)
		p = V[p].parent;

	if (!p)
		return;

	if (Y >= 224) {
		Y = 0;
		X += round_up (rounded_width * period + 8, 8);
	}

	fprintf (output, "#D (%u) %s", p, current_time ());
	fprintf (output, "#P %d %d\n", X - 160, Y - 112);

	int depth = vertex_depth (p);
	int rounded_depth = round_up (depth, period);
	int height = rounded_depth / period;
	int phase = (rounded_depth - depth) % period;

	int k;

	for (k = 0; k < phase; k++)
		fprint_row (output, 0);

	for (k = phase; k < rounded_depth; k++) {
		fprint_row (output, V[p].row);
		p = V[p].parent;
		if ((k + 1) % period)
			fput_chars (output, '.', gap);
		else
			putc ('\n', output);
	}
	putc ('\n', output);

	Y += round_up (height + 15, 8);

	fflush (output);
}	

//---------------------------------------------------------------------------
// returns true if we do not come across an empty node
inline bool finder::build_state (index_t p, row_t *state)
{
	for (int k = 0; k < rows_in_state; k++) {
		if (V[p].is_empty ())
			return false;
		state[k] = V[p].row;
		p = V[p].parent;
	}
	return true;
}

//---------------------------------------------------------------------------
bool finder::find_matching_rows (index_t parent, int parent_depth)
{
	row_t state[rows_in_state + 1];

	build_state (parent, state + 1);

	int phase = (parent_depth + 1) % period; // phase of the row being searched for

#ifndef REVERSE
	bool check1 = (B[phase] >= 0);
	bool check2 = (B[phase] >= 0) and (BB[phase] >= 0);
	int shift = D[(phase + period - B[phase]) % period];
#else
	bool check1 = (F[phase] <= 0);
	bool check2 = (F[phase] >= 0) and (FF[phase] >= 0);
#endif // REVERSE

	row_finder s;
	s.init (state[2 * period], state[period], state[period - F[phase]] >> D[(phase + period + F[phase]) % period]);

	while (s.next ()) {
		state[0] = s;

		hash_t value = hash_bits ? hash_value (parent, s, phase) : 0;

// do not allow any fake zero states grow from V[0]:
		if (!parent) if (compare (0, parent, s)) continue;

		if (value == 0) if (compare (0, parent, s)) {
			fprintf (stderr, "[%d/%d]\r", counter, num_cycles);
//			fputc ('*', stderr);
			pretty_fprint (stdout, parent);
			assert (difference (parent) == 0);
			counter++;
			continue;
		}

		if (hash_bits) if (hash[value] != hash_t (-1))
			if (s and compare (hash[value], parent, s)) {
				index_t p0 = hash[value], p;
				num_hits++;
				for (p = head; p and (p != p0); p = V[p].parent);
				if (p) {
					num_cycles++;
					fprintf (stderr, "[%d/%d]\r", counter, num_cycles);
				}
				continue;
			}

#ifndef REVERSE
		if (check1) if (!check_ahead (state[period + B [phase]], state[B [phase]], s >> D[phase])) continue;
		if (check2) if (!check_ahead (state[period + BB[phase]] << shift, state[BB[phase]] << shift,
					      state[period + B [phase]], state[B [phase]], s >> D[phase])) continue;
#else
		if (check1) if (!check_ahead (state[period], state[0], state[-F[phase]])) continue;
		if (check2) if (!check_ahead (state[period], s, state[period - F[phase]],
					      state[-F[phase]], state[-FF[phase]])) continue;
#endif // REVERSE

		V[tail].row = s;
		V[tail].parent = parent;

//		if (depth_limited_search (tail, parent_depth + 1, 2) == 0) continue;

		hash[value] = tail;

		tail++;
		if (tail == queue_size)
			return false;
	}
	return true;
}

//---------------------------------------------------------------------------
// returns true if the search is complete (i. e. it does not reach depth_limit)
int finder::depth_limited_search (index_t parent, int parent_depth, int depth_limit)
{
	row_finder S[depth_limit + rows_in_state];

	index_t p = parent;
	for (int k = 0; k < rows_in_state; k++) {
		S[depth_limit + k].row = V[p].row;
		p = V[p].parent;
	}

	struct { int shift, fwd, back, ffwd, bback, check1, check2; } T[depth_limit + rows_in_state];

	for (int k = 0; k < depth_limit + rows_in_state; k++) {
		int phase = (2 * period + parent_depth + (depth_limit - k)) % period;
		T[k].shift  = D[phase];
		T[k].fwd    = k - F [phase];
		T[k].back   = k + B [phase];
#ifndef REVERSE
		T[k].bback  = k + BB[phase];
		T[k].check1 =  (B[phase] >= 0);
		T[k].check2 = ((B[phase] >= 0) and (BB[phase] >= 0));
#else
		T[k].ffwd   = k - FF[phase];
		T[k].check1 =  (F[phase] <= 0);
		T[k].check2 = ((F[phase] <= 0) and (FF[phase] <= 0));
#endif // REVERSE
	}

	int bottom = depth_limit - 1;	// tends to zero (always being <= depth_limit - 1)

	S[bottom].init (S[bottom + 2 * period], S[bottom + period], // S[bottom + period - 1]);
			S[T[bottom].fwd + period] >> T[T[bottom].fwd].shift);

	while (bottom < depth_limit) {
		if (S[bottom].next ()) {
			int n;
			for (n = 0; S[bottom + n] == 0; n++);
			if (n == rows_in_state) return 2;

#ifndef REVERSE
			if (T[bottom].check1)
				if (!check_ahead (S[T[bottom].back + period], S[T[bottom].back],
						  S[bottom] >> T[bottom].shift))
					continue;

			if (T[bottom].check2) {
				int shift = T[T[bottom].back].shift;
				if (!check_ahead (S[T[bottom].bback + period] << shift, S[T[bottom].bback] << shift,
						  S[T[bottom].back + period], S[T[bottom].back],
						  S[bottom] >> T[bottom].shift))
					continue;
			}
#else
			if (T[bottom].check1) if (!check_ahead (S[bottom + period], S[bottom], S[T[bottom].fwd])) continue;
			if (T[bottom].check2) if (!check_ahead (S[bottom + period], S[bottom], S[T[bottom].fwd + period],
						  S[T[bottom].fwd], S[T[bottom].ffwd])) continue;
#endif // REVERSE
			bottom--;

			if (bottom < 0) return 1;

			S[bottom].init (S[bottom + 2 * period], S[bottom + period], // S[bottom + period - 1]);
					S[T[bottom].fwd + period] >> T[T[bottom].fwd + period].shift);
		} else
			bottom++;
	}

	return 0;
}

//---------------------------------------------------------------------------
// return value 'true' means queue became empty and the search is finished
bool finder::compactify ()
{
	index_t p, q, r;
	index_t start;

//	row_t state[rows_in_state];

	assert (tail == queue_size);

// delete the (often non-complete) list of some node's children in the end of the queue
	for (q = tail - 1; V[q].parent == V[q - 1].parent; q--);
	for (p = q; p < queue_size; p++) V[p].make_empty ();
	tail = q;

	if (q == 0) {
		fprintf (stderr, "queue too small, queue compaction won't work!\n");
		return false;
	}

	int depth = vertex_depth (tail - 1);
	depth_limit = (depth - prev_depth > depth_step) ? depth_step : (2 * depth_step - depth + prev_depth);

	fprintf (stderr, "queue full: depth = %d, depth_limit = %d\n", depth, depth_limit);
	prev_depth = depth;

// find the starting point for DLS: everything in [start, tail) is the search frontier,
// i. e. the nodes that have not queued their successors
	start = V[tail - 1].parent + 1;

// depth-limited search: delete nodes that lead only to dead ends (in no more than depth_limit steps)

	int num_front_nodes = tail - start; // number of nodes on the frontier
	int num_kept_nodes = 0;	// number of nodes worth considering further
	int num_sure_nodes = 0; // number of nodes that surely lead to something (maybe not new :)

	clock_t prev_clock = clock (), new_clock;

	fprintf (stderr, "frontier: %d node(s)\n", num_front_nodes);

	assert (head_depth == vertex_depth (start));

	for (head = start; head < tail; head++) {
		if (head == next_depth_start)
			head_depth++;

		if ((head - start) % 10 == 0)
			if ((new_clock = clock ()) - prev_clock > 60 * CLOCKS_PER_SEC) {

				fprintf (stderr, "[%d/%d/%u]\r", num_sure_nodes, num_kept_nodes, head - start);
				prev_clock = new_clock;
			}

		int result;
		if ((result = depth_limited_search (head, head_depth, depth_limit))) {
			num_kept_nodes++;
			num_sure_nodes += (result == 2);
		} else
			V[head].make_empty ();
	}

	fprintf (stderr, "[%d/%d] kept", num_sure_nodes, num_kept_nodes);

	if (num_kept_nodes == 0) {
		fprintf (stderr, " => queue empty\n");
		head = 0;
		tail = 1;
		return false;
	}

// backward pass: delete all nodes that do not have children
	int num_deleted_nodes = 0;

	for (q = tail - 1; V[q].is_empty (); q--);
	// now q is the last non-empty node on the frontier
	// => everything between q's parent and frontier start
	// may be deleted
	for (r = V[q].parent + 1; r < start; r++) {
		V[r].make_empty ();
		num_deleted_nodes++;
	}

	while (q >= 1) {
		for (p = q - 1; V[p].is_empty (); p--);
		// now p and q are 2 successive non-empty nodes
		// => everything between p's and q's parents leads to nothing
		// and may be deleted:
		for (r = V[p].parent + 1; r < V[q].parent; r++) {
			V[r].make_empty ();
			num_deleted_nodes++;
		}
		q = p;
	}

	fprintf (stderr, " => %d node(s) remain in queue\n", num_kept_nodes + (start - num_deleted_nodes));

	collapse_gaps ();

	assert (tail == num_kept_nodes + (start - num_deleted_nodes));

	regenerate ();

	return true;
}

//---------------------------------------------------------------------------
void finder::collapse_gaps ()
{
	index_t p, q, r;
// collapse the gaps:
	for (p = 1; p < tail; p++) if ( V[p].is_empty ()) break; // p is the 1st empty node
	for (q = p; q < tail; q++) if (!V[q].is_empty ()) break; // q is the 1st non-empty node after p
	r = 1;

	while (q < tail) {
		V[p] = V[q];
		V[q].make_empty ();

		for (; r < tail; r++) if (!V[r].is_empty ()) {
			if (V[r].parent > q) break;
			if (V[r].parent == q) V[r].parent = p;
		}

		p++; q++;
		for (; p < tail; p++) if ( V[p].is_empty ()) break;
		for (; q < tail; q++) if (!V[q].is_empty ()) break;
	}

	tail = p;
	head = V[tail - 1].parent + 1;
}

//---------------------------------------------------------------------------
void finder::regenerate ()
{
// restore head_depth and next_depth_start:
	head_depth = vertex_depth (head);

	index_t start = 1;
	for (int n = 1; n <= head_depth; n++) {
		// here start is the first node with depth = n
		index_t p = start; 
		while ((V[p].parent < start) and (p < tail))
			p++;
		start = p;
	}
	next_depth_start = start;

	assert (vertex_depth (start - 1) == head_depth);
	assert (((start < tail) ? (vertex_depth (start) == head_depth + 1) : 1));
}

//---------------------------------------------------------------------------
void finder::input_sanity_check ()
{
	const int max_width = 8 * sizeof (row_t);

	assert ((width >= 0) and (width < max_width));
	assert ((left_edge >= 0) and (left_edge < max_width));

#ifdef FLOATING_ROWS
	assert (floating_rows == 1);
#else
	assert (floating_rows == 0);
#endif // FLOATING_ROWS

	assert (period >= 0);

#ifndef REVERSE
	assert (offset >= 0);
#else
	assert (offset <= 0);
#endif // REVERSE

	assert (slide >= 0);
	assert ((mode == asym) or (mode == odd_sym) or (mode == even_sym));

	assert ((queue_bits > 0) and (queue_bits < 30));
	assert ((hash_bits >= 0) and (hash_bits  < 30));

	if (hash_bits == 0)
		fprintf (stderr, "hashing disabled since hash_bits = 0\n");
}

//---------------------------------------------------------------------------
void finder::queue_sanity_check ()
{
	assert ((head >= 0) and (tail > 0) and (head <= tail));
	assert (tail <= index_t (1 << queue_bits));

	index_t true_head = V[tail - 1].parent + 1;
	if (head and (head != true_head)) {
		fprintf (stderr, "sanity_check: head is %d, should be %d, fixed\n", head, true_head);
		head = true_head;
	}

	bool need_cleanup = false;
	int num_empty_nodes = 0;

	assert (!V[0].is_empty ());

	for (index_t p = 0; p < tail; p++) {
		if (p and V[p].is_empty ()) {
			need_cleanup = true;
			num_empty_nodes++;
		} else {
			index_t parent = V[p].parent;
			assert ((parent >= 0) and (parent < tail));
		}
	}

	if (need_cleanup) {
		fprintf (stderr, "queue has empty node(s), cleanup needed\n");

		int num_deleted_nodes = 0;

		for (index_t p = 0; p < tail; p++) {
			index_t parent = V[p].parent;
			if (!V[p].is_empty ()) if (V[parent].is_empty ()) V[p].make_empty ();

			if (V[p].is_empty ()) num_deleted_nodes++;
		}

		fprintf (stderr, "cleanup: got %d empty node(s), %d node(s) deleted\n", num_empty_nodes, num_deleted_nodes);
		collapse_gaps ();
	}

	int depth = vertex_depth (tail - 1);
	if (prev_depth != depth) {
		fprintf (stderr, "sanity_check: prev_depth is %d, should be %d, fixed\n", prev_depth, depth);
		prev_depth = depth;
	}
}

//---------------------------------------------------------------------------
void finder::prepare () throw (std::bad_alloc)
{
	input_sanity_check ();

	if (slide) {
		fprintf (stderr, "slide is nonzero, asymmetrical mode forced\n");
		mode = asym;
	}

	parse_rule_string (rule_string);
	fill_lookup_tables ();

	switch (mode) {
	case asym:     full_width = width; break;
	case even_sym: full_width = 2 * width; break;
	case odd_sym:  full_width = 2 * width - 1; break;
	}

	rows_in_state = 2 * period;

	rounded_width = ((mode > asym) ? 16 : 8) * sizeof (row_t);

	gap = 0;

	F  = new int[5 * period];
	B  = F + period;
	FF = F + 2 * period;
	BB = F + 3 * period;
	D  = F + 4 * period;

	wrap = gcd (period, offset);
	int cowrap = period / wrap;

	int slide_gcd = gcd (period, slide);
	int slide_period = period / slide_gcd;
	int small_slide = slide / slide_gcd;

	if (slide and (left_edge < slide_gcd)) {
		left_edge = slide_gcd;
		fprintf (stderr, "setting left_edge = %d\n", left_edge);
	}

	int k;
	for (k = 0; k < period; k++)
		D[k] = 0;

	k = 0;
	for (int m = 0; m < period; m++) {
		F[k] = offset + (((m + 1) % cowrap) == 0);
		if ((m + 1) % period == 0) F[k] -= wrap;
		if (m % slide_period == 0) D[(k + 1) % period] = small_slide;
		k = (k + F[k] + period) % period;
	}

	int tmp = F[period - 1];
	for (k = period - 1; k > 0; k--) F[k] = F[k - 1];
	F[0] = tmp;

	for (k = 0; k < period; k++) B [(period + k + F[k]) % period] = F[k];
	for (k = 0; k < period; k++) BB[(period + k + F[k]) % period] = F[k] + B[k];
	for (k = 0; k < period; k++) FF[(period + k + B[k]) % period] = F[k] + B[k];

	queue_size = 1 << queue_bits;
	hash_size  = 1 << hash_bits;

	V    = new vertex_t[queue_size];
	hash = new index_t [hash_size];
}

//---------------------------------------------------------------------------
void finder::reset_search ()
{
	counter = 0;
	X = Y = 0;

	prev_depth = 0;
	depth_step = depth_limit = period;

	V[0].clear ();		// => "row" is empty and "parent" is itself

	head = head_depth = 0;
	next_depth_start = tail = 1;

// looking for sparkers:
/*
	for (tail = 1; int (tail) < 2 * period; tail++) {
		V[tail].row = 0;
		V[tail].parent = tail - 1;
	}
	V[1].row = 1;
	V[period + 1].row = 4;

	head = tail - 1;
	head_depth = vertex_depth (head);
	next_depth_start = tail;
*/
	ready = true;
}

//---------------------------------------------------------------------------
void finder::search ()
{
	assert (ready);

	fprint_banner (stdout);

	bool finished = false;
	num_hits = num_cycles = 0;

	while (!finished) {
		build_hash ();
		
		while (head < tail) {
			if (!find_matching_rows (head, head_depth))
				break;
			if ((++head) == next_depth_start) {
				head_depth++;
				next_depth_start = tail;
			}
		}

		if (head == tail)
			finished = true;
		else {
			fprintf (stderr, "\n");
			finished = !compactify (); // finish if search frontier is empty
			if (!finished) {
				save (filename);
				save_preview ("preview");
			}
		}
	}

	fputc ('\n', stderr);

//	save (filename);
	show_levels ();

	pretty_fprint (stdout, tail - 1);

	fprintf (stderr, "search complete\n");
	fprintf (stderr, "%d object(s) found\n", counter);
}

//---------------------------------------------------------------------------
const char *finder::context_format =
"# search context:\n"
"head %u\n"
"tail %u\n"
"depth_step %d\n"
"prev_depth %d\n"
"depth_limit %d\n"
"counter %d\n"
"X %d\n"
"Y %d\n";

//---------------------------------------------------------------------------
finder::finder (const char *ifn) :
	V (NULL),
	hash (NULL),
	F (NULL),
	full_width (0),
	head (0), tail (0),
	counter (0),
	X (0), Y (0),
	ready (false),
	filename (NULL)
{
	if (ifn) {
		fprintf (stderr, "restoring search state from file: %s\n", ifn);
		filename = strdup (base_file_name (ifn));
		fprintf (stderr, "base filename: %s\n", filename);

		load (ifn);
	} else {
		prepare ();
		reset_search ();
	}
}

//---------------------------------------------------------------------------
finder::~finder ()
{
	free (filename);

	delete [] F;
	delete [] hash;
	delete [] V;
}

//---------------------------------------------------------------------------
void finder::fprint_banner (FILE *output)
{
	const char *mode_string[] = { "asymmetrical", "odd-bilateral symmetry", "even-bilateral symmetry" };

	const char *banner_format = 
		"#Life 1.05\n"
		"#D Generated by " PROGRAM ".\n"
		"#D Input parameters:\n"
		"#D  width  = %d (full_width = %d)\n"
		"#D  left_edge = %d\n"
		"#D  floating_rows = %d\n"
		"#D  period = %d\n"
		"#D  offset = %d\n"
		"#D  slide  = %d\n"
		"#D  mode   = %s\n"
		"#D  queue_size = 2^%d\n"
		"#D  hash_size  = 2^%d\n";

	fprintf (output, banner_format, width, full_width, left_edge, floating_rows,
		 period, offset, slide, mode_string[mode], queue_bits, hash_bits);

	fprintf (output, "#R %s\n\n", rule_string);

	fflush (output);
}

//---------------------------------------------------------------------------
void finder::load (const char *ifn)
{
	FILE *input;

	if ((input = fopen (ifn, "rb")) == NULL) {
		perror (ifn);
		throw std::runtime_error ("could not load file");
	}

	char header[32];
	fscanf (input, "%30s", header);
	goto_next_line (input);
	if (strcmp (header, PROGRAM))
		throw std::runtime_error ("input file should begin with \"" PROGRAM "\"");

	do {
		char c = getc (input);
		if (c == EOF) break;
		if (c == '\n') break;
		if (c == '#') {
			goto_next_line (input);
			continue;
		}
		ungetc (c, input);

		char name[80];
		if (fscanf (input, "%[a-z_]s", name) != 1)
			break;

		param_t *p = input_params;
		while (p->name and strcmp (name, p->name)) p++;
		if (p->name) {
			switch (p->type) {
			case 'i': fscanf (input, "%d",   (int*)  p->addr); break;
			case 's': fscanf (input, "%30s", (char*) p->addr); break;
			}
		} else
			fprintf (stderr, "unknown input parameter %s\n", name);

		goto_next_line (input);
	} while (true);

	prepare ();

	if (fscanf (input, context_format, &head, &tail,
		    &depth_step, &prev_depth, &depth_limit,
		    &counter, &X, &Y) != 8) {
		fprintf (stderr, "failed to read search context, starting from scratch\n");
		reset_search ();
	} else if (tail >= queue_size) {
		fprintf (stderr, "queue tail is outside the queue! starting from scratch\n");
		reset_search ();
	} else if (fread (V, sizeof (vertex_t), tail, input) != tail) {
		fprintf (stderr, "failed to read queue, starting from scratch\n");
		reset_search ();
	} else {
		queue_sanity_check ();
		regenerate ();
		ready = true;
	}

	fclose (input);
}

//---------------------------------------------------------------------------
bool finder::save (const char *ofn, bool full_save)
{
	char *real_ofn = safe_file_name (ofn);

	if (!real_ofn) return false;

	FILE *output;

	if ((output = fopen (real_ofn, "wb")) == NULL) {
		perror (ofn);
		return false;
	} else {
		fprintf (output, PROGRAM "\n");
		fprintf (output, "# %s", current_time ());
		fprintf (output, "# input data:\n");

		param_t *p = input_params;
		while (p->name) {
			switch (p->type) {
			case 'i': fprintf (output, "%s %d\n", p->name, *(int*)(p->addr)); break;
			case 's': fprintf (output, "%s %s\n", p->name, (char*)(p->addr)); break;
			}
			p++;
		}
		putc ('\n', output);

		if (full_save) {
			fprintf (output, context_format, head, tail,
				 depth_step, prev_depth, depth_limit,
				 counter, X, Y);

			fwrite (V, sizeof (vertex_t), tail, output);
		}

		fclose (output);
	}

	fprintf (stderr, "(wrote %s)\n", real_ofn);
	return true;
}

//---------------------------------------------------------------------------
void finder::show_levels ()
{
	fprintf (stderr, "levels:\n");

	index_t p = 1, q;
	while (p < tail) {
		for (q = p + 1; q < tail; q++)
			if (V[q].parent >= p) break;
		// parenthesize if the level is possibly incomplete
		fprintf (stderr, (q == tail and tail > head) ? "(%d) " : "%d ", q - p);
		p = q;
	}
/*
	q = tail;
	while (q > 1) {
		p = V[q - 1].parent + 1;
		fprintf (stderr, "%d ", q - p);
		q = p;
	}
*/
	fputc ('\n', stderr);
}

//---------------------------------------------------------------------------
void finder::save_best (const char *ofn)
{
	FILE *output;

	if ((output = fopen (ofn, "w")) == NULL) {
		perror (ofn);
		return;
	}

	fprint_banner (output);

	unsigned int div_min = (unsigned) (-1);
	index_t p_min = 0;

	index_t start = V[V[tail - 1].parent].parent + 1;
	index_t end = tail;

	fprintf (output, "#D depth is %d:\n", vertex_depth (tail - 1));

	for (index_t p = start; p < end; p++) {
		unsigned int div_p = difference (p);
		if (div_p <= div_min) {
			div_min = div_p;

			if (!compare_last_phase (p, p_min)) {
				fprintf (output, "#D node %u: difference %d\n", p, div_min);
				for (index_t q = p; q; ) {
					fprint_row (output, V[q].row);
					fprintf (output, "\n");
					for (int k = 0; k < period; k++)
						q = V[q].parent;
				}
				for (int k = 0; k < 2 * period; k++)
					fprintf (output, ".\n");
				fprintf (output, "\n");
			}
			p_min = p;
		}

		if ((p - start) % 100 == 0)
			fprintf (stderr, "[%u/%d/%d]\r", div_min, p - start, end - start);
	}
	fprintf (stderr, "\n");

	fclose (output);
	fprintf (stderr, "(wrote %s)\n", ofn);
}

//---------------------------------------------------------------------------
void finder::save_preview (const char *ofn)
{
	show_levels ();

	FILE *output;

	if ((output = fopen (ofn, "w")) == NULL) {
		perror (ofn);
		return;
	}

	fprint_banner (output);

	int X_save = X;
	int Y_save = Y;

	X = Y = 0;

	const int N = 10;	// number of paths to preview

	// the purpose here is to give preview of N maximally diverse branches
	int n = 0;		// number of paths currently being tracked
	index_t a[N];		// the paths being tracked
	index_t p, q;

	for (int k = 0; k < n; k++)
		a[k] = 0;

	p = a[0] = 1;
	n = 1;
	while (p < tail) {
		// p is the beginning of a level
		int k = 0;
		// q goes through the level; each of n known paths is advanced:
		for (q = p; (q < tail) and (V[q].parent < p); q++) {
			if (k < n) if (V[q].parent == a[k])
				a[k++] = q;
		}

		if (n < N) {
			int k_max = min (N, q - p);
			int shift = 1;
			k = n;
			while (k < k_max) {
				for (int i = 0; i < n; i++)
					if (a[i] + shift < ((i + 1 < n) ? a[i + 1] : q))
						a[k++] = a[i] + shift;
				shift++;
			}
			n = k_max;
			qsort (a, n, sizeof (int), compare_ints);
		}
		p = q;		// the beginning of next level
	}

	qsort (a, n, sizeof (int), compare_ints);
	for (int k = 0; k < n; k++)
		pretty_fprint (output, a[k]);

/*
	for (int k = 0; k < N; k++)
		pretty_fprint (output, (head * (n - k) + tail * k) / n);
*/

	X = X_save;
	Y = Y_save;

	fclose (output);
	fprintf (stderr, "(wrote %s)\n", ofn);
}

//---------------------------------------------------------------------------
void finder::truncate (const char *ofn)
{
	const int num_levels = rows_in_state;

	index_t p = V[tail - 1].parent + 1, q;

	for (int n = 1; n < num_levels; n++)
		p = V[p].parent;

	for (q = 1; q < p; q++)
		V[q].make_empty ();

	for (q = p; V[q].parent < p; q++)
		V[q].parent = 0;

	collapse_gaps ();

	regenerate ();

	prev_depth = head_depth;

	save (ofn);
}

//---------------------------------------------------------------------------
bool finder::compare_last_phase (index_t p, index_t q)
{
	do {
		if (V[p].row != V[q].row)
			return false;
		for (int k = 0; k < period; k++) {
			p = V[p].parent;
			q = V[q].parent;
		}
	} while (p or q);
	return true;
}

//---------------------------------------------------------------------------
int finder::difference (index_t p)
{
    int depth = vertex_depth (p);
    int margin = period + 2;
    int num_rows = round_up (depth, period) / period + 2 * margin;

    // row_t A[num_rows], B[num_rows], C[num_rows]; //this is the problem code that causes segfaults
    std::vector<row_t> A(num_rows), B(num_rows), C(num_rows);

    for (int k = 0; k < num_rows; k++)
        A[k] = B[k] = C[k] = 0;
        //A.push_back(0);
        //B.push_back(0);
        //C.push_back(0);

    for (int m = margin; p; m++) {
        A[m] = V[p].row;
        for (int k = 0; k < period; k++)
            p = V[p].parent;
    }

    for (int k = 0; k < num_rows; k++)
        B[k] = A[k] << slide;

    for (int t = 0; t < period; t++) {
        for (int k = 1; k < num_rows - 1; k++)
            C[k] = evolve (B[k - 1], B[k], B[k + 1]);
        for (int k = 0; k < num_rows; k++)
            B[k] = C[k];
    }

    int num = 0;
    for (int k = 0; k < num_rows; k++)
        if ((k + offset >= 0) and (k + offset < num_rows))
            num += count_bits (A[k] ^ B[k + offset]);
    return num;
}
//---------------------------------------------------------------------------
/*
void finder::asymmetrize (const char *ofn)
{
	if (mode == asym) {
		fprintf (stderr, "asymmetrize: mode is already asymmetrical\n");
		return;
	}

	if (full_width >= 30) {
		fprintf (stderr, "asymmetrize: width is too big\n");
		return;
	}
		
	int shift = full_width - width;
	width = full_width;
	mode = asym;
	X = Y = counter = 0;

	for (index_t p = 0; p < tail; p++) {
		V[p].row <<= shift;
		for (int k = 0; k < shift; k++)
			if (V[p].row & (1 << (full_width - 1 - k)))
				V[p].row |= (1 << k);
	}

	regenerate ();

	save (ofn);
}

//---------------------------------------------------------------------------
void finder::widen_left (const char *ofn)
{
	if (mode != asym) {
		fprintf (stderr, "widen_left: mode should be asymmetrical\n");
		return;
	}

	width++;
	X = Y = counter = 0;

	for (index_t p = 0; p < tail; p++)
		V[p].row <<= 1;

	regenerate ();

	save (ofn);
}
*/

//---------------------------------------------------------------------------
int main (int argc, char **argv)
{
	try {
		enum {
			search, scratch, preview, find_best,
//			asymmetrize, widen_left,
			truncate,
			help
		} what_to_do = search;

		const char *usage =
			"Usage: %s [<action>] [[-f] <file>] [-o <output_file>]\n\n"
			"The default action is search;\n"
			"if <file> is given, restore search state from <file>.\n\n"
			"Search results are sent to stdout,\n"
			"intermediate search states are saved as <file>.1, <file>.2, etc.\n\n"
			"Other actions are:\n"
			"  -h\tprint this message\n"
			"  -s\twrite a sample initial search state to <file> (default 'scratch')\n"
			"  -p\ttake a search state from <file> and\n"
			"\twrite its preview to <output_file> (default 'preview')\n"
			"  -b\twrite the best search branch(es) from <file> to <output_file> (default 'best')\n"
//			"  -a\tasymmetrize the state in <file> and save it to <output_file>\n"
//			"  -w\twiden the state in <file> and save it to <output_file>\n"
			"  -t\ttruncate (by leaving only last 2*p levels)\n"
			"\tthe state in <file> and save it to <output_file>\n"
			"\n";
		const char *need_ofn = "Use '-o <file>' to specify output file name\n";
		const char *need_fn  = "Need a filename, use '-h' for help\n";

		char *fn = NULL, *ofn = NULL;

		for (int k = 1; k < argc; k++) {
			if (argv[k][0] == '-') switch (argv[k][1]) {
			case 'f': if (++k < argc) fn  = argv[k]; break;
			case 'o': if (++k < argc) ofn = argv[k]; break;
			case 's': what_to_do = scratch; break;
			case 'p': what_to_do = preview; break;
			case 'b': what_to_do = find_best; break;
//			case 'a': what_to_do = asymmetrize; break;
//			case 'w': what_to_do = widen_left;  break;
			case 't': what_to_do = truncate;  break;
			case 'h': what_to_do = help; break;
			} else
				fn = argv[k];
		}

		switch (what_to_do) {
		case search: {
#ifdef BACKGROUND
			int priority = 15;
			if (setpriority (PRIO_PROCESS, 0, priority) == 0)
				fprintf (stderr, "running with priority %d\n", priority);
			else {
				perror ("setpriority");
				return 1;
			}
#endif // BACKGROUND
			fprintf (stderr, "%s", current_time ());
			finder (fn).search ();
			fprintf (stderr, "%s", current_time ());
		} break;

		case scratch: finder (NULL).save (fn ? fn : "scratch"); break;
		case preview:
			if (fn)
				finder (fn).save_preview (ofn ? ofn : "preview");
			else
				fprintf (stderr, need_fn);
			break;
		case find_best:
			if (fn)
				finder (fn).save_best (ofn ? ofn : "best");
			else
				fprintf (stderr, need_fn);
			break;
/*
		case asymmetrize: if (ofn) finder (fn).asymmetrize (ofn); else fprintf (stderr, need_ofn); break;
		case widen_left:  if (ofn) finder (fn).widen_left  (ofn); else fprintf (stderr, need_ofn); break;
*/
		case truncate: if (ofn) finder (fn).truncate (ofn); else fprintf (stderr, need_ofn); break;
		default: printf (usage, argv[0]); break;
		}

#ifdef PROFILE
		fprintf (stderr, "some_counter = %Lu\n", some_counter);
#endif

	} catch (std::exception &e) {
		fprintf (stderr, "exception: %s\n", e.what ());
	}

	return 0;
}

//---------------------------------------------------------------------------
