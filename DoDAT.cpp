/*
 *  DoDAT
 *
 *  This program is free software; you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation; either version 2 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License along
 *  with this program; if not, write to the Free Software Foundation, Inc.,
 *  51 Franklin Street, Fifth Floor, Boston, MA 02110-1301, USA.
 */

#include <memory.h>
#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>
#include <string.h>
#include <time.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <vector>
#include <string>
#ifdef _WIN32
#include <windows.h>
#else
#include <dirent.h>
#include <unistd.h>
#endif

typedef unsigned char Bit8u;
typedef unsigned short Bit16u;
typedef signed short Bit16s;
typedef unsigned int Bit32u;
typedef signed int Bit32s;
#ifndef _MSC_VER
typedef unsigned long long Bit64u;
typedef signed long long Bit64s;
#else
typedef unsigned __int64 Bit64u;
typedef signed __int64 Bit64s;
#define strcasecmp(a,b) stricmp(a,b)
#define strncasecmp(a,b,n) _strnicmp(a,b,n)
#ifndef va_copy
#define va_copy(d,s) ((d) = (s))
#endif
#endif

// Use 64-bit fseek and ftell
#if defined(_MSC_VER) && _MSC_VER >= 1400 // VC2005 and up have a special 64-bit fseek
#define fseek_wrap(fp, offset, whence) _fseeki64(fp, (__int64)offset, whence)
#define ftell_wrap(fp) _ftelli64(fp)
#elif defined(HAVE_64BIT_OFFSETS) || (defined(_POSIX_C_SOURCE) && (_POSIX_C_SOURCE - 0) >= 200112) || (defined(__POSIX_VISIBLE) && __POSIX_VISIBLE >= 200112) || (defined(_POSIX_VERSION) && _POSIX_VERSION >= 200112) || __USE_LARGEFILE || (defined(_FILE_OFFSET_BITS) && _FILE_OFFSET_BITS == 64)
#define fseek_wrap(fp, offset, whence) fseeko(fp, (off_t)offset, whence)
#define ftell_wrap(fp) ftello(fp)
#else
#define fseek_wrap(fp, offset, whence) fseek(fp, (long)offset, whence)
#define ftell_wrap(fp) ftell(fp)
#endif
static Bit8u ReadBuf[1024 * 512];

static void LogErr(const char* fmt, ...) { va_list ap; va_start(ap, fmt); vfprintf(stderr, fmt, ap); va_end(ap); fflush(stderr); }
static void Log(const char* fmt, ...) { va_list ap; va_start(ap, fmt); vfprintf(stdout, fmt, ap); va_end(ap); fflush(stdout); }

static Bit32u CRC32(const void* data, size_t data_size, Bit32u crc = 0)
{
	// A compact CCITT crc16 and crc32 C implementation that balances processor cache usage against speed
	// By Karl Malbrain - http://www.geocities.ws/malbrain/
	static const Bit32u s_crc32[16] = { 0, 0x1db71064, 0x3b6e20c8, 0x26d930ac, 0x76dc4190, 0x6b6b51f4, 0x4db26158, 0x5005713c, 0xedb88320, 0xf00f9344, 0xd6d6a3e8, 0xcb61b38c, 0x9b64c2b0, 0x86d3d2d4, 0xa00ae278, 0xbdbdf21c };
	crc = (Bit32u)~(Bit32u)crc;
	for (Bit8u b, *p = (Bit8u*)data; data_size--;) { b = *p++; crc = (crc >> 4) ^ s_crc32[(crc & 0xF) ^ (b & 0xF)]; crc = (crc >> 4) ^ s_crc32[(crc & 0xF) ^ (b >> 4)]; }
	return ~crc;
}

static void RawUnCRC32(Bit32u crc, Bit8u data_size, Bit8u* out_data) // no ~ bit flipping on input and output
{
	for (int i = 0; i != (data_size * 8); i++)
		crc = ((crc >> 31) ? (((crc ^ 0xEDB88320) << 1) | 1) : (crc << 1));
	for (int j = 0; j != data_size; crc >>= 8, j++)
		out_data[j] = (crc & 255);
}

struct SHA1_CTX
{
	// BASED ON SHA-1 in C (public domain)
	// By Steve Reid - https://github.com/clibs/sha1
	SHA1_CTX()
	{
		count[0] = count[1] = 0;
		state[0] = 0x67452301;
		state[1] = 0xEFCDAB89;
		state[2] = 0x98BADCFE;
		state[3] = 0x10325476;
		state[4] = 0xC3D2E1F0;
	}
	void Process(const Bit8u* data, size_t len)
	{
		size_t i; Bit32u j = count[0];
		if ((count[0] += (Bit32u)(len << 3)) < j) count[1]++;
		count[1] += (Bit32u)(len>>29);
		j = (j >> 3) & 63;
		if ((j + len) > 63)
		{
			memcpy(&buffer[j], data, (i = 64-j));
			Transform(state, block);
			for (; i + 63 < len; i += 64)
			{
				//Bit32u* block = (Bit32u*)&data[i]; // Destructive (buffer will be modified in place)
				memcpy(block, &data[i], 64); // Non destructive (can have input buffer be const)
				Transform(state, block);
			}
			j = 0;
		}
		else i = 0;
		memcpy(&buffer[j], &data[i], len - i);
	}
	void Finish(Bit8u res[20])
	{
		Bit8u finalcount[8];
		for (unsigned i = 0; i < 8; i++)  finalcount[i] = (Bit8u)((count[(i >= 4 ? 0 : 1)] >> ((3-(i & 3)) * 8) ) & 255);
		Bit8u c = 0200;
		Process(&c, 1);
		while ((count[0] & 504) != 448) { c = 0000; Process(&c, 1); }
		Process(finalcount, 8);
		for (unsigned j = 0; j < 20; j++) res[j] = (Bit8u)((state[j>>2] >> ((3-(j & 3)) * 8) ) & 255);
	}
	static void Run(const Bit8u* data, size_t data_size, Bit8u res[20])
	{
		SHA1_CTX ctx;
		ctx.Process(data, data_size);
		ctx.Finish(res);
	}
	private: Bit32u count[2], state[5]; union { Bit8u buffer[64]; Bit32u block[16]; };
	static void Transform(Bit32u* state, Bit32u block[16])
	{
		Bit32u a = state[0], b = state[1], c = state[2], d = state[3], e = state[4];
		#define SHA1ROL(value, bits) (((value) << (bits)) | ((value) >> (32 - (bits))))
		#ifdef WORDS_BIGENDIAN
		#define SHA1BLK0(i) block[i]
		#else
		#define SHA1BLK0(i) (block[i] = (SHA1ROL(block[i],24)&0xFF00FF00)|(SHA1ROL(block[i],8)&0x00FF00FF))
		#endif
		#define SHA1BLK(i) (block[i&15] = SHA1ROL(block[(i+13)&15]^block[(i+8)&15]^block[(i+2)&15]^block[i&15],1))
		#define SHA1R0(v,w,x,y,z,i) z+=((w&(x^y))^y)+SHA1BLK0(i)+0x5A827999+SHA1ROL(v,5);w=SHA1ROL(w,30);
		#define SHA1R1(v,w,x,y,z,i) z+=((w&(x^y))^y)+SHA1BLK(i)+0x5A827999+SHA1ROL(v,5);w=SHA1ROL(w,30);
		#define SHA1R2(v,w,x,y,z,i) z+=(w^x^y)+SHA1BLK(i)+0x6ED9EBA1+SHA1ROL(v,5);w=SHA1ROL(w,30);
		#define SHA1R3(v,w,x,y,z,i) z+=(((w|x)&y)|(w&x))+SHA1BLK(i)+0x8F1BBCDC+SHA1ROL(v,5);w=SHA1ROL(w,30);
		#define SHA1R4(v,w,x,y,z,i) z+=(w^x^y)+SHA1BLK(i)+0xCA62C1D6+SHA1ROL(v,5);w=SHA1ROL(w,30);
		SHA1R0(a,b,c,d,e, 0); SHA1R0(e,a,b,c,d, 1); SHA1R0(d,e,a,b,c, 2); SHA1R0(c,d,e,a,b, 3);
		SHA1R0(b,c,d,e,a, 4); SHA1R0(a,b,c,d,e, 5); SHA1R0(e,a,b,c,d, 6); SHA1R0(d,e,a,b,c, 7);
		SHA1R0(c,d,e,a,b, 8); SHA1R0(b,c,d,e,a, 9); SHA1R0(a,b,c,d,e,10); SHA1R0(e,a,b,c,d,11);
		SHA1R0(d,e,a,b,c,12); SHA1R0(c,d,e,a,b,13); SHA1R0(b,c,d,e,a,14); SHA1R0(a,b,c,d,e,15);
		SHA1R1(e,a,b,c,d,16); SHA1R1(d,e,a,b,c,17); SHA1R1(c,d,e,a,b,18); SHA1R1(b,c,d,e,a,19);
		SHA1R2(a,b,c,d,e,20); SHA1R2(e,a,b,c,d,21); SHA1R2(d,e,a,b,c,22); SHA1R2(c,d,e,a,b,23);
		SHA1R2(b,c,d,e,a,24); SHA1R2(a,b,c,d,e,25); SHA1R2(e,a,b,c,d,26); SHA1R2(d,e,a,b,c,27);
		SHA1R2(c,d,e,a,b,28); SHA1R2(b,c,d,e,a,29); SHA1R2(a,b,c,d,e,30); SHA1R2(e,a,b,c,d,31);
		SHA1R2(d,e,a,b,c,32); SHA1R2(c,d,e,a,b,33); SHA1R2(b,c,d,e,a,34); SHA1R2(a,b,c,d,e,35);
		SHA1R2(e,a,b,c,d,36); SHA1R2(d,e,a,b,c,37); SHA1R2(c,d,e,a,b,38); SHA1R2(b,c,d,e,a,39);
		SHA1R3(a,b,c,d,e,40); SHA1R3(e,a,b,c,d,41); SHA1R3(d,e,a,b,c,42); SHA1R3(c,d,e,a,b,43);
		SHA1R3(b,c,d,e,a,44); SHA1R3(a,b,c,d,e,45); SHA1R3(e,a,b,c,d,46); SHA1R3(d,e,a,b,c,47);
		SHA1R3(c,d,e,a,b,48); SHA1R3(b,c,d,e,a,49); SHA1R3(a,b,c,d,e,50); SHA1R3(e,a,b,c,d,51);
		SHA1R3(d,e,a,b,c,52); SHA1R3(c,d,e,a,b,53); SHA1R3(b,c,d,e,a,54); SHA1R3(a,b,c,d,e,55);
		SHA1R3(e,a,b,c,d,56); SHA1R3(d,e,a,b,c,57); SHA1R3(c,d,e,a,b,58); SHA1R3(b,c,d,e,a,59);
		SHA1R4(a,b,c,d,e,60); SHA1R4(e,a,b,c,d,61); SHA1R4(d,e,a,b,c,62); SHA1R4(c,d,e,a,b,63);
		SHA1R4(b,c,d,e,a,64); SHA1R4(a,b,c,d,e,65); SHA1R4(e,a,b,c,d,66); SHA1R4(d,e,a,b,c,67);
		SHA1R4(c,d,e,a,b,68); SHA1R4(b,c,d,e,a,69); SHA1R4(a,b,c,d,e,70); SHA1R4(e,a,b,c,d,71);
		SHA1R4(d,e,a,b,c,72); SHA1R4(c,d,e,a,b,73); SHA1R4(b,c,d,e,a,74); SHA1R4(a,b,c,d,e,75);
		SHA1R4(e,a,b,c,d,76); SHA1R4(d,e,a,b,c,77); SHA1R4(c,d,e,a,b,78); SHA1R4(b,c,d,e,a,79);
		state[0] += a; state[1] += b; state[2] += c; state[3] += d; state[4] += e;
	}
};

#define ZIP_MAX(a,b) (((a)>(b))?(a):(b))
#define ZIP_MIN(a,b) (((a)<(b))?(a):(b))
#define ZIP_READ_LE16(p) ((Bit16u)(((const Bit8u *)(p))[0]) | ((Bit16u)(((const Bit8u *)(p))[1]) << 8U))
#define ZIP_READ_LE32(p) ((Bit32u)(((const Bit8u *)(p))[0]) | ((Bit32u)(((const Bit8u *)(p))[1]) << 8U) | ((Bit32u)(((const Bit8u *)(p))[2]) << 16U) | ((Bit32u)(((const Bit8u *)(p))[3]) << 24U))
#define ZIP_READ_LE64(p) ((Bit64u)(((const Bit8u *)(p))[0]) | ((Bit64u)(((const Bit8u *)(p))[1]) << 8U) | ((Bit64u)(((const Bit8u *)(p))[2]) << 16U) | ((Bit64u)(((const Bit8u *)(p))[3]) << 24U) | ((Bit64u)(((const Bit8u *)(p))[4]) << 32U) | ((Bit64u)(((const Bit8u *)(p))[5]) << 40U) | ((Bit64u)(((const Bit8u *)(p))[6]) << 48U) | ((Bit64u)(((const Bit8u *)(p))[7]) << 56U))
#define ZIP_READ_BE32(p) ((Bit32u)((((const Bit8u *)(p))[0] << 24) | (((const Bit8u *)(p))[1] << 16) | (((const Bit8u *)(p))[2] << 8) | ((const Bit8u *)(p))[3]))
#define ZIP_READ_BE64(p) ((Bit64u)((((Bit64u)((const Bit8u *)(p))[0] << 56) | ((Bit64u)((const Bit8u *)(p))[1] << 48) | ((Bit64u)((const Bit8u *)(p))[2] << 40) | ((Bit64u)((const Bit8u *)(p))[3] << 32) | ((Bit64u)((const Bit8u *)(p))[4] << 24) | ((Bit64u)((const Bit8u *)(p))[5] << 16) | ((Bit64u)((const Bit8u *)(p))[6] << 8) | (Bit64u)((const Bit8u *)(p))[7])))
#define ZIP_WRITE_LE16(b,v) { (b)[0] = (Bit8u)((Bit16u)(v)); (b)[1] = (Bit8u)((Bit16u)(v) >> 8); }
#define ZIP_WRITE_BE16(b,v) { (b)[0] = (Bit8u)((Bit16u)(v) >> 8); (b)[1] = (Bit8u)((Bit16u)(v)); }
#define ZIP_WRITE_LB16(b,v) { ZIP_WRITE_LE16(b,v) ZIP_WRITE_BE16((b+2),v) }
#define ZIP_WRITE_LE32(b,v) { (b)[0] = (Bit8u)((Bit32u)(v)); (b)[1] = (Bit8u)(((Bit32u)(v) >> 8)); (b)[2] = (Bit8u)(((Bit32u)(v) >> 16)); (b)[3] = (Bit8u)((Bit32u)(v) >> 24); }
#define ZIP_WRITE_BE32(b,v) { (b)[0] = (Bit8u)((Bit32u)(v) >> 24); (b)[1] = (Bit8u)(((Bit32u)(v) >> 16)); (b)[2] = (Bit8u)(((Bit32u)(v) >> 8)); (b)[3] = (Bit8u)((Bit32u)(v)); }
#define ZIP_WRITE_BE64(b,v) { (b)[0] = (Bit8u)((Bit64u)(v) >> 56); (b)[1] = (Bit8u)((Bit64u)(v) >> 48); (b)[2] = (Bit8u)((Bit64u)(v) >> 40); (b)[3] = (Bit8u)((Bit64u)(v) >> 32); (b)[4] = (Bit8u)((Bit64u)(v) >> 24); (b)[5] = (Bit8u)((Bit64u)(v) >> 16); (b)[6] = (Bit8u)((Bit64u)(v) >> 8); (b)[7] = (Bit8u)(Bit64u)(v); }
#define ZIP_WRITE_LB32(b,v) { ZIP_WRITE_LE32(b,v) ZIP_WRITE_BE32((b+4),v) }
#define ZIP_PACKDATE(year,mon,day) (Bit16u)((((year)-1980)&0x7f)<<9 | ((mon)&0x3f) << 5 | ((day)&0x1f))
#define ZIP_PACKTIME(hour,min,sec) (Bit16u)(((hour)&0x1f)<<11 | ((min)&0x3f) << 5 | (((sec)/2)&0x1f))

#ifdef NDEBUG
#define ZIP_ASSERT(cond)
#else
#define ZIP_ASSERT(cond) (void)((cond) ? ((int)0) : *(volatile int*)0 |= 0xbad|fprintf(stderr, "FAILED ASSERT (%s)\n", #cond))
#endif
#define _ZIP_STATIC_ASSERTM(A,B) static_assertion_##A##_##B
#define _ZIP_STATIC_ASSERTN(A,B) _ZIP_STATIC_ASSERTM(A,B)
#define ZIP_STATIC_ASSERT(cond) enum { _ZIP_STATIC_ASSERTN(__LINE__,__COUNTER__) = 1/((cond)?1:0) }

static FILE* fopen_utf8(const char* path, const char* mode)
{
	#ifdef _WIN32
	bool needw = false;
	for (const char* p = path; *p; p++) { if ((Bit8u)*p > 0x7F) { needw = true; break; } }
	if (needw)
	{
		WCHAR wpath[MAX_PATH+5], wmode[20], *pwmode = wmode;
		MultiByteToWideChar(CP_UTF8, 0, path, -1, wpath, MAX_PATH);
		for (const char* p = mode, *pEnd = p + 19; *p && p != pEnd; p++) *(pwmode++) = *p;
		*pwmode = '\0';
		return _wfopen(wpath, wmode);
	}
	#endif
	return fopen(path, mode);
}

static bool stat_utf8(const char* path, Bit16u* date = NULL, Bit16u* time = NULL)
{
	time_t mtime;
	#ifdef _WIN32
	bool needw = false;
	for (const char* p = path; *p; p++) { if ((Bit8u)*p > 0x7F) { needw = true; break; } }
	if (needw)
	{
		WCHAR wpath[MAX_PATH+5];
		MultiByteToWideChar(CP_UTF8, 0, path, -1, wpath, MAX_PATH);
		struct _stat64i32 wres;
		if (_wstat64i32(wpath, &wres)) return false;
		mtime = wres.st_mtime;
	}
	else
	#endif
	{
		struct stat res;
		if (stat(path, &res)) return false;
		mtime = res.st_mtime;
	}
	struct tm *mtm = localtime(&mtime);
	if (date) *date = ZIP_PACKDATE(mtm->tm_year+1900, mtm->tm_mon + 1, mtm->tm_mday);
	if (time) *time = ZIP_PACKTIME(mtm->tm_hour, mtm->tm_min, mtm->tm_sec);
	return true;
}

static Bit64u atoi64(const char* p, int radix = 10)
{
	for (Bit64u res = 0;; p++)
	{
		char c = *p;
		if (c >= '0' && c <= '9') res = (res * radix) + (c - '0');
		else if (c >= 'a' && c <= ('a'-10)+radix) res = (res * radix) + (c - ('a'-10));
		else if (c >= 'A' && c <= ('A'-10)+radix) res = (res * radix) + (c - ('A'-10));
		else return res;
	}
}

static bool hextouint8(const char* hex, Bit8u* res, int len)
{
	for (int i = 0, b; i != len; res[i] = (Bit8u)b, i++)
	{
		char h1 = hex[i*2], c1 = h1&(h1>='a'?0x4f:0xff); if (!c1) return false; char h2 = hex[i*2+1], c2 = h2&(h2>='a'?0x4f:0xff);
		int i1 = (c1 - (c1 <= '9' ? '0' : (c1 < 'A' ? 255 : (c1 <= 'F' ? ('A'-10) : 255))));
		int i2 = (c2 - (c2 <= '9' ? '0' : (c2 < 'A' ? 255 : (c2 <= 'F' ? ('A'-10) : 255))));
		if ((b = ((i1<<4) | i2)) < 0) return false;
	}
	return true;
}

static void PathGetExt(const char* path, size_t len, const char*& ext3, const char*& ext4)
{
	ext3 = (len > 4 && path[len - 4] == '.' ? path + len - 3 : NULL);
	ext4 = (!ext3 && len > 5 && path[len - 5] == '.' ? path + len - 4 : NULL);
}

enum EXml { XML_END = 0, XML_ELEM_START, XML_ELEM_END, XML_ELEM_SOLO, XML_TEXT };
static EXml XMLParse(char*& pStart, char*& pEnd)
{
	char* p = pStart;
	while (*p <= ' ') { if (!*p) return XML_END; p++; }
	pStart = p;
	if (*p == '<')
	{
		while (*p != '>') if (!*(p++)) return XML_END;
		pEnd = p + 1;
		if (pStart[1] == '?' || pStart[1] == '!') // skip XML instructions and syntax elements
		{
			// Skip past XML comments (`<!--  ... -->`)
			if (pStart[1] == '!' && pStart[2] == '-' && pStart[3] == '-') { p = pStart + 3; while (p[0] != '-' || p[1] != '-' || p[2] != '>') if (!*(p++)) return XML_END; pEnd = p + 3; }
			// Skip past DTD DOCTYPE (tags inside tags, it looks like `<!DOCTYPE name [ <!ELEMENT...>... ]>`
			else if (pStart[1] == '!') for (p = pStart; p != pEnd; p++) if (*p == '[') { while (*p) if (*(p++) == ']') { while (*p != '>') if (!*(p++)) return XML_END; return XMLParse(pStart = ++p, pEnd); } return XML_END; }
			return XMLParse(pStart = pEnd, pEnd);
		}
		return (p[-1] == '/' ? XML_ELEM_SOLO : (pStart[1] == '/' ? XML_ELEM_END : XML_ELEM_START));
	}
	while (*p != '<' && *p) p++;
	while (p[-1] <= ' ') p--;
	pEnd = p;
	return XML_TEXT;
}

static bool XMLMatchTag(char* pStart, char* pEnd, const char* tag, int tagLen, ...)
{
	ZIP_ASSERT(pStart[0] == '<' && pEnd[-1] == '>');
	int elemLen = (int)((pEnd -= (pEnd[-2] == '/' ? 2 : 1)) - (++pStart));
	if (elemLen < tagLen || memcmp(pStart, tag, tagLen) || (pStart[tagLen] != '>' && pStart[tagLen] != '/' && pStart[tagLen] != ' ')) return false;

	va_list apStart, ap;
	va_start(apStart, tagLen);
	va_copy(ap, apStart);
	int matchCount = 0, matchLens[64], n;
	for (const char *matchParam, **matchOut, **matchEndOut; (matchParam = va_arg(ap, const char*)) != NULL; matchCount++)
	{
		matchLens[matchCount] = (int)strlen(matchParam);
		*(matchOut = va_arg(ap, const char**)) = NULL;
		if ((matchEndOut = va_arg(ap, const char**)) != NULL) *matchEndOut = NULL;
	}
	va_end(ap);
	ZIP_ASSERT(matchCount < 64);

	Bit64u matchedBits = 0, bit;
	for (char* p = pStart + tagLen;;)
	{
		while (*p <= ' ') p++;
		if (p == pEnd) { va_end(apStart); return true; }
		const char *paramName = p;
		while (*p > ' ' && *p != '=') p++;
		const char *paramNameEnd = p, *val = NULL, *valEnd = NULL;
		while (*p <= ' ') p++;
		if (*p == '=')
		{
			p++;
			while (*p <= ' ') p++;
			if (*p == '"') { val = ++p; while (*p != '"' && p != pEnd) p++; valEnd = p; if (*p == '"') p++; }
			else { val = p; while (*p > ' ' && p != pEnd) p++; valEnd = p; }
		}

		va_copy(ap, apStart);
		for (n = 0, bit = 1; n != matchCount; n++, bit <<= 1)
		{
			const char *matchParam = va_arg(ap, const char*), **matchOut = va_arg(ap, const char**), **matchEndOut = va_arg(ap, const char**);
			if ((matchedBits & bit) || *matchParam != *paramName || matchLens[n] != (int)(paramNameEnd - paramName) || memcmp(paramName, matchParam, matchLens[n])) continue;
			*matchOut = val;
			if (matchEndOut) *matchEndOut = valEnd;
			matchedBits |= bit;
		}
		va_end(ap);
	}
}

static char* XMLLevel(char* p, EXml x = XML_END, char** textStart = NULL, char** textEnd = NULL)
{
	if (x && x != XML_ELEM_START) return p;
	int depth = (x ? 1 : 0), hadDepth = depth;
	for (char* pEnd = NULL;; p = pEnd)
	{
		if ((x = XMLParse(p, pEnd)) == XML_END) return NULL;
		if (x == XML_ELEM_START) { hadDepth = 1; ++depth; }
		if (x == XML_ELEM_END && --depth <= 0) return ((hadDepth && !depth) ? pEnd : NULL);
		if (x == XML_ELEM_SOLO && !depth) return pEnd;
		if (x == XML_TEXT && depth == 1 && textStart) { *textStart = p; *textEnd = pEnd; }
	}
}

static void XMLInlineStringConvert(char* pStart, char*& pEnd)
{
	char *p = pStart, *pLast = pEnd;
	for (char *pIn = p; pIn != pLast;)
		if ((*(p++) = *(pIn++)) != '&') continue;
		else if (!strncmp(p, "amp;", 4)) pIn += 4;
		else if (!strncmp(p, "lt;", 3)) { p[-1] = '<'; pIn += 3; }
		else if (!strncmp(p, "gt;", 3)) { p[-1] = '>'; pIn += 3; }
	pEnd = p;
	if (p != pLast && *pLast != '<') *(p++) = *(pLast++); // move over the string closing ' or ", then fill spaces afterwards
	for (; p != pLast;) *(p++) = ' '; // fill with spaces to keep XML valid (unless < or > were inserted...)
}

struct SFile
{
	std::string path; Bit64u size; Bit16u date, time; Bit32u crc32; Bit8u sha1[20]; bool have_crc32, have_sha1, was_matched;
	enum : Bit8u { T_RAW, T_MEMORY, T_ZIP, T_ISO, T_FAT } typ;
	inline SFile() : date(0), time(0), have_crc32(false), have_sha1(false), was_matched(false) { }
	virtual inline ~SFile() { }
	virtual bool Open() = 0;
	virtual bool IsOpen() = 0;
	virtual bool Close() = 0;
	virtual Bit64u Read(Bit8u* data, Bit64u len) = 0;
	//virtual Bit64u Write(const Bit8u* data, Bit64u len) { return 0; }
	virtual Bit64u Seek(Bit64s ofs, int origin = SEEK_SET) = 0;

	Bit32u GetCRC32()
	{
		if (have_crc32) return crc32;
		crc32 = 0;
		if (size)
		{
			bool wasOpen = IsOpen();
			if (wasOpen) Seek(0); else Open();
			for (Bit64u sz; (sz = Read(ReadBuf, sizeof(ReadBuf))) != 0;) crc32 = CRC32(ReadBuf, (size_t)sz, crc32);
			if (!wasOpen) Close();
		}
		have_crc32 = true;
		return crc32;
	}
	const Bit8u* GetSHA1()
	{
		if (have_sha1) return sha1;
		SHA1_CTX ctx;
		if (size)
		{
			bool wasOpen = IsOpen();
			if (wasOpen) Seek(0); else Open();
			for (Bit64u sz; (sz = Read(ReadBuf, sizeof(ReadBuf))) != 0;) ctx.Process(ReadBuf, (size_t)sz);
			if (!wasOpen) Close();
		}
		ctx.Finish(sha1);
		have_sha1 = true;
		return sha1;
	}
	size_t PathMatch(const char* rom, size_t len) const // non-case sensitive, slash char agnostic
	{
		const char *pBegin = path.c_str(), *pEnd = pBegin + path.length(), *p = pEnd, *r = rom + len;
		while (p != pBegin && r != rom) { char a = *(--r), b = *(--p); if (((a>='A'&&a<='Z')?(a|0x20):a=='\\'?'/':a) != ((b>='A'&&b<='Z')?(b|0x20):b=='\\'?'/':b)) { p++; break; } }
		return (size_t)(pEnd - p);
	}
	bool IsContainedBy(const char* parent_path, size_t len) const // non-case sensitive, slash char agnostic
	{
		const char *pa = path.c_str(), *pb = parent_path;
		if (path.length() <= len || (pa[len] != '/' && pa[len] != '\\')) return false;
		for (;;) { char a = *(pa++), b = *(pb++); if (!b) return true; if (((a>='A'&&a<='Z')?(a|0x20):a=='\\'?'/':a) != ((b>='A'&&b<='Z')?(b|0x20):b=='\\'?'/':b)) return false; }
	}

	struct Writer
	{
		FILE* f; bool failed;
		Writer(const char* path) : f(fopen_utf8(path, "wb")), failed(f == NULL) { }
		virtual ~Writer() { if (f) fclose(f); }
		virtual void WriteFile(const char* innerpath, size_t innerpath_len, Bit16u wdate, Bit16u wtime, SFile* fsrc, bool keep_already_compressed = false) = 0;
		virtual bool Finalize(char* XmlGameInner) = 0;
	};
};

struct SFileRaw : SFile
{
	FILE* f;
	inline SFileRaw(std::string& _path, bool isdir) : SFile(), f(NULL)
	{
		typ = T_RAW;
		path.swap(_path);
		if (!stat_utf8(path.c_str(), &date, &time)) { size = 0; return; }
		if (isdir) { path += '/'; size = 0; return; }
		if (!Open()) { size = 0; return; }
		size = Seek(0, SEEK_END);
		Close();
	}
	virtual inline ~SFileRaw() { Close(); }
	virtual bool Open() { ZIP_ASSERT(!f); return ((f = fopen_utf8(path.c_str(), "rb")) != NULL); }
	virtual bool IsOpen() { return (f != NULL); }
	virtual bool Close() { return (f ? (fclose(f), (f = NULL), true) : false); }
	virtual Bit64u Read(Bit8u* data, Bit64u len) { return (Bit64u)fread(data, 1, (size_t)len, f); }
	//virtual Bit64u Write(const Bit8u* data, Bit64u len) { return (Bit64u)fwrite(data, 1, (size_t)len, f); }
	virtual Bit64u Seek(Bit64s ofs, int origin = SEEK_SET) { fseek_wrap(f, ofs, origin); return (origin == SEEK_SET ? ofs : ftell_wrap(f)); }

	static void IndexFiles(const char* path, std::vector<SFile*>& files)
	{
		struct Local
		{
			static bool IterateDir(const char *path, std::vector<SFile*>& files)
			{
				#ifdef _WIN32
				WCHAR wpath[MAX_PATH+5];
				int wpathlen = MultiByteToWideChar(CP_UTF8, 0, path, -1, wpath, MAX_PATH);
				wpath[wpathlen-1] = '\\';
				wpath[wpathlen++] = '*';
				wpath[wpathlen++] = '\0';
				WIN32_FIND_DATAW ffd;
				HANDLE hFind = FindFirstFileW(wpath, &ffd);
				if (hFind == INVALID_HANDLE_VALUE) return false;
				for (BOOL more = 1; more; more = FindNextFileW(hFind, &ffd))
					if (ffd.cFileName[0] != '.' || ffd.cFileName[ffd.cFileName[1] == '.' ? 2 : 1])
						if (WideCharToMultiByte(CP_UTF8, 0, ffd.cFileName, -1, (char*)wpath, sizeof(wpath), NULL, NULL) > 0)
							Process(path, (char*)wpath, !!(ffd.dwFileAttributes & FILE_ATTRIBUTE_DIRECTORY), files);
				FindClose(hFind);
				#else
				struct dirent *entry;
				DIR *dp = opendir(path);
				if (!dp) return false;
				while ((entry = readdir(dp)))
					if (entry->d_name[0] != '.' || entry->d_name[entry->d_name[1] == '.' ? 2 : 1])
						Process(path, entry->d_name, (entry->d_type == DT_DIR), files);
				closedir(dp);
				#endif
				return true;
			}
			static void Process(const char* path, const char* file, bool is_dir, std::vector<SFile*>& files)
			{
				std::string fullpath; fullpath.assign(path).append(1, '/').append(file);
				if (is_dir)
				{
					IterateDir(fullpath.c_str(), files);
					files.push_back(new SFileRaw(fullpath, true)); // do after iterate because SFileRaw modifies fullpath
				}
				else
					files.push_back(new SFileRaw(fullpath, false));
			}
		};
		Local::IterateDir(path, files);
	}
};

struct SFileMemory : SFile
{
	Bit8u* buf; Bit64u pos;
	inline SFileMemory(Bit64u _size) : buf(_size ? (Bit8u*)malloc((size_t)_size) : (Bit8u*)NULL), pos((Bit64u)-1) { typ = T_MEMORY; size = _size; date = time = (Bit16u)-1; }
	virtual inline ~SFileMemory() { free(buf); }
	virtual bool Open() { ZIP_ASSERT(pos == (Bit64u)-1 && size); pos = 0; return true; }
	virtual bool IsOpen() { return (pos != (Bit64u)-1); }
	virtual bool Close() { pos = (Bit64u)-1; return true; }
	virtual Bit64u Read(Bit8u* data, Bit64u ln) { Bit64u i = pos+ln, j = (i > size ? size : i), k = (j - pos); memcpy(data, buf+pos, (size_t)k); pos += k; return k; }
	//virtual Bit64u Write(const Bit8u* data, Bit64u ln) { Bit64u i = pos+ln, j = (i > size ? size : i), k = (j - pos); memcpy(buf+pos, data, (size_t)k); pos += k; return k; }
	virtual Bit64u Seek(Bit64s ofs, int origin = SEEK_SET) { switch (origin) { case SEEK_SET: default: pos = (Bit64u)ofs; break; case SEEK_CUR: pos += ofs; break; case SEEK_END: pos = size + ofs; break; } return (pos > size ? (pos = size) : pos); }

	// Generate a file from Base64
	SFileMemory(const char* base64, size_t len) : SFileMemory((len + 3) / 4 * 3)
	{
		path.assign("<EMBEDDED>"); Bit8u* trg = buf;
		static const Bit8u base64dec[256] = {0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,62,0,0,0,63,52,53,54,55,56,57,58,59,60,61,0,0,0,0,0,0,0,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,0,0,0,0,0,0,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,0};
		for (const Bit8u* pIn = (const Bit8u*)base64; len; len -= 4, pIn += 4)
		{
			*trg = (base64dec[pIn[0]] << 2);
			if (len == 1 || pIn[1] == '=') break;
			*(trg++) |= ((base64dec[pIn[1]] >> 4) & 0x3);
			*trg = (base64dec[pIn[1]] << 4);
			if (len == 2 || pIn[2] == '=') break;
			*(trg++) |= (base64dec[pIn[2]] >> 2) & 0xf;
			*trg = (base64dec[pIn[2]] << 6);
			if (len == 3 || pIn[3] == '=') break;
			*(trg++) |= (base64dec[pIn[3]]);
		}
		size = (size_t)(trg - buf);
	}

	// Read entire input file into buf
	SFileMemory(SFile& fiLoad) : SFileMemory(fiLoad.size)
	{
		bool wasOpen = fiLoad.IsOpen();
		if (wasOpen) fiLoad.Seek(0); else fiLoad.Open();
		fiLoad.Read(buf, size);
		if (!wasOpen) fiLoad.Close();
	}

	// Generate a file from CRC and SHA1 (up to 7 bytes)
	static SFileMemory* BuildFromCRC(Bit64u _size, Bit32u crc, Bit8u sha1[20])
	{
		if (_size > 7) { ZIP_ASSERT(false); return NULL; } // 7 is slow and 8 takes a very long time, more is unreasonable
		SFileMemory* res = new SFileMemory(_size); res->path.assign("<GENERATED>"); Bit8u* trg = res->buf;
		if (_size <= 4) { RawUnCRC32(~crc, (Bit8u)_size, trg); for (Bit64u i = 0; i != _size; i++) trg[i] = ~trg[i]; return res; }
		for (Bit64u i = 0, n = _size - 4; ; i++)
		{
			Bit8u test[8] = { (Bit8u)i, (Bit8u)(i >> 8), (Bit8u)(i >> 16), (Bit8u)(i >> 24), 0, 0, 0, 0 };
			RawUnCRC32((crc ^ CRC32(test, (size_t)_size)), 4, test + n);
			Bit8u compSha1[20];
			SHA1_CTX::Run(test, (size_t)_size, compSha1);
			if (sha1[0] == compSha1[0] && !memcmp(sha1, compSha1, sizeof(compSha1))) { memcpy(trg, test, (size_t)_size); return  res; } // found
		}
	}

	// Patch a file with a IPS or BPS patch encoded as Base64 in the DAT XML
	static SFileMemory* BuildPatched(const std::vector<SFile*>& files, char* pRomOpenTagEnd, Bit64u romSize, const char* romSha1)
	{
		struct Local
		{
			static bool GetU24(SFile& fi, Bit32u& res)
			{
				Bit8u buf[3]; if (fi.Read(buf, 3) == 3) { res = (Bit32u)((buf[0] << 16) | (buf[1] << 8) | buf[2]); return true; } else { return false; }
			}
			static bool GetU16(SFile& fi, Bit16u& res)
			{
				Bit8u buf[2]; if (fi.Read(buf, 2) == 2) { res = (Bit16u)((buf[0] << 8) | buf[1]); return true; } else { return false; }
			}
			static bool GetU8(SFile& fi, Bit8u& res)
			{
				Bit8u buf; if (fi.Read(&buf, 1) == 1) { res = buf; return true; } else { return false; }
			}
			static bool BPSGetVarLenInt(SFile& fi, Bit64u& res)
			{
				Bit8u x; Bit64u shift = 1; for (res = 0;;) { if (!fi.Read(&x, 1)) return false; res += (x & 0x7f) * shift; if (x & 0x80) return true; res += (shift <<= 7); }
			}

			static bool IPSPatch(SFileMemory& patch, const Bit8u* inp, const Bit8u* inpEnd, Bit8u* outp, const Bit8u* outpEnd)
			{
				Bit32u ofs; Bit16u len, rlelen; Bit8u rlebyte;
				if ((outpEnd - outp) <= (inpEnd - inp)) { memcpy(outp, inp, (outpEnd - outp)); }
				else { memcpy(outp, inp, (inpEnd - inp)); memset(outp + (inpEnd - inp), 0, (outpEnd - outp) - (inpEnd - inp)); }
				patch.Seek(5); // skip over header
				while (GetU24(patch, ofs))
				{
					if (ofs == 0x454f46) return true; // EOF marker (followed by trunc which we don't use)
					if (!GetU16(patch, len) || outp + ofs + len > outpEnd) return false;
					if (len) patch.Read(outp + ofs, len); // patch bytes
					else if (!GetU16(patch, rlelen) || !GetU8(patch, rlebyte) || outp + ofs + rlelen > outpEnd) return false;
					else memset(outp + ofs, rlebyte, rlelen); // RLE
				}
				return true; // no EOF marker but still success?
			}

			static bool BPSPatch(SFileMemory& patch, const Bit8u* inp, const Bit8u* inpEnd, Bit8u* outp, const Bit8u* outpEnd)
			{
				Bit64u sourceLen, targetLen, metaLen, cmd, len, ofs = 0, inpRelOfs = 0, outpRelOfs = 0;
				patch.Seek(4); // skip over header
				if (!BPSGetVarLenInt(patch, sourceLen) || sourceLen != (Bit64u)(inpEnd - inp) || !BPSGetVarLenInt(patch, targetLen) || targetLen != (Bit64u)(outpEnd - outp) || !BPSGetVarLenInt(patch, metaLen)) return false;
				patch.Seek(metaLen, SEEK_CUR); // skip over meta data
				for (;;)
				{
					if (!BPSGetVarLenInt(patch, cmd) || ofs + (len = ((cmd >> 2) + 1)) > targetLen) return false;
					switch (cmd & 3)
					{
						case 0: // SourceRead
							if (ofs + len > sourceLen) return false;
							memcpy(&outp[ofs], &inp[ofs], (size_t)len);
							break;
						case 1: // TargetRead
							if (patch.Read(&outp[ofs], len) != len) return false;
							break;
						case 2: // SourceCopy
							if (!BPSGetVarLenInt(patch, cmd) || (inpRelOfs += (Bit64s)(cmd >> 1) * ((cmd & 1) ? -1 : 1)) + len > sourceLen) return false;
							memcpy(&outp[ofs], &inp[inpRelOfs], (size_t)len);
							inpRelOfs += len;
							break;
						case 3: // TargetCopy
							if (!BPSGetVarLenInt(patch, cmd) || (outpRelOfs += (Bit64s)(cmd >> 1) * ((cmd & 1) ? -1 : 1)) >= ofs) return false;
							for (Bit8u *p = &outp[ofs], *pEnd = p + len; p != pEnd;) *(p++) = outp[outpRelOfs++];
							break;
					}
					if ((ofs += len) == targetLen) return true;
				}
			}
		};

		EXml x;
		for (char *p = pRomOpenTagEnd, *pEnd; p && (x = XMLParse(p, pEnd)) != XML_END && x != XML_ELEM_END; p = XMLLevel(pEnd, x))
		{
			char *patchData, *patchDataX, *patchSize, *patchCrc, *patchSha1;
			if (!XMLMatchTag(p, pEnd, "patch", 5, "data", &patchData, &patchDataX, "size", &patchSize, NULL, "crc", &patchCrc, NULL, "sha1", &patchSha1, NULL, NULL)) continue;

			Bit64u size = atoi64(patchSize);
			for (SFile* fi : files)
			{
				if (fi->size != size || fi->GetCRC32() != (Bit32u)atoi64(patchCrc, 0x10)) continue;
				Bit8u patchSha1b[20];
				if (!fi->GetSHA1() || !hextouint8(patchSha1, patchSha1b, 20) || memcmp(fi->sha1, patchSha1b, 20)) continue;

				SFileMemory unpatched(*fi), patched(romSize), patch(patchData, (size_t)(patchDataX - patchData));
				patch.Open();

				Bit32u hdr = 0;
				Local::GetU24(patch, hdr);
				bool success = false;
				if (hdr == 0x504154) success = Local::IPSPatch(patch, unpatched.buf, unpatched.buf + unpatched.size, patched.buf, patched.buf + patched.size); // IPS file
				if (hdr == 0x425053) success = Local::BPSPatch(patch, unpatched.buf, unpatched.buf + unpatched.size, patched.buf, patched.buf + patched.size); // BPS file

				SFileMemory* res = NULL;
				Bit8u romSha1b[20];
				bool match = (success && patched.GetSHA1() && hextouint8(romSha1, romSha1b, 20) && !memcmp(patched.sha1, romSha1b, 20));
				if (match) { res = new SFileMemory(0); res->buf = patched.buf; res->size = patched.size; patched.buf = NULL; res->path.assign(fi->path).append("|PATCHED"); }
				else LogErr("Patch of type %s for rom with Sha1 %.*s failed (%s)\n", (hdr == 0x504154 ? "IPS" : hdr == 0x425053 ? "BPS" : "Unknown"), 40, romSha1, (success ? "Patched file did not match" : "Patch format error"));
				return res;
			}
		}
		return NULL;
	}

	static bool CanPotentiallyBuildPatched(const std::vector<SFile*>& files, char* pRomOpenTagEnd)
	{
		EXml x;
		for (char *p = pRomOpenTagEnd, *pEnd; p && (x = XMLParse(p, pEnd)) != XML_END && x != XML_ELEM_END; p = XMLLevel(pEnd, x))
		{
			char *patchData, *patchSize, *patchCrc, *patchSha1, *patchSha1X;
			if (!XMLMatchTag(p, pEnd, "patch", 5, "data", &patchData, NULL, "size", &patchSize, NULL, "crc", &patchCrc, NULL, "sha1", &patchSha1, &patchSha1X, NULL)) continue;

			const char *missField = (!patchData ? "data" : !patchSize ? "size" : !patchCrc ? "crc" : (!patchSha1 || (patchSha1X - patchSha1) != 40) ? "sha1" : NULL);
			if (missField) { LogErr("<%s> element missing '%s' field!\n", "patch", missField); return false; }
			Bit64u size = atoi64(patchSize);
			for (SFile* fil : files) if (fil->size == size) return true;
		}
		return false;
	}
};

struct SFileZip : SFileMemory
{
	struct ZipReader
	{
		ZipReader(SFile& _archive) : archive(_archive), refs(0) { }
		~ZipReader() { archive.Close(); }
		SFile& archive; Bit32u refs;
		inline void AddRef() { refs++; }
		inline void DelRef() 
		{
			ZIP_ASSERT(refs); 
			if (!--refs)
				delete this;
		}
	};

	ZipReader& reader; Bit64u unpacked, data_ofs; Bit32u comp_size; Bit8u bit_flags, method; bool lhskip; void* decomp_state;
	SFileZip(ZipReader& _reader, const char* filename, Bit32u filename_len, Bit64u _data_ofs, Bit32u _comp_size, Bit64u _decomp_size, Bit16u _date, Bit16u _time, Bit8u _bit_flags, Bit8u _method, Bit32u _crc32)
		: SFileMemory(0), reader(_reader), unpacked(0), data_ofs(_data_ofs), comp_size(_comp_size), bit_flags(_bit_flags), method(_method), lhskip(false), decomp_state(NULL)
	{
		typ = T_ZIP;
		(path.assign(reader.archive.path) += '/').append(filename, (size_t)filename_len);
		size = _decomp_size;
		date = _date;
		time = _time;
		crc32 = _crc32;
		have_crc32 = true;
		reader.AddRef();
	}
	virtual inline ~SFileZip()
	{
		free(decomp_state);
		reader.DelRef();
	}
	virtual inline bool Open() { ZIP_ASSERT(size); return (SFileMemory::Open()); }
	virtual Bit64u Read(Bit8u* data, Bit64u len)
	{
		Bit64u posAndLen = pos+len, readEnd = (posAndLen > size ? size : posAndLen), readLen = (readEnd - pos);
		if (!readLen) return 0;
		if (method == METHOD_STORED)
		{
			if (!lhskip && !SkipLocalHeader()) return 0;
			if (reader.archive.Seek(data_ofs + pos) != data_ofs + pos) { ZIP_ASSERT(false); return 0; }
			pos += readLen; return reader.archive.Read(data, readLen);
		}
		if (readEnd > unpacked && !Unpack(readEnd)) { ZIP_ASSERT(false); return 0; }
		memcpy(data, buf+pos, (size_t)readLen); pos += readLen; return readLen;
	}

	// Various ZIP archive enums. To completely avoid cross platform compiler alignment and platform endian issues, we don't use structs for any of this stuff
	enum
	{
		// ZIP archive identifiers and record sizes
		ZIP_END_OF_CENTRAL_DIR_HEADER_SIG = 0x06054b50, ZIP_CENTRAL_DIR_HEADER_SIG = 0x02014b50, ZIP_LOCAL_DIR_HEADER_SIG = 0x04034b50,
		ZIP_LOCAL_DIR_HEADER_SIZE = 30, ZIP_CENTRAL_DIR_HEADER_SIZE = 46, ZIP_END_OF_CENTRAL_DIR_HEADER_SIZE = 22,
		ZIP64_END_OF_CENTRAL_DIR_HEADER_SIG = 0x06064b50, ZIP64_END_OF_CENTRAL_DIR_HEADER_SIZE = 56,
		ZIP64_END_OF_CENTRAL_DIR_LOCATOR_SIG = 0x07064b50, ZIP64_END_OF_CENTRAL_DIR_LOCATOR_SIZE = 20,
		// End of central directory offsets
		ZIP_ECDH_NUM_THIS_DISK_OFS = 4, ZIP_ECDH_NUM_DISK_CDIR_OFS = 6, ZIP_ECDH_CDIR_NUM_ENTRIES_ON_DISK_OFS = 8,
		ZIP_ECDH_CDIR_TOTAL_ENTRIES_OFS = 10, ZIP_ECDH_CDIR_SIZE_OFS = 12, ZIP_ECDH_CDIR_OFS_OFS = 16, ZIP_ECDH_COMMENT_SIZE_OFS = 20,
		ZIP64_ECDL_ECDH_OFS_OFS = 8, ZIP64_ECDH_CDIR_TOTAL_ENTRIES_OFS = 32, ZIP64_ECDH_CDIR_SIZE_OFS = 40, ZIP64_ECDH_CDIR_OFS_OFS = 48,
		// Central directory header record offsets
		ZIP_CDH_BIT_FLAG_OFS = 8, ZIP_CDH_METHOD_OFS = 10, ZIP_CDH_FILE_TIME_OFS = 12, ZIP_CDH_FILE_DATE_OFS = 14, ZIP_CDH_CRC32_OFS = 16,
		ZIP_CDH_COMPRESSED_SIZE_OFS = 20, ZIP_CDH_DECOMPRESSED_SIZE_OFS = 24, ZIP_CDH_FILENAME_LEN_OFS = 28, ZIP_CDH_EXTRA_LEN_OFS = 30,
		ZIP_CDH_COMMENT_LEN_OFS = 32, ZIP_CDH_EXTERNAL_ATTR_OFS = 38, ZIP_CDH_LOCAL_HEADER_OFS = 42,
		// Local directory header offsets
		ZIP_LDH_FILENAME_LEN_OFS = 26, ZIP_LDH_EXTRA_LEN_OFS = 28,
	};

	bool SkipLocalHeader()
	{
		ZIP_ASSERT(!lhskip);
		SFile& fi = reader.archive;
		Bit8u local_header[ZIP_LOCAL_DIR_HEADER_SIZE];
		if (fi.Seek(data_ofs) != data_ofs || fi.Read(local_header, ZIP_LOCAL_DIR_HEADER_SIZE) != ZIP_LOCAL_DIR_HEADER_SIZE)
			return false;
		if (ZIP_READ_LE32(local_header) != ZIP_LOCAL_DIR_HEADER_SIG)
			return false;
		data_ofs += ZIP_LOCAL_DIR_HEADER_SIZE + ZIP_READ_LE16(local_header + ZIP_LDH_FILENAME_LEN_OFS) + ZIP_READ_LE16(local_header + ZIP_LDH_EXTRA_LEN_OFS);
		if ((data_ofs + comp_size) > fi.size)
			return false;
		return (lhskip = true);
	}

	bool Unpack(Bit64u unpack_until);
	static SFileMemory* BuildDeflated(const Bit8u* data, size_t comp_len, size_t uncomp_len);
	static bool CompressInto(FILE* f, SFile* fsrc, Bit32u& out_crc, Bit32u& out_compsize);

	enum { METHOD_STORED = 0, METHOD_SHRUNK = 1, METHOD_IMPLODED = 6, METHOD_DEFLATED = 8 };
	static bool MethodSupported(Bit32u method) { return (method == METHOD_DEFLATED || method == METHOD_STORED || method == METHOD_SHRUNK || method == METHOD_IMPLODED); }

	static bool UsesExtension(const char* ext3, const char* ext4, bool as_output)
	{
		return (ext3 && (!strncasecmp(ext3, "ZIP", 3) || !strncasecmp(ext3, "EXE", 3))) || (ext4 && (!strncasecmp(ext4, "DOSC", 4) || (as_output && !strncasecmp(ext4, "DOSZ", 4))));
	}

	static bool IndexFiles(SFile& fi, std::vector<SFile*>& files)
	{
		// Basic sanity checks - reject files which are too small.
		if (fi.size < ZIP_END_OF_CENTRAL_DIR_HEADER_SIZE)
		{
			invalid_zip:
			if (fi.path.length() < 3 || (fi.path[fi.path.length()-3] | 0x20) != 'e') // don't log for .exe files
				LogErr("Invalid or unsupported ZIP file: %s\n", fi.path.c_str());
			if (fi.size >= ZIP_END_OF_CENTRAL_DIR_HEADER_SIZE) fi.Close();
			return false;
		}

		// Find the end of central directory record by scanning the file from the end towards the beginning.
		fi.Open();
		Bit8u buf[4096];
		Bit64u ecdh_ofs = (fi.size < sizeof(buf) ? 0 : fi.size - sizeof(buf));
		for (;; ecdh_ofs = ZIP_MAX(ecdh_ofs - (sizeof(buf) - 3), 0))
		{
			Bit32s i, n = (Bit32s)ZIP_MIN(sizeof(buf), fi.size - ecdh_ofs);
			if (fi.Seek(ecdh_ofs) != ecdh_ofs || fi.Read(buf, (Bit64u)n) != (Bit64u)n) goto invalid_zip;
			for (i = n - 4; i >= 0; --i) { if (ZIP_READ_LE32(buf + i) == ZIP_END_OF_CENTRAL_DIR_HEADER_SIG) break; }
			if (i >= 0) { ecdh_ofs += i; break; }
			if (!ecdh_ofs || (fi.size - ecdh_ofs) >= (0xFFFF + ZIP_END_OF_CENTRAL_DIR_HEADER_SIZE)) goto invalid_zip;
		}

		// Read and verify the end of central directory record.
		if (fi.Seek(ecdh_ofs) != ecdh_ofs || fi.Read(buf, ZIP_END_OF_CENTRAL_DIR_HEADER_SIZE) != ZIP_END_OF_CENTRAL_DIR_HEADER_SIZE)
			goto invalid_zip;

		Bit64u total_files = ZIP_READ_LE16(buf + ZIP_ECDH_CDIR_TOTAL_ENTRIES_OFS);
		Bit64u cdir_size   = ZIP_READ_LE32(buf + ZIP_ECDH_CDIR_SIZE_OFS);
		Bit64u cdir_ofs    = ZIP_READ_LE32(buf + ZIP_ECDH_CDIR_OFS_OFS);

		if ((cdir_ofs == 0xFFFFFFFF || cdir_size == 0xFFFFFFFF || total_files == 0xFFFF)
			&& ecdh_ofs >= (ZIP64_END_OF_CENTRAL_DIR_LOCATOR_SIZE + ZIP64_END_OF_CENTRAL_DIR_HEADER_SIZE)
			&& fi.Seek(ecdh_ofs - ZIP64_END_OF_CENTRAL_DIR_LOCATOR_SIZE) == ecdh_ofs - ZIP64_END_OF_CENTRAL_DIR_LOCATOR_SIZE
			&& fi.Read(buf, ZIP64_END_OF_CENTRAL_DIR_LOCATOR_SIZE) == ZIP64_END_OF_CENTRAL_DIR_LOCATOR_SIZE
			&& ZIP_READ_LE32(buf) == ZIP64_END_OF_CENTRAL_DIR_LOCATOR_SIG)
		{
			Bit64u ecdh64_ofs = ZIP_READ_LE64(buf + ZIP64_ECDL_ECDH_OFS_OFS);
			if (ecdh64_ofs <= (fi.size - ZIP64_END_OF_CENTRAL_DIR_HEADER_SIZE)
				&& fi.Seek(ecdh64_ofs) == ecdh64_ofs
				&& fi.Read(buf, ZIP64_END_OF_CENTRAL_DIR_HEADER_SIZE) == ZIP64_END_OF_CENTRAL_DIR_HEADER_SIZE
				&& ZIP_READ_LE32(buf) == ZIP64_END_OF_CENTRAL_DIR_HEADER_SIG)
			{
				total_files = ZIP_READ_LE64(buf + ZIP64_ECDH_CDIR_TOTAL_ENTRIES_OFS);
				cdir_size   = ZIP_READ_LE64(buf + ZIP64_ECDH_CDIR_SIZE_OFS);
				cdir_ofs    = ZIP_READ_LE64(buf + ZIP64_ECDH_CDIR_OFS_OFS);
			}
		}

		if (!total_files) return true;
		if (cdir_size >= 0x10000000 // limit to 256MB content directory
			|| (cdir_size < total_files * ZIP_CENTRAL_DIR_HEADER_SIZE)
			|| ((cdir_ofs + cdir_size) > fi.size)
			) goto invalid_zip;

		Bit8u* m_central_dir = (Bit8u*)malloc((size_t)cdir_size);
		if (fi.Seek(cdir_ofs) != cdir_ofs || fi.Read(m_central_dir, cdir_size) != cdir_size)
			goto invalid_zip;
		const Bit8u *cdir_start = (const Bit8u*)m_central_dir, *cdir_end = cdir_start + cdir_size, *p = cdir_start;

		ZipReader* reader = new ZipReader(fi); // pass already opened file

		// Now create an index into the central directory file records, do some basic sanity checking on each record
		p = cdir_start;
		size_t old_files_count = files.size();
		for (Bit32u i = 0, total_header_size; i < total_files && p >= cdir_start && p < cdir_end && ZIP_READ_LE32(p) == ZIP_CENTRAL_DIR_HEADER_SIG; i++, p += total_header_size)
		{
			Bit32u bit_flag         = ZIP_READ_LE16(p + ZIP_CDH_BIT_FLAG_OFS);
			Bit32u method           = ZIP_READ_LE16(p + ZIP_CDH_METHOD_OFS);
			Bit16u file_time        = ZIP_READ_LE16(p + ZIP_CDH_FILE_TIME_OFS);
			Bit16u file_date        = ZIP_READ_LE16(p + ZIP_CDH_FILE_DATE_OFS);
			Bit32u crc32            = ZIP_READ_LE32(p + ZIP_CDH_CRC32_OFS);
			Bit64u comp_size        = ZIP_READ_LE32(p + ZIP_CDH_COMPRESSED_SIZE_OFS);
			Bit64u decomp_size      = ZIP_READ_LE32(p + ZIP_CDH_DECOMPRESSED_SIZE_OFS);
			Bit32u filename_len     = ZIP_READ_LE16(p + ZIP_CDH_FILENAME_LEN_OFS);
			Bit32s extra_len        = ZIP_READ_LE16(p + ZIP_CDH_EXTRA_LEN_OFS);
			Bit64u local_header_ofs = ZIP_READ_LE32(p + ZIP_CDH_LOCAL_HEADER_OFS);
			total_header_size = ZIP_CENTRAL_DIR_HEADER_SIZE + filename_len + extra_len + ZIP_READ_LE16(p + ZIP_CDH_COMMENT_LEN_OFS);

			if (!MethodSupported(method)
				|| (p + total_header_size > cdir_end)
				|| (bit_flag & (1 | 32)) // Encryption and patch files are not supported.
				) continue;

			if (decomp_size == 0xFFFFFFFF || comp_size == 0xFFFFFFFF || local_header_ofs == 0xFFFFFFFF)
			{
				for (const Bit8u *x = p + ZIP_CENTRAL_DIR_HEADER_SIZE + filename_len, *xEnd = x + extra_len; (x + (sizeof(Bit16u) * 2)) < xEnd;)
				{
					const Bit8u *field = x + (sizeof(Bit16u) * 2), *fieldEnd = field + ZIP_READ_LE16(x + 2);
					if (ZIP_READ_LE16(x) != 0x0001 || fieldEnd > xEnd) { x = fieldEnd; continue; } // Not Zip64 extended information extra field
					if (decomp_size == 0xFFFFFFFF)
					{
						if ((size_t)(fieldEnd - field) < sizeof(Bit64u)) goto invalid_zip;
						decomp_size = ZIP_READ_LE64(field);
						field += sizeof(Bit64u);
					}
					if (comp_size == 0xFFFFFFFF)
					{
						if ((size_t)(fieldEnd - field) < sizeof(Bit64u)) goto invalid_zip;
						comp_size = ZIP_READ_LE64(field);
						field += sizeof(Bit64u);
					}
					if (local_header_ofs == 0xFFFFFFFF)
					{
						if ((size_t)(fieldEnd - field) < sizeof(Bit64u)) goto invalid_zip;
						local_header_ofs = ZIP_READ_LE64(field);
						field += sizeof(Bit64u);
					}
					break;
				}
			}

			if (((!method) && (decomp_size != comp_size)) || (decomp_size && !comp_size)
				|| (decomp_size > 0xFFFFFFFF) || (comp_size > 0xFFFFFFFF) // not supported on DOS file systems
				|| ((local_header_ofs + ZIP_LOCAL_DIR_HEADER_SIZE + comp_size) > fi.size)
				) continue;

			char *name = (char*)(p + ZIP_CENTRAL_DIR_HEADER_SIZE);
			for (char *q = name, *name_end = name + filename_len; q != name_end; q++)
				if (*q == '\\')
					*q = '/'; // convert back-slashes to regular slashes

			files.push_back(new SFileZip(*reader, name, filename_len, local_header_ofs, (Bit32u)comp_size, decomp_size, file_date, file_time, (Bit8u)bit_flag, (Bit8u)method, crc32));
		}
		free(m_central_dir);
		if (old_files_count == files.size()) delete reader;
		return true;
	}

	struct ZipWriter : SFile::Writer
	{
		Bit32u local_file_offset;
		Bit16u file_count;
		std::vector<Bit8u> central_dir;

		ZipWriter(const char* path) : SFile::Writer(path), local_file_offset(0), file_count(0) { }

		virtual void WriteFile(const char* innerpath, size_t innerpath_len, Bit16u wdate, Bit16u wtime, SFile* fsrc, bool keep_already_compressed)
		{
			if (innerpath_len > 0xFFFF) { ZIP_ASSERT(false); failed = true; return; }
			bool is_dir = (innerpath[innerpath_len-1] == '/' || innerpath[innerpath_len-1] == '\\');
			Bit16u pathLen = (Bit16u)innerpath_len, wmethod = METHOD_STORED;
			Bit32u wsize = (fsrc ? (Bit32u)fsrc->size : (Bit32u)0), wcrc32 = 0, extAttr = (is_dir ? 0x10 : 0), compsize = 0;
			//if (is_dir) return; // force skip directory entries

			if (is_dir || !wsize || !fsrc) { ZIP_ASSERT(!wsize); wsize = 0; }
			else if (keep_already_compressed && fsrc->typ == SFile::T_ZIP)
			{
				ZIP_ASSERT(wsize == fsrc->size);
				SFileZip& zsrc = (SFileZip&)*fsrc;
				if ((zsrc.lhskip || zsrc.SkipLocalHeader()) && zsrc.reader.archive.Seek(zsrc.data_ofs) == zsrc.data_ofs)
				{
					// Copy compressed data as is from source without recompressing
					fseek_wrap(f, 30 + pathLen, SEEK_CUR);
					wmethod = zsrc.method;
					compsize = zsrc.comp_size;
					wcrc32 = zsrc.crc32;
					for (size_t comp_remain = compsize, n; comp_remain && !failed; comp_remain -= n)
					{
						n = (comp_remain < sizeof(ReadBuf) ? comp_remain : sizeof(ReadBuf));
						failed |= (zsrc.reader.archive.Read(ReadBuf, n) != n);
						failed |= !fwrite(ReadBuf, n, 1, f);
					}
					fseek_wrap(f, local_file_offset, SEEK_SET);
				}
				else { ZIP_ASSERT(false); goto justcompress; }
			}
			else
			{
				justcompress:

				// Write file and calculate CRC32 along the way
				fseek_wrap(f, 30 + pathLen, SEEK_CUR);

				bool wasOpen = fsrc->IsOpen();
				if (wasOpen) fsrc->Seek(0); else if (!fsrc->Open()) { failed = true; return; }

				failed |= !CompressInto(f, fsrc, wcrc32, compsize);

				// Fall back to storing raw if compression didn't do much
				if (!failed && compsize + (compsize / 100) >= wsize)
				{
					fseek_wrap(f, local_file_offset + 30 + pathLen, SEEK_SET);
					Bit32u src_remain = wsize;
					fsrc->Seek(0, SEEK_SET);
					for (int read; src_remain && (read = (int)fsrc->Read(ReadBuf, sizeof(ReadBuf))) > 0; src_remain -= read)
						failed |= !fwrite(ReadBuf, read, 1, f);
					ZIP_ASSERT(src_remain == 0);
					compsize = wsize;
				}
				if (!wasOpen) fsrc->Close();
				if (failed) return;
				wmethod = (Bit16u)(compsize == wsize ? METHOD_STORED : METHOD_DEFLATED);
				fseek_wrap(f, local_file_offset, SEEK_SET);
			}

			Bit8u wbuf[4096];
			ZIP_WRITE_LE32(wbuf+ 0, 0x04034b50); // Local file header signature
			ZIP_WRITE_LE16(wbuf+ 4, 0);          // Version needed to extract (minimum)
			ZIP_WRITE_LE16(wbuf+ 6, 0);          // General purpose bit flag
			ZIP_WRITE_LE16(wbuf+ 8, wmethod);     // Compression method
			ZIP_WRITE_LE16(wbuf+10, wtime);       // File last modification time
			ZIP_WRITE_LE16(wbuf+12, wdate);       // File last modification date
			ZIP_WRITE_LE32(wbuf+14, wcrc32);      // CRC-32 of uncompressed data
			ZIP_WRITE_LE32(wbuf+18, compsize);   // Compressed size
			ZIP_WRITE_LE32(wbuf+22, wsize);       // Uncompressed size
			ZIP_WRITE_LE16(wbuf+26, pathLen);    // File name length
			ZIP_WRITE_LE16(wbuf+28, 0);          // Extra field length

			//File name (with \ changed to /)
			for (char* pIn = (char*)innerpath, *pEnd = pIn + pathLen, *pOut = (char*)(wbuf+30); pIn != pEnd; pIn++, pOut++)
				*pOut = (*pIn == '\\' ? '/' : *pIn);
			//if (1) { for (char *pP = (char*)buf+30, *pE = pP + pathLen; pP != pE; pP++) if (*pP >= 'a' && *pP <= 'z') (*pP) -= 0x20; } // force upper case names

			failed |= !fwrite(wbuf, 30 + pathLen, 1, f);
			if (compsize) { fseek_wrap(f, compsize, SEEK_CUR); }

			size_t centralDirPos = central_dir.size();
			central_dir.resize(centralDirPos + 46 + pathLen);
			Bit8u* cd = &central_dir[0] + centralDirPos;

			ZIP_WRITE_LE32(cd+0, 0x02014b50);         // Central directory file header signature
			ZIP_WRITE_LE16(cd+4, 0);                  // Version made by (0 = DOS)
			memcpy(cd+6, wbuf+4, 26);                 // Copy middle section shared with local file header
			ZIP_WRITE_LE16(cd+32, 0);                 // File comment length
			ZIP_WRITE_LE16(cd+34, 0);                 // Disk number where file starts
			ZIP_WRITE_LE16(cd+36, 0);                 // Internal file attributes
			ZIP_WRITE_LE32(cd+38, extAttr);           // External file attributes
			ZIP_WRITE_LE32(cd+42, local_file_offset); // Relative offset of local file header
			memcpy(cd + 46, wbuf + 30, pathLen);      // File name

			local_file_offset += 30 + pathLen + compsize;
			file_count++;
		}

		virtual bool Finalize(char*)
		{
			if (failed) return false;
			if (file_count) failed |= !fwrite(&central_dir[0], central_dir.size(), 1, f);
			Bit8u eocd[22];
			ZIP_WRITE_LE32(eocd+ 0, 0x06054b50);                 // End of central directory signature
			ZIP_WRITE_LE16(eocd+ 4, 0);                          // Number of this disk
			ZIP_WRITE_LE16(eocd+ 6, 0);                          // Disk where central directory starts
			ZIP_WRITE_LE16(eocd+ 8, file_count);                 // Number of central directory records on this disk
			ZIP_WRITE_LE16(eocd+10, file_count);                 // Total number of central directory records
			ZIP_WRITE_LE32(eocd+12, (Bit32u)central_dir.size()); // Size of central directory (bytes)
			ZIP_WRITE_LE32(eocd+16, local_file_offset);          // Offset of start of central directory, relative to start of archive
			ZIP_WRITE_LE16(eocd+20, 0);                          // Comment length (n)
			failed |= !fwrite(eocd, 22, 1, f);
			return !failed;
		}
	};
};

struct SFileIso : SFile
{
	enum { RAW_SECTOR_SIZE = 2352, COOKED_SECTOR_SIZE = 2048, ISO_FIRST_VD = 16, CD_FPS = 75, ISO_ASSOCIATED = 4, ISO_DIRECTORY = 2, ISO_HIDDEN = 1 };
	enum { CD_MAX_SUBCODE_DATA = 96, CD_FRAME_SIZE = RAW_SECTOR_SIZE + CD_MAX_SUBCODE_DATA, ISO_FRAMESIZE = 2048 };
	enum { CHD_V5_HEADER_SIZE = 124, CHD_V5_UNCOMPMAPENTRYBYTES = 4, CHD_METADATA_HEADER_SIZE = 16, CHD_CDROM_TRACK_METADATA_TAG = 1128813650, CHD_CDROM_TRACK_METADATA2_TAG = 1128813618 };
	enum { CHD_UNITBYTES = CD_FRAME_SIZE, CHD_HUNKBYTES = CHD_UNITBYTES * 8, CHD_CD_TRACK_PADDING = 4 };
	struct BuiltTrack { Bit8u* buf = NULL; ~BuiltTrack() { free(buf); } size_t bufsize; int data_size, pregap, omitted_pregap; char ttype[16]; };

	struct IsoReader
	{
		// BASED ON cdrom_image.cpp of DOSBox (GPL2)
		// Copyright (C) 2002-2021  The DOSBox Team
		struct Track { int number, start, pregap, frames, sector_size; bool audio, mode2; Bit16s zerotag; SFile* file; Bit64u skip; Bit32u inzeros, outzeros; };
		struct ChdState { ChdState() : hunkmap(NULL), cooked_sector_shift(0) { } ~ChdState() { free(hunkmap); } Bit32u *hunkmap; int hunkbytes, cooked_sector_shift; };

		IsoReader(SFile& _src, ChdState* _chd, std::vector<IsoReader::Track>& _tracks) : src(_src), refs(0), chd(_chd), lasttrack(0), cachesector((Bit32u)-1) { tracks.swap(_tracks); for (Track& t : tracks) if (t.file &&!t.file->IsOpen()) t.file->Open(); }
		~IsoReader() { delete chd; for (Track& t : tracks) if (t.file) t.file->Close(); }
		SFile& src; Bit32u refs;
		void AddRef() { refs++; }
		void DelRef() { ZIP_ASSERT(refs); if (!--refs) delete this; }

		ChdState *chd;
		std::vector<IsoReader::Track> tracks;
		Bit8u cache[RAW_SECTOR_SIZE];
		Bit32u lasttrack, cachesector;

		const Bit8u* ReadSector(Bit32u sector, bool raw = false, Bit8u* non_cached_out = NULL)
		{
			Track* t = &tracks[lasttrack];
			while (lasttrack && sector < (Bit32u)(t[-1].start + t[-1].frames)) { t--; lasttrack--; }
			while (sector >= (Bit32u)(t->start + t->frames)) { t++; if (t->number == (int)tracks.size()) return NULL; lasttrack++; }

			int secsize = t->sector_size, mode2 = t->mode2;
			int insecofs = (secsize >= RAW_SECTOR_SIZE ? (!raw ? (!mode2 ? 16 : 24) + (chd ? chd->cooked_sector_shift : 0) : 0) : (!raw ? (!mode2 ? 0 : 8) + (chd ? chd->cooked_sector_shift : 0) : -1));
			if (insecofs == -1) return NULL;
			if (cachesector != sector || non_cached_out)
			{
				ZIP_ASSERT((int)sector >= t->start);
				Bit64u seek = t->skip + (sector - t->start) * secsize, hunk_pos;
				if (sector < (Bit32u)t->start)
				{
					// Pregap area that have been omitted from the track data (by using the PREGAP command in the CUE sheet or CHD with a MODE1 pgtype)
					seek = (Bit64u)-1;
				}
				else if (chd)
				{
					ZIP_ASSERT((seek / CD_FRAME_SIZE) == ((seek + (RAW_SECTOR_SIZE-1)) / CD_FRAME_SIZE)); // read only inside one sector
					seek = ((hunk_pos = chd->hunkmap[seek / chd->hunkbytes]) != 0 ? hunk_pos + (seek % chd->hunkbytes) : (Bit64u)-1);
				}

				Bit8u* out      = (non_cached_out ? non_cached_out : cache);
				Bit64u readseek = (non_cached_out ? (seek + insecofs) : seek);
				size_t readsize = (non_cached_out ? (raw ? RAW_SECTOR_SIZE : COOKED_SECTOR_SIZE) : (chd ? RAW_SECTOR_SIZE : secsize));
				if      (seek == (Bit64u)-1) memset(out, 0, readsize);
				else if (t->file->Seek(readseek) != readseek || !t->file->Read(out, readsize)) return NULL;
				else if (chd && t->audio && raw) // CHD audio endian swap
					for (Bit8u *p = cache, *pEnd = p + RAW_SECTOR_SIZE, tmp; p < pEnd; p += 2)
						{ tmp = p[0]; p[0] = p[1]; p[1] = tmp; }
				if (non_cached_out) return out;
				cachesector = sector;
			}
			return cache + insecofs;
		}

		#define ISO_MSF_TO_FRAMES(M, S, F)	((M)*60*CD_FPS+(S)*CD_FPS+(F))
		#define ISO_IS_DIR(de) (((iso) ? (de)->fileFlags : (de)->timeZone) & ISO_DIRECTORY)

		static bool CanReadPVD(SFile& fi, int sectorSize, bool mode2)
		{
			Bit8u pvd[COOKED_SECTOR_SIZE];
			Bit32u seek = ISO_FIRST_VD * sectorSize; // first vd is located at sector 16
			if (sectorSize == RAW_SECTOR_SIZE && !mode2) seek += 16;
			if (mode2) seek += 24;
			// pvd[0] = descriptor type, pvd[1..5] = standard identifier, pvd[6] = iso version (+8 for High Sierra)
			return (fi.Seek(seek) == seek && fi.Read(pvd, COOKED_SECTOR_SIZE) &&
					((pvd[0] == 1 && !strncmp((char*)(&pvd[1]), "CD001", 5) && pvd[6] == 1) ||
					(pvd[8] == 1 && !strncmp((char*)(&pvd[9]), "CDROM", 5) && pvd[14] == 1)));
		}

		static bool LoadISO(SFile& fi, std::vector<Track>& tracks)
		{
			// data track
			Track track = { 1, 0, 0, 0, 0, false, false, false, &fi };

			// try to detect iso type
			if      (CanReadPVD(fi, COOKED_SECTOR_SIZE, false)) { track.sector_size = COOKED_SECTOR_SIZE; track.mode2 = false; }
			else if (CanReadPVD(fi, RAW_SECTOR_SIZE,    false)) { track.sector_size = RAW_SECTOR_SIZE;    track.mode2 = false; }
			else if (CanReadPVD(fi, 2336,               true )) { track.sector_size = 2336;               track.mode2 = true;  }
			else if (CanReadPVD(fi, RAW_SECTOR_SIZE,    true )) { track.sector_size = RAW_SECTOR_SIZE;    track.mode2 = true;  }
			else if (CanReadPVD(fi, CD_FRAME_SIZE,      false)) { track.sector_size = CD_FRAME_SIZE;      track.mode2 = false; }
			else return false;

			track.frames = (int)(fi.size / track.sector_size);
			tracks.push_back(track);

			Track leadout_track = { 2, track.frames, 0, 0, track.sector_size };
			tracks.push_back(leadout_track);
			return true;
		}

		static bool AddTrack(std::vector<Track>& tracks, Track& curr, int& total_omitted_pregap)
		{
			const int track_index = (curr.start != -1 ? curr.start : (curr.pregap != -1 ? curr.pregap : 0));
			const int included_pregap = ((curr.start != -1 && curr.pregap != -1) ? (curr.frames != -1 ? curr.frames : (curr.pregap - curr.start)) : 0);
			const int omitted_pregap = ((curr.frames != -1 && !included_pregap) ? curr.frames : 0);
			if (included_pregap < 0) { ZIP_ASSERT(false); return false; }

			curr.frames = 0;
			curr.pregap = included_pregap;
			if (tracks.empty())
			{
				// first track (track number must be 1)
				if (curr.number != 1) { ZIP_ASSERT(false); return false; }
				curr.start = track_index + omitted_pregap;
				curr.skip = (Bit32u)(track_index * curr.sector_size);
			}
			else
			{
				Track &prev = *(tracks.end() - 1);
				if (prev.file == curr.file)
				{
					// current track consumes data from the same file as the previous
					prev.frames = track_index - (prev.start - total_omitted_pregap);
					curr.start = prev.start + prev.frames + omitted_pregap;
					curr.skip = prev.skip + prev.frames * prev.sector_size;
				}
				else
				{
					// current track uses a different file as the previous track
					prev.frames = (int)((prev.file->size - prev.skip + prev.sector_size - 1) / prev.sector_size); // round up
					curr.start = prev.start + prev.frames + track_index + omitted_pregap;
					curr.skip = (Bit32u)(track_index * curr.sector_size);
				}
				// error checks
				if (curr.number <= 1 || prev.number + 1 != curr.number || curr.start < prev.start + prev.frames || prev.frames < 0) { ZIP_ASSERT(false); return false; }
			}
			total_omitted_pregap += omitted_pregap;
			tracks.push_back(curr);
			return true;
		}

		static bool LoadCUE(SFile& fi, std::vector<Track>& tracks, std::vector<SFile*>& files)
		{
			if (!fi.size || fi.size > 32*1024) return false;
			std::string dosfilebuf;
			dosfilebuf.resize((size_t)fi.size + 1); // + 1 to enforce null terminator without using c_str()
			if (fi.Seek(0) != 0 ||  fi.Read((Bit8u*)&dosfilebuf[0], fi.size) != fi.size) return false;

			tracks.clear();
			Track track = { 0 };
			int total_omitted_pregap = 0;

			bool success = false, canAddTrack = false;

			for (char* p = &dosfilebuf[0], *pCommand, *pEOCommand, *pEOL, *pNumber, *pType, *pName, *pEOName; *p; p = pEOL)
			{
				while (*p && *p <= ' ') p++; // skip white space
				for (pCommand = p, pEOCommand = p; *pEOCommand > ' ';) pEOCommand++; // skip letters
				for (p = pEOCommand, pEOL = p; *pEOL && *pEOL != '\r' && *pEOL != '\n';) pEOL++; // find end of line
				for (; p != pEOL && *p <= ' ';) p++; // skip white space after command

				const int cmdLen = (int)(pEOCommand - pCommand);
				if (cmdLen == 5 && !memcmp(pCommand, "TRACK", 5))
				{
					success = !canAddTrack || AddTrack(tracks, track, total_omitted_pregap);

					// A CUE sheet can list both pre-gaps areas included in the track file as well as omitted pre-gaps (meant to be assumed filled zero)
					track.start = -1; // store point to start of pregap in file until call to AddTrack
					track.pregap = -1; // store point to end of pregap in file until call to AddTrack
					track.frames = -1; // store number of pregap frames omitted in file until call to AddTrack

					for (pNumber = p; *p > ' ';) p++; // skip over number
					for (; p != pEOL && *p <= ' '; ) p++; // skip over space
					for (pType = p; *p > ' ';) p++; // skip over type

					track.number = atoi(pNumber);

					const int typeLen = (int)(p - pType);
					if      (typeLen ==  5 && !memcmp(pType, "AUDIO",       5)) { track.sector_size = RAW_SECTOR_SIZE;    track.audio = true;  track.mode2 = false; }
					else if (typeLen == 10 && !memcmp(pType, "MODE1/2048", 10)) { track.sector_size = COOKED_SECTOR_SIZE; track.audio = false; track.mode2 = false; }
					else if (typeLen == 10 && !memcmp(pType, "MODE1/2352", 10)) { track.sector_size = RAW_SECTOR_SIZE;    track.audio = false; track.mode2 = false; }
					else if (typeLen == 10 && !memcmp(pType, "MODE2/2048", 10)) { track.sector_size = COOKED_SECTOR_SIZE; track.audio = false; track.mode2 = false; }
					else if (typeLen == 10 && !memcmp(pType, "MODE2/2336", 10)) { track.sector_size = 2336;               track.audio = false; track.mode2 = true;  }
					else if (typeLen == 10 && !memcmp(pType, "MODE2/2352", 10)) { track.sector_size = RAW_SECTOR_SIZE;    track.audio = false; track.mode2 = true;  }
					else success = false;

					canAddTrack = true;
				}
				else if ((cmdLen == 5 && !memcmp(pCommand, "INDEX", 5)) || (cmdLen == 6 && !memcmp(pCommand, "PREGAP", 6)))
				{
					int* pFrames = NULL;
					if (cmdLen == 5) // INDEX
					{
						for (pNumber = p; *p > ' ';) p++; // skip over number
						for (; p != pEOL && *p <= ' ';) p++; // skip over space
						int index = atoi(pNumber);
						if      (index == 1) pFrames = &track.pregap; // index post pregap
						else if (index == 0) pFrames = &track.start; // index pre pregap
						// ignore other indices
					}
					else pFrames = &track.frames; // PREGAP

					int min = 0, sec = 0, fr = 0;
					success = (pEOL - p > 5 && sscanf(p, "%d:%d:%d", &min, &sec, &fr) == 3);
					if (success && pFrames) *pFrames = ISO_MSF_TO_FRAMES(min, sec, fr);
				}
				else if (cmdLen == 4 && !memcmp(pCommand, "FILE", 4))
				{
					success = !canAddTrack || AddTrack(tracks, track, total_omitted_pregap);
					canAddTrack = false;

					if (*p == '"') for (pName = ++p, pEOName = p; pEOName != pEOL && *pEOName != '"';) pEOName++;
					else           for (pName = p,   pEOName = p; pEOName != pEOL && *pEOName >  ' ';) pEOName++;

					for (p = pEOName + 1; p != pEOL && *p <= ' ';) p++; // skip over space
					for (pType = p; *p > ' ';) p++; // skip over type

					track.file = NULL;

					std::string tmpImgPath;
					char* imgPath = &tmpImgPath.assign(fi.path).append("/../").append(pName, pEOName - pName).append(1, '\0')[0];
					size_t imgPathLen;
					for (char* pip = imgPath, *pipWrite = pip, *pipCuePart = pip + fi.path.length();;) // fix up '/../', '/./' and '//'
					{
						if (pip[0] == '\\' && pip >= pipCuePart) pip[0] = '/';
						int skip = (pip[0] == '/' ? ((pip[1] == '.' && pip[2] == '.' && pip[3] == '/') ? 3 : ((pip[1] == '.' && pip[2] == '/') ? 2 : ((pip[1] == '/') ? 1 : 0))) : 0);
						if (skip)
						{
							if (skip == 3) { for (pipWrite--; pipWrite > imgPath && pipWrite[0] != '/';) pipWrite--; } // go up one path
							pip += skip;
							continue;
						}
						if ((*(pipWrite++) = *(pip++)) == '\0') { imgPathLen = pipWrite - imgPath - 1; break; }
					}

					SFile* imgFile = NULL;
					for (SFile* fil : files)
						if (fil->path.length() == imgPathLen && !strncasecmp(&fil->path[0], imgPath, imgPathLen))
							{ imgFile = fil; break; }
					if (!imgFile)
					{
						std::string imgPathStr(imgPath, imgPathLen);
						imgFile = new SFileRaw(imgPathStr, false);
						if (!imgFile->size) { delete imgFile; imgFile = NULL; }
						else files.push_back(imgFile);
					}

					if (!imgFile)
					{
						LogErr("Unable to find image '%.*s' used by CD-ROM CUE '%s'\n", (int)imgPathLen, imgPath, fi.path.c_str());
					}
					else
					{
						const int typeLen = (int)(p - pType);
						if (typeLen ==  6 && !memcmp(pType, "BINARY", 6)) track.file = imgFile;
						else if ((typeLen ==  4 && (!memcmp(pType, "WAVE", 4) || !memcmp(pType, "AIFF", 4))) || (typeLen == 3 && !memcmp(pType, "MP3", 3))) goto do_leadout; // not supported
					}
				}
				else if (cmdLen) continue; // ignore all other commands
				if (!success) return false;
			}

			// add last track
			if (!AddTrack(tracks, track, total_omitted_pregap)) return false;

			// add leadout track
			do_leadout:
			track.number++;
			track.start = track.pregap = track.frames = -1;
			track.audio = false;
			track.file = NULL;
			if (!AddTrack(tracks, track, total_omitted_pregap)) return false;

			return true;
		}

		static bool LoadCHD(SFile& fi, std::vector<Track>& tracks, ChdState*& chd)
		{
			tracks.clear();

			bool not_chd = false;
			chd = NULL;
			if (0)
			{
				err:
				if (!not_chd) LogErr("Invalid or unsupported CHD file, must be an uncompressed version 5 CD image\n");
				if (chd) { delete chd; chd = NULL; }
				return false;
			}

			// Read CHD header and check signature
			Bit8u rawheader[CHD_V5_HEADER_SIZE];
			if (fi.Seek(0) != 0 || !fi.Read(rawheader, CHD_V5_HEADER_SIZE) || memcmp(rawheader, "MComprHD", 8)) { not_chd = true; goto err; }

			// Check supported version, flags and compression
			Bit32u hdr_length = ZIP_READ_BE32(&rawheader[8]);
			Bit32u hdr_version = ZIP_READ_BE32(&rawheader[12]);
			if (hdr_version != 5 || hdr_length != CHD_V5_HEADER_SIZE) goto err; // only ver 5 is supported
			if (ZIP_READ_BE32(&rawheader[16])) goto err; // compression is not supported

			// Make sure it's a CD image
			Bit32u unitsize = ZIP_READ_BE32(&rawheader[60]);
			int hunkbytes = (int)ZIP_READ_BE32(&rawheader[56]);
			if (unitsize != CD_FRAME_SIZE || (hunkbytes % CD_FRAME_SIZE) || !hunkbytes) goto err; // not CD sector size

			// Read file offsets for hunk mapping and track meta data
			Bit64u filelen = fi.size;
			Bit64u logicalbytes = ZIP_READ_BE64(&rawheader[32]);
			Bit64u mapoffset = ZIP_READ_BE64(&rawheader[40]);
			Bit64u metaoffset = ZIP_READ_BE64(&rawheader[48]);
			if (mapoffset < CHD_V5_HEADER_SIZE || mapoffset >= filelen || metaoffset < CHD_V5_HEADER_SIZE || metaoffset >= filelen || !logicalbytes) goto err;

			// Read track meta data
			chd = new ChdState();
			chd->hunkbytes = hunkbytes;
			Track empty_track = { 0, 0, 0, 0, CD_FRAME_SIZE, false, false, false, &fi };
			for (Bit64u metaentry_offset = metaoffset, metaentry_next; metaentry_offset != 0; metaentry_offset = metaentry_next)
			{
				char meta[256], mt_type[32], mt_subtype[32], mt_pgtype[32];
				Bit8u raw_meta_header[CHD_METADATA_HEADER_SIZE];
				if (fi.Seek(metaentry_offset) != metaentry_offset || !fi.Read(raw_meta_header, CHD_METADATA_HEADER_SIZE)) goto err;
				Bit32u metaentry_metatag = ZIP_READ_BE32(&raw_meta_header[0]);
				Bit32u metaentry_length = (ZIP_READ_BE32(&raw_meta_header[4]) & 0x00ffffff);
				metaentry_next = ZIP_READ_BE64(&raw_meta_header[8]);
				if (metaentry_metatag != CHD_CDROM_TRACK_METADATA_TAG && metaentry_metatag != CHD_CDROM_TRACK_METADATA2_TAG) continue;
				if (!fi.Read((Bit8u*)meta, (int)(metaentry_length > sizeof(meta) ? sizeof(meta) : metaentry_length))) goto err;
				//Log("%.*s\n", metaentry_length, meta);

				int mt_track_no = 0, mt_frames = 0, mt_pregap = 0;
				if (sscanf(meta,
					(metaentry_metatag == CHD_CDROM_TRACK_METADATA2_TAG ? "TRACK:%d TYPE:%30s SUBTYPE:%30s FRAMES:%d PREGAP:%d PGTYPE:%30s" : "TRACK:%d TYPE:%30s SUBTYPE:%30s FRAMES:%d"),
					&mt_track_no, mt_type, mt_subtype, &mt_frames, &mt_pregap, mt_pgtype) < 4) continue;

				// Add CHD tracks without using AddTrack because it's much simpler, we also support an incoming unsorted track list
				while (tracks.size() < (size_t)(mt_track_no)) { empty_track.number++; tracks.push_back(empty_track); }
				bool isAudio = !strcmp(mt_type, "AUDIO"), isMode2Form1 = (!isAudio && !strcmp(mt_type, "MODE2_FORM1")); // treated equivalent to MODE1
				Track& track = tracks[mt_track_no - 1];
				track.start = (mt_pgtype[0] != 'V' ? mt_pregap : 0); // pregap that was omitted from the CHD
				track.pregap = (mt_pgtype[0] == 'V' ? mt_pregap : 0); // pregap that is part of the CHD
				track.frames = mt_frames; // contains pregap only when part of the CHD, which is what we need
				track.audio = isAudio;
				track.mode2 = (mt_type[4] == '2' && !isMode2Form1);
				if (isAudio) continue;

				// Negate offset done in ReadSector
				if (isMode2Form1 || !strcmp(mt_type, "MODE1") || !strcmp(mt_type, "MODE2") || !strcmp(mt_type, "MODE2_FORM_MIX")) chd->cooked_sector_shift = -16;
				else if (!strcmp(mt_type, "MODE2_FORM2")) chd->cooked_sector_shift = -24;
			}

			Bit32u trackcount = (Bit32u)tracks.size();
			if (!trackcount || trackcount > 127) goto err; // no tracks found

			// Add leadout track for chd, just calculate it manually and skip AddTrack (which would call TrackFile::getLength).
			// AddTrack would wrongfully change the length of the last track. By doing this manually we don't need ChdFile::getLength.
			empty_track.number++;
			empty_track.file = NULL;
			tracks.push_back(empty_track);

			ZIP_STATIC_ASSERT(CHD_V5_UNCOMPMAPENTRYBYTES == sizeof(Bit32u));
			Bit32u hunkcount = (Bit32u)((logicalbytes + hunkbytes - 1) / hunkbytes);
			chd->hunkmap = (Bit32u*)malloc(hunkcount * CHD_V5_UNCOMPMAPENTRYBYTES);

			// Read hunk mapping and convert to file offsets
			if (fi.Seek(mapoffset) != mapoffset || !fi.Read((Bit8u*)chd->hunkmap, hunkcount * CHD_V5_UNCOMPMAPENTRYBYTES)) goto err;
			for (Bit32u i = 0; i != hunkcount; i++) chd->hunkmap[i] = ZIP_READ_BE32((Bit8u*)&chd->hunkmap[i]) * hunkbytes;

			// Now set physical start offsets for tracks and calculate CHD paddings. In CHD files tracks are padded to a to a 4-frame boundary.
			// Thus we need to give ChdFile::read a means to figure out the padding that applies to the physical sector number it is reading.
			for (Bit32u t = 1;; t++)
			{
				tracks[t].start += tracks[t - 1].start + tracks[t - 1].frames; // include omitted pregap with +=
				if (t == trackcount) break; // leadout only needs start
				tracks[t].skip = (((Bit32u)(tracks[t-1].skip / CD_FRAME_SIZE) + tracks[t-1].frames + (CHD_CD_TRACK_PADDING - 1)) / CHD_CD_TRACK_PADDING * CHD_CD_TRACK_PADDING) * CD_FRAME_SIZE;
			}
			return true;
		}

		bool TestOrFillTrackBuf(BuiltTrack** outBuiltTrack, int frames, int data_size, int in_zeros, int out_zeros, bool skip_pregap, const char* needSha1)
		{
			const Bit64u needsize = (Bit64u)(frames * data_size) - (in_zeros >= 0 ? (in_zeros + out_zeros) : 0);
			for (Track& t : tracks)
			{
				const Bit16s zerotag = (Bit16s)data_size * ((skip_pregap && t.pregap) ? -1 : 1);
				if (in_zeros >= 0 && t.zerotag != zerotag)
				{
					t.zerotag = zerotag;
					const bool raw = (t.sector_size >= RAW_SECTOR_SIZE);
					const int read_size = ZIP_MIN(t.sector_size, data_size);
					Bit32u inz = 0, outz = 0, sfrom = (Bit32u)(t.start + (skip_pregap ? t.pregap : 0)), sto = (Bit32u)(t.start + t.frames), tail = (Bit32u)(data_size - read_size), i;
					for (i = sfrom; i != sto; inz += tail) { for (const Bit8u *p = ReadSector(i++, raw), *pEnd = p + read_size; p != pEnd;) { if (*(p++)) { i = sto; break; } inz++; } }
					for (i = sto; i != sfrom; outz += tail) { for (const Bit8u *pEnd = ReadSector(--i, raw), *p = pEnd + read_size; p != pEnd;) { if (*(--p)) { i = sfrom; break; } outz++; } }
					t.inzeros = inz;
					t.outzeros = outz;
				}
				const Bit64u tsize = (Bit64u)((t.frames - (skip_pregap ? t.pregap : 0)) * data_size) - (in_zeros >= 0 ? (t.inzeros + t.outzeros) : 0);
				if (needsize && needsize != tsize) continue;
				if (!outBuiltTrack) return true; // potential match

				size_t bt_buf_size = frames * data_size;
				Bit8u* bt_buf = (Bit8u*)realloc((*outBuiltTrack ? (*outBuiltTrack)->buf : NULL), bt_buf_size);
				memset(bt_buf, 0, bt_buf_size);
				const bool raw = (t.sector_size >= RAW_SECTOR_SIZE);
				const int read_size = ZIP_MIN(t.sector_size, data_size);
				if (needsize)
				{
					Bit8u *pTrg = bt_buf + (in_zeros > 0 ? in_zeros : t.inzeros), *pTrgEnd = pTrg + needsize - (in_zeros > 0 ? 0 : t.inzeros);
					Bit32u tStart = (Bit32u)(t.start + (skip_pregap ? t.pregap : 0)), tFrame = (Bit32u)(tStart + t.inzeros / data_size), tFrameEnd = (Bit32u)(tStart + (t.inzeros + tsize + data_size - 1) / data_size);
					if (Bit32u tZeroOfs = (t.inzeros % data_size))
					{
						Bit8u *pTrgUntil = pTrg + read_size - tZeroOfs, *pTrgLimit = ZIP_MIN(pTrgUntil, pTrgEnd);
						memcpy(pTrg, ReadSector(tFrame++, raw) + tZeroOfs, (pTrgLimit - pTrg));
						pTrg += (data_size - tZeroOfs);
					}
					for (; tFrame != tFrameEnd; pTrg += data_size)
					{
						Bit8u *pTrgUntil = pTrg + read_size, *pTrgLimit = ZIP_MIN(pTrgUntil, pTrgEnd);
						memcpy(pTrg, ReadSector(tFrame++, raw), (pTrgLimit - pTrg));
					}
				}

				Bit8u tSha1[20], needSha1b[20];
				SHA1_CTX::Run(bt_buf, bt_buf_size, tSha1);
				if (!hextouint8(needSha1, needSha1b, 20) || memcmp(needSha1b, tSha1, 20)) continue;

				if (!*outBuiltTrack) *outBuiltTrack = new BuiltTrack;
				(*outBuiltTrack)->buf = bt_buf;
				(*outBuiltTrack)->bufsize = bt_buf_size;
				(*outBuiltTrack)->data_size = data_size;
				return true;
			}
			return false;
		}

		#pragma pack(1)
		struct isoDirEntry {
			Bit8u length, extAttrLength;
			#ifdef WORDS_BIGENDIAN
			Bit32u extentLocationL, extentLocation, dataLengthL, dataLength;
			#else
			Bit32u extentLocation, extentLocationM, dataLength, dataLengthM;
			#endif
			Bit8u dateYear, dateMonth, dateDay, timeHour, timeMin, timeSec, timeZone, fileFlags, fileUnitSize, interleaveGapSize;
			Bit16u VolumeSeqNumberL, VolumeSeqNumberM;
			Bit8u fileIdentLength, ident[222];
		};
		#pragma pack()

		static int ReadDirEntry(isoDirEntry& de, const Bit8u* data, bool iso)
		{
			// copy data into isoDirEntry struct, data[0] = length of DirEntry
			//	if (data[0] > sizeof(isoDirEntry)) return -1;//check disabled as isoDirentry is currently 258 bytes large. So it always fits
			memcpy(&de, data, data[0]); //Perhaps care about a zero at the end.

			// xa and interleaved mode not supported
			if (de.extAttrLength != 0 || de.fileUnitSize != 0 || de.interleaveGapSize != 0 || 33 + de.fileIdentLength > de.length || de.fileIdentLength > 221) return -1;
			de.ident[de.fileIdentLength] = '\0';

			if (ISO_IS_DIR(&de))
			{
				if      (de.fileIdentLength == 1 && de.ident[0] == 0) strcpy((char*)de.ident, ".");
				else if (de.fileIdentLength == 1 && de.ident[0] == 1) strcpy((char*)de.ident, "..");
			}

			// remove any file version identifiers as there are some cdroms that don't have them
			for (char* p = (char*)de.ident;; p++) { if (!*p || *p == ';') { *p = '\0'; de.fileIdentLength = (Bit8u)(p - (char*)de.ident); break; } }

			// if file has no extension remove the trailing dot
			if (de.fileIdentLength && de.ident[de.fileIdentLength - 1] == '.') de.ident[--de.fileIdentLength] = '\0';
			return de.length;
		}

		void IterateDir(isoDirEntry& deDir, bool iso, std::vector<SFile*>& files, std::string& ipath)
		{
			Bit32u currentSector = deDir.extentLocation, endSector = deDir.extentLocation + deDir.dataLength / ISO_FRAMESIZE - 1 + ((deDir.dataLength % ISO_FRAMESIZE != 0) ? 1 : 0);
			Bit8u buffer[ISO_FRAMESIZE];
			if (!ReadSector(currentSector, false, buffer)) return;

			// check if the directory entry is valid
			size_t pathlen = ipath.length();
			for (Bit32u ipos = 0;;)
			{
				// check if the next sector has to be read
				if ((ipos >= ISO_FRAMESIZE) || (buffer[ipos] == 0) || (ipos + buffer[ipos] > ISO_FRAMESIZE))
				{
					// check if there is another sector available
					if (currentSector >= endSector || !ReadSector(++currentSector, false, buffer)) return;
			 		ipos = 0;
				}
				// read sector and advance sector pointer
				isoDirEntry deFile;
				int length = ReadDirEntry(deFile, &buffer[ipos], iso);
				if (length <= 0) break;
				ipos += length;
				if (deFile.fileIdentLength == 0 || deFile.ident[deFile.ident[0] == '.' ? deFile.ident[1] == '.' ? 2 : 1 : 0] == '\0') continue;

				ipath.resize(pathlen);
				ipath.append((const char*)deFile.ident, deFile.fileIdentLength);
				if (ISO_IS_DIR(&deFile))
				{
					files.push_back(new SFileIso(*this, (ipath += '/'), 0, ZIP_PACKDATE(deFile.dateYear + 1900, deFile.dateMonth, deFile.dateDay), ZIP_PACKTIME(deFile.timeHour, deFile.timeMin, deFile.timeSec), deFile.extentLocation));
					IterateDir(deFile, iso, files, ipath);
				}
				else
					files.push_back(new SFileIso(*this, ipath, deFile.dataLength, ZIP_PACKDATE(deFile.dateYear + 1900, deFile.dateMonth, deFile.dateDay), ZIP_PACKTIME(deFile.timeHour, deFile.timeMin, deFile.timeSec), deFile.extentLocation));
			}
		}
	};

	static bool UsesExtension(const char* ext3, bool as_output)
	{
		return ext3 && (!strncasecmp(ext3, "ISO", 3) || !strncasecmp(ext3, "CHD", 3) || !strncasecmp(ext3, "CUE", 3) || (!as_output && (!strncasecmp(ext3, "INS", 3) || !strncasecmp(ext3, "IMG", 3) || !strncasecmp(ext3, "IMA", 3))));
	}

	static bool ValidSuperflous(const std::vector<SFile*>& files, SFile* chk)
	{
		// Check if a superfluous file entry parsed by IsoReader matches what IsoWriter generates (which can only be directory entries and then the date/time needs to match the highest child date)
		const char* fiPath = chk->path.c_str(); size_t fiLen = chk->path.length() - 1; // len without slash
		if (!*fiPath || (fiPath[fiLen] != '/' && fiPath[fiLen] != '\\')) return false;
		const SFile* fiDate = NULL;
		for (const SFile* fi : files) if (fi->IsContainedBy(fiPath, fiLen) && (!fiDate || (fi->date > fiDate->date || (fi->date == fiDate->date && fi->time > fiDate->time)))) fiDate = fi;
		return (chk->date == (fiDate ? fiDate->date : 0) && chk->time == (fiDate ? fiDate->time : 0));
	}

	static bool IndexFiles(SFile& fi, std::vector<SFile*>& files)
	{
		std::vector<IsoReader::Track> tracks;
		IsoReader::ChdState* chd = NULL;
		fi.Open();
		bool loaded = IsoReader::LoadISO(fi, tracks) || IsoReader::LoadCUE(fi, tracks, files) || IsoReader::LoadCHD(fi, tracks, chd);
		fi.Close();
		if (!loaded || tracks.size() <= 1) return false; // must have at least 1 regular track and 1 leadout track

		bool havedata = false, iso = false;
		IsoReader* reader = new IsoReader(fi, chd, tracks); // pass tracks

		std::string tmppath;
		size_t old_files_count = files.size();
		IsoReader::Track* datatrack = NULL;
		for (IsoReader::Track& t : reader->tracks) { if (!t.audio) { datatrack = &t; break; } }
		if (datatrack && datatrack->file)
		{
			const Bit8u* pvd = reader->ReadSector(ISO_FIRST_VD);
			if      (pvd && pvd[0] == 1 && !strncmp((char*)(&pvd[1]), "CD001", 5) && pvd[6]  == 1) { havedata = true; iso = true;  }
			else if (pvd && pvd[8] == 1 && !strncmp((char*)(&pvd[9]), "CDROM", 5) && pvd[14] == 1) { havedata = true; iso = false; }

			IsoReader::isoDirEntry rootEntry;
			if (havedata && IsoReader::ReadDirEntry(rootEntry, &pvd[iso ? 156 : 180], iso) > 0)
				reader->IterateDir(rootEntry, iso, files, ((tmppath = fi.path) += '/'));
		}
		if (old_files_count == files.size())
			files.push_back(new SFileIso(*reader, (tmppath = fi.path).append("/\b"), 0, 0, 0, 0)); // fake file for keeping IsoReader reference to potentially generate CHD
		return true;
	}

	Bit64u pos; IsoReader& reader; Bit32u firstsector;
	inline SFileIso(IsoReader& _reader, const std::string& _path, Bit64u _size, Bit16u _date, Bit16u _time, Bit32u _firstsector) : pos((Bit64u)-1), reader(_reader), firstsector(_firstsector)
	{
		typ = T_ISO;
		path = _path;
		size = _size;
		date = _date;
		time = _time;
		reader.AddRef();
	}
	virtual inline ~SFileIso() { reader.DelRef(); }
	virtual bool Open() { ZIP_ASSERT(pos == (Bit64u)-1 && size); pos = 0; return true; }
	virtual bool IsOpen() { return (pos != (Bit64u)-1); }
	virtual bool Close() { pos = (Bit64u)-1; return true; }
	virtual Bit64u Seek(Bit64s ofs, int origin = SEEK_SET) { switch (origin) { case SEEK_SET: default: pos = (Bit64u)ofs; break; case SEEK_CUR: pos += ofs; break; case SEEK_END: pos = size + ofs; break; } return (pos > size ? (pos = size) : pos); }
	virtual Bit64u Read(Bit8u* data, Bit64u len)
	{
		Bit64u posAndLen = pos+len, readEnd = (posAndLen > size ? size : posAndLen), readLen = (readEnd - pos);
		for (Bit64u remain = readLen; remain;)
		{
			const Bit8u* buf = reader.ReadSector(firstsector + (Bit32u)(pos / ISO_FRAMESIZE));
			if (!buf) { ZIP_ASSERT(0); return 0; }
			Bit16u sectorOfs = (Bit16u)(pos % ISO_FRAMESIZE), sectorRemain = (Bit16u)ISO_FRAMESIZE - sectorOfs, step = (remain < sectorRemain ? (Bit16u)remain : sectorRemain);
			memcpy(data, buf + sectorOfs, step);
			data += step;
			remain -= step;
			pos += step;
		}
		return readLen;
	}

	struct IsoWriter : SFile::Writer
	{
		// Make CHD and BIN files with just 2048 byte sized sectors, also supports making .ISO files
		#define ISOGEN_SECTOR_SIZE 2048

		// Make CHD and BIN files with raw sectors including sync head and checksums, disables support for making .ISO files
		//#define ISOGEN_SECTOR_SIZE 2352

		struct SQueuedFile { const char *wpath, *wpathX; Bit16u wdate, wtime; SFile* src; };

		// ISO record structures (recordLen is always zero padded to an even number of bytes)
		struct PathRecord
		{
			PathRecord() {}
			Bit8u nameLen, extAttrLen, dirSector[4], parentNumber[2], name[222];
			Bit32u _parentPathIndex, _DirRecordStart, _DirRecordEnd, _DirRecordSectors, _DirSector;
			inline Bit8u RecordLen() { return (Bit8u)(8 + ((nameLen + 1) & ~1)); } // pad to even byte numbers
			inline void Pad() { if (nameLen & 1) name[nameLen] = '\0'; } // pad to even byte numbers
		};
		struct DirRecord
		{
			enum : Bit8u { FLAG_DIR = ISO_DIRECTORY, RECORD_LEN_BASE = 33 };
			Bit8u recordLen, extAttrLen, dataSector[8], dataSize[8], dateY, dateM, dateD, timeH, timeM, timeS, timeZone, fileFlags, fileUnitSize, interleaveGapSize, VolumeSeqNumber[4], nameLen, name[222];
			Bit32u _fileIndex, _pathIndex;
			DirRecord() {}
			DirRecord(SQueuedFile* qf, Bit32u fileIndex, Bit32u pathIndex, bool isDir, const char* _name, Bit8u _nameLen) : _fileIndex(fileIndex), _pathIndex(pathIndex)
			{
				recordLen = RECORD_LEN_BASE + _nameLen + (1 - (_nameLen & 1)); // pad to even byte numbers
				extAttrLen = 0;
				Bit32u siz = ((qf && qf->src) ? (Bit32u)qf->src->size : (Bit32u)0);
				ZIP_WRITE_LB32(dataSize, siz);
				SetDate((qf ? qf->wdate : 0), (qf ? qf->wtime : 0));
				timeZone = 0; // gmtOffset;
				fileFlags = (isDir ? FLAG_DIR : 0); // file flags
				fileUnitSize = 0; // interleaved mode file unit size;
				interleaveGapSize = 0; // Interleave gap size
				ZIP_WRITE_LB16(VolumeSeqNumber, 1); // volume sequence number
				nameLen = _nameLen;
				memcpy(name, _name, _nameLen);
				if (!(_nameLen & 1)) name[_nameLen] = '\0'; // pad
			}
			void SetDate(Bit16u dat, Bit16u tim) { dateY = (Bit8u)((dat>>9)+80); dateM = (Bit8u)((dat>>5)&0xf); dateD = (Bit8u)(dat&0x1f); timeH = (Bit8u)(tim>>11); timeM = (Bit8u)((tim>>5)&0x3f); timeS = (Bit8u)((tim&0x1f)*2); }
		};

		std::vector<SQueuedFile> filequeue;
		std::vector<PathRecord> pathRecords; // filled LE, converted to BE during output
		std::vector<DirRecord> dirRecords;
		Bit32u pathTableSize = 0, fileSectors = 0, dirRecordSectors = 0, numSectors = 0, chdhunkcount = 0;
		Bit8u sec[ISO_FRAMESIZE], *chdbuf = NULL, *chdmap = NULL, *chdhunk = NULL, *chdhunkofs;
		enum { MODE_CHD, MODE_CUE, MODE_ISO } mode;

		IsoWriter(const char* path, const char* pathExt3) : SFile::Writer(path)
		{
			if (!failed) switch (pathExt3[1]|0x20)
			{
				case 'h':
					mode = MODE_CHD;
					fclose(f); // CHD needs wb+ for EndOutput
					failed |= ((f = fopen_utf8(path, "wb+")) == NULL);
					break;
				case 'u': {
					mode = MODE_CUE;
					std::string tmp;
					const char* pathbin = tmp.assign(path, (pathExt3 - path)).append("bin").c_str();
					FILE *fcue = f;
					if ((f = fopen_utf8(pathbin, "wb")) == NULL) { fclose(fcue); failed = true; break; }
					//Log("Writing cue sheet to %s ...\n", path);
					const char* lastS = strrchr(pathbin, '/'), *lastBS = strrchr(pathbin, '\\');
					fprintf(fcue, "FILE \"%s\" BINARY\r\n  TRACK 01 MODE1/%u\r\n    INDEX 01 00:00:00\r\n", (lastS > lastBS ? lastS + 1 : lastBS ? lastBS + 1 : path), ISOGEN_SECTOR_SIZE);
					fclose(fcue);
					break; }
				#if ISOGEN_SECTOR_SIZE == 2048
				default: mode = MODE_ISO; break;
				#else
				default: LogErr("IsoWriter Invalid output file '%s', must end with CHD or CUE\n"); failed = true; break;
				#endif
			}
		}

		~IsoWriter() { free(chdbuf); }

		virtual void WriteFile(const char* innerpath, size_t innerpath_len, Bit16u wdate, Bit16u wtime, SFile* fsrc, bool)
		{
			filequeue.push_back({innerpath, innerpath + innerpath_len, wdate, wtime, fsrc});
		}

		static void ChdWriteHeader(Bit8u *rawheader, Bit64u totalSize, Bit64u metaOffset)
		{
			memcpy(&rawheader[0], "MComprHD", 8);
			ZIP_WRITE_BE32(&rawheader[8], CHD_V5_HEADER_SIZE);
			ZIP_WRITE_BE32(&rawheader[12], 5);
			memset(&rawheader[16], 0, 32 - 16);
			ZIP_WRITE_BE64(&rawheader[32], totalSize);
			ZIP_WRITE_BE64(&rawheader[40], CHD_V5_HEADER_SIZE); // mapoffset
			ZIP_WRITE_BE64(&rawheader[48], metaOffset); //should be (mapoffset + hunkcount * 4) where hunkcount is ((logicalbytes + hunkbytes - 1) / hunkbytes)
			ZIP_WRITE_BE32(&rawheader[56], CHD_HUNKBYTES); // hunkbytes (8 units)
			ZIP_WRITE_BE32(&rawheader[60], CHD_UNITBYTES); // unitbytes
			memset(&rawheader[64], 0, CHD_V5_HEADER_SIZE - 64);
		}

		void ChdStartOutput(Bit32u totalISOSectors)
		{
			const Bit32u totalunits = (totalISOSectors + CHD_CD_TRACK_PADDING - 1) / CHD_CD_TRACK_PADDING * CHD_CD_TRACK_PADDING;
			const Bit32u totalunmappedhunks = (totalunits + 7) / 8;
			const size_t chdHeadSize = // uncompressed chd file structure
				CHD_V5_HEADER_SIZE // 124 bytes header
				+ (totalunmappedhunks * CHD_V5_UNCOMPMAPENTRYBYTES) // hunk map (4 bytes index)
				+ (CHD_METADATA_HEADER_SIZE + 256); // single data track meta array, followed by zeros until next hunk boundary
			chdbuf = (Bit8u*)malloc(((chdHeadSize + 7) & ~(Bit64u)7) + CHD_HUNKBYTES);
			chdmap = chdbuf + CHD_V5_HEADER_SIZE;
			chdhunk = chdbuf + ((chdHeadSize + 7) & ~(Bit64u)7);
			Bit8u *rawheader = chdbuf, *meta = rawheader + CHD_V5_HEADER_SIZE + (totalunmappedhunks * CHD_V5_UNCOMPMAPENTRYBYTES);
			ChdWriteHeader(rawheader, (totalunits * CHD_UNITBYTES), (Bit64u)(meta - rawheader));

			int len = sprintf((char*)meta + CHD_METADATA_HEADER_SIZE, "TRACK:%d TYPE:%s SUBTYPE:%s FRAMES:%d PREGAP:%d PGTYPE:%s PGSUB:%s POSTGAP:%d",
				1, (ISOGEN_SECTOR_SIZE == 2048 ? "MODE1" : "MODE1_RAW"), "NONE", (int)totalISOSectors, 0, "MODE1", "NONE", 0);

			ZIP_WRITE_BE32(&meta[0], CHD_CDROM_TRACK_METADATA2_TAG);
			ZIP_WRITE_BE32(&meta[4], len + 1); // len of formatted string with \0 terminator
			meta[4] = 0x1; // ALWAYS 0x01 (defined as CHD_MDFLAGS_CHECKSUM)
			ZIP_WRITE_BE64(&meta[8], 0); // offset from file start to next meta element, 0 for last element

			const size_t finalHeadLen = (meta + CHD_METADATA_HEADER_SIZE + len + 1 - chdbuf);
			failed |= !fwrite(chdbuf, finalHeadLen, 1, f);
			memset(chdhunk, 0, CHD_HUNKBYTES);
			failed |= !fwrite(chdhunk, CHD_HUNKBYTES - (finalHeadLen % CHD_HUNKBYTES), 1, f);
			chdhunkofs = chdhunk;
			chdhunkcount = (Bit32u)((finalHeadLen + CHD_HUNKBYTES - 1) / CHD_HUNKBYTES);
		}

		void ChdEndOutput()
		{
			if (mode != MODE_CHD) return;

			const size_t totalunmappedhunks = ((chdmap - (chdbuf + CHD_V5_HEADER_SIZE)) / 4) + ((chdhunkofs != chdhunk) ? 1 : 0);
			if (Bit32u garbagehunkidx = ((chdhunkofs != chdhunk && chdhunkofs <= chdhunk + (CHD_HUNKBYTES / 2) && totalunmappedhunks > 256) ? ZIP_READ_BE32(chdmap - 256*4) : 0))
			{
				// An unintended (but consistent) behavior of chdman can add garbage at the end of the final chunk from 256 (mapped) hunks ago
				memset(chdhunkofs, 0, (chdhunk + (CHD_HUNKBYTES / 2) - chdhunkofs));
				fseek_wrap(f, (garbagehunkidx * CHD_HUNKBYTES + (CHD_HUNKBYTES / 2)), SEEK_SET);
				failed |= !fread(chdhunk + (CHD_HUNKBYTES / 2), (CHD_HUNKBYTES / 2), 1, f);
				fseek_wrap(f, 0, SEEK_END);
				ChdPutHunk();
			}
			else if (chdhunkofs != chdhunk)
			{
				memset(chdhunkofs, 0, (chdhunk + CHD_HUNKBYTES - chdhunkofs));
				ChdPutHunk();
			}
			ZIP_ASSERT(ZIP_READ_BE32(chdmap) == CHD_CDROM_TRACK_METADATA2_TAG); // chdmap should now be perfectly filled and the cursor ends up being where the first track meta tag is
			fseek(f, 0, SEEK_SET);
			failed |= !fwrite(chdbuf, chdmap - chdbuf, 1, f); // write hunk map
		}

		void ChdPutHunk()
		{
			bool allzeros = true;
			for (Bit64u* p = (Bit64u*)chdhunk, *pEnd = (Bit64u*)(chdhunk + CHD_HUNKBYTES); p != pEnd; p++) { if (*p) { allzeros = false; break; } }
			if (allzeros)
			{
				ZIP_WRITE_BE32(chdmap, 0);
				chdmap += 4;
			}
			else
			{
				ZIP_WRITE_BE32(chdmap, chdhunkcount);
				chdmap += 4;
				failed |= !fwrite(chdhunk, CHD_HUNKBYTES, 1, f);
				chdhunkcount++;
			}
			chdhunkofs = chdhunk;
		}

		void WriteSector(size_t len)
		{
			ZIP_ASSERT(len <= ISO_FRAMESIZE);
			memset(sec + len, 0, ISO_FRAMESIZE - len);
			#if ISOGEN_SECTOR_SIZE == 2048 // ISO with 2048 bytes per sector
			if (mode == MODE_CHD) { memcpy(chdhunkofs, sec, ISO_FRAMESIZE); if ((chdhunkofs += CHD_UNITBYTES) == (chdhunk + CHD_HUNKBYTES)) ChdPutHunk(); }
			else failed |= !fwrite(sec, ISO_FRAMESIZE, 1, f);
			#elif ISOGEN_SECTOR_SIZE == 2352 // BIN with 2352 bytes per sector, MODE1 Data Track
			// MODE1 sector generation based on ECM by Neill Corlett
			Bit8u head[16], tail[288];
			// [0x000 ~ 0x00B] Sync pattern (00 FF ... FF 00)
			head[0] = 0x00;
			memset(head + 0x001, 0xFF, 0x00A);
			head[0x00B] = 0x00;
			// [0x00C ~ 0x00E] Sector address in MSF format (decimal number in hex)
			Bit32u nsector = numSectors + (75 * 2);
			Bit8u addrM = (nsector / (75 * 60)), addrS =  ((nsector / 75) % 60), addrF = (nsector % 75);
			head[0x00C] = ((addrM / 10 * 0x10) | (addrM % 10));
			head[0x00D] = ((addrS / 10 * 0x10) | (addrS % 10));
			head[0x00E] = ((addrF / 10 * 0x10) | (addrF % 10));
			// [0x00F] Data Track Mode
			head[0x00F] = 0x01;
			// EDC and ECC lookup tables
			static Bit8u ecc_f_lut[256], ecc_b_lut[256];
			static Bit32u edc_lut[256];
			if (!edc_lut[1]) 
			{
				for (Bit32u i = 0; i < 256; i++)
				{
					Bit8u j = (Bit8u)((i << 1) ^ (i & 0x80 ? 0x11D : 0));
					ecc_f_lut[i] = j;
					ecc_b_lut[i ^ j] = i;
					Bit32u edc = i;
					for (j = 0; j < 8; j++) edc = (edc >> 1) ^ (edc & 1 ? 0xD8018001 : 0);
					edc_lut[i] = edc;
				}
			}
			// [0x810 ~ 0x813] EDC (4 byte checksum)
			Bit32u edc = 0;
			//for (Bit8u *edcsrc = sector, *edcend = edcsrc + 0x810; edcsrc != edcend;) edc = (edc >> 8) ^ edc_lut[(edc ^ *(edcsrc++)) & 0xFF];
			for (Bit8u *edcsrc = head, *edcend = head + 0x010; edcsrc != edcend;) edc = (edc >> 8) ^ edc_lut[(edc ^ *(edcsrc++)) & 0xFF];
			for (Bit8u *edcsrc = sec,  *edcend = sec  + 0x800; edcsrc != edcend;) edc = (edc >> 8) ^ edc_lut[(edc ^ *(edcsrc++)) & 0xFF];
			ZIP_WRITE_LE32(tail, edc);
			// [0x814 ~ 0x81B] Reserved (zeroed)
			memset(tail + 0x004, 0x00, 8);
			// [0x81C ~ 0x92F] ECC (Error correction codes)
			Bit8u *eccout = tail+0x00C;
			const size_t major_counts[] = { 86, 52 }, minor_counts[] = { 24, 43 }, major_mults[] = { 2, 86 }, minor_incs[] = { 86, 88 };
			for (int pq = 0; pq != 2; pq++, eccout += 0xAC) // first P then Q codes 0xAC bytes afterwards
			{
				const size_t major_count = major_counts[pq], minor_count = minor_counts[pq], major_mult = major_mults[pq], minor_inc = minor_incs[pq];
				for (size_t size = major_count * minor_count, major = 0; major < major_count; major++)
				{
					Bit8u ecc_a = 0, ecc_b = 0;
					for (size_t index = (major >> 1) * major_mult + (major & 1), minor = 0; minor < minor_count; minor++)
					{
						const Bit8u temp = (index < 4 ? head[0x00C + index] : (index < 2052 ? sec[index - 4] : tail[index - 2052]));
						index += minor_inc;
						if (index >= size) { index -= size; }
						ecc_b ^= temp;
						ecc_a = ecc_f_lut[ecc_a ^ temp];
					}
					ecc_a = ecc_b_lut[ecc_f_lut[ecc_a] ^ ecc_b];
					eccout[major              ] = (ecc_a        );
					eccout[major + major_count] = (ecc_a ^ ecc_b);
				}
			}
			if (mode == MODE_CHD)
			{
				memcpy(chdhunkofs + 0x000, head, sizeof(head)); // [0x000 ~ 0x00F] Head
				memcpy(chdhunkofs + 0x010, sec,  sizeof(sec )); // [0x010 ~ 0x80F] Data
				memcpy(chdhunkofs + 0x810, tail, sizeof(tail)); // [0x810 ~ 0x92F] Tail
				if ((chdhunkofs += CHD_UNITBYTES) == (chdhunk + CHD_HUNKBYTES)) ChdPutHunk();
			}
			else
			{
				failed |= !fwrite(head, sizeof(head), 1, fiso); // [0x000 ~ 0x00F] Head
				failed |= !fwrite(sec,  sizeof(sec ), 1, fiso); // [0x010 ~ 0x80F] Data
				failed |= !fwrite(tail, sizeof(tail), 1, fiso); // [0x810 ~ 0x92F] Tail
			}
			#else
			#error Not implemented
			#endif
			numSectors++;
		}

		void FillDir(SQueuedFile* qf, size_t baseLen = 0, Bit8u dirNameLen = 0, const DirRecord* parentDot = NULL, Bit32u parentPathIndex = 0, Bit32u parentDirRecordIndex = (Bit32u)-1)
		{
			ZIP_ASSERT(!qf || !baseLen || (qf->wpath[baseLen] == '/' && qf->wpath[baseLen-1] != '/' && qf->wpath[baseLen+1] != '/'));
			//if (qf) printf("DIR [%8.*s]/[%-8.*s] (First File:  %.*s)\n", (parentDot ? pathRecords[parentDot->_pathIndex].nameLen : 0), (parentDot ? (char*)pathRecords[parentDot->_pathIndex].name : ""), dirNameLen, qf->wpath + baseLen - dirNameLen, (int)(qf->wpathX - qf->wpath), qf->wpath);

			PathRecord pr;
			pr.nameLen = (dirNameLen ? dirNameLen : 1);
			pr.extAttrLen = 0;
			memcpy(pr.name, (dirNameLen ? qf->wpath + baseLen - dirNameLen : "\0"), pr.nameLen);
			pr.Pad();
			pathTableSize += pr.RecordLen();
			pr._parentPathIndex = parentPathIndex;
			pr._DirRecordStart = (Bit32u)dirRecords.size();

			size_t dirLen = (baseLen ? baseLen + 1 : 0); // including slash
			SQueuedFile *qfFirst = qf, *qfBegin = (qf ? &filequeue[0] : NULL), *qfEnd = qfBegin + filequeue.size(), *qfDate = NULL;
			Bit32u dirSectors = 1, dirBytesLeft = (ISO_FRAMESIZE - ((DirRecord::RECORD_LEN_BASE + 1) * 2)); // dot and dotdot records already used
			dirRecords.resize(dirRecords.size() + 2);
			if (qf) for (const char *curName, *curNameEnd, *lastName = NULL, *lastNameEnd = NULL;; lastName = curName, lastNameEnd = curNameEnd)
			{
				if (!qfDate || (qf->wdate > qfDate->wdate || (qf->wdate == qfDate->wdate && qf->wtime > qfDate->wtime))) qfDate = qf;
				const char *sfPath = qf->wpath, *dirTerm = qf->wpathX - 1;
				curName = sfPath + dirLen;
				while (dirTerm >= curName && *dirTerm != '/' && *dirTerm != '\\') dirTerm--;
				curNameEnd = (dirTerm >= curName ? dirTerm : qf->wpathX);
				size_t nameLen = (curNameEnd - curName);
				if (nameLen && nameLen < sizeof(((DirRecord*)qf)->name) && (nameLen != (size_t)(lastNameEnd - lastName) || memcmp(curName, lastName, nameLen)))
				{
					//printf("    %s [%.*s] Size: %u\n", ((dirTerm >= curName) ? "SDIR" : "FILE"), nameLen, curName, (qf->src ? (unsigned)qf->src->size : (unsigned)0));
					dirRecords.emplace_back(qf, (Bit32u)(qf - qfBegin), (Bit32u)-1, (dirTerm >= curName), curName, (Bit8u)nameLen);
					if (dirTerm < curName) fileSectors += (Bit32u)(((qf ? qf->src->size : (Bit64u)0) + (ISO_FRAMESIZE-1)) / ISO_FRAMESIZE);
					Bit32u drLen = dirRecords.back().recordLen;
					if (dirBytesLeft < drLen) { dirSectors++; dirBytesLeft = ISO_FRAMESIZE - drLen; } else dirBytesLeft -= drLen;
				}
				if (++qf == qfEnd || (size_t)(qf->wpathX - qf->wpath) <= baseLen || memcmp(qf->wpath, sfPath, dirLen)) break;
			}

			Bit32u pathIndex = (Bit32u)pathRecords.size();
			pr._DirRecordEnd = (Bit32u)dirRecords.size();
			pr._DirRecordSectors = dirSectors;
			pathRecords.push_back(pr);
			dirRecordSectors += dirSectors;

			if (qfFirst->wpathX == qfFirst->wpath || qfFirst->wpathX[-1] == '/' || qfFirst->wpathX[-1] == '\\') qfDate = qfFirst;
			DirRecord drDot(qfDate, (Bit32u)-1, pathIndex, true, "\0", (Bit8u)1);
			dirRecords[pr._DirRecordStart + 0] = drDot;
			dirRecords[pr._DirRecordStart + 1] = (parentDot ? *parentDot : drDot);
			dirRecords[pr._DirRecordStart + 1].name[0] = '\x01';
			if (parentDot) dirRecords[parentDirRecordIndex].SetDate((qfDate ? qfDate->wdate : 0), (qfDate ? qfDate->wtime : 0));

			for (Bit32u i = pr._DirRecordStart + 2, iEnd = pr._DirRecordEnd; i != iEnd; i++)
			{
				DirRecord& dr = dirRecords[i];
				if (!(dr.fileFlags & DirRecord::FLAG_DIR)) continue;
				dr._pathIndex = (Bit32u)pathRecords.size();
				FillDir(qfBegin + dr._fileIndex, dirLen + dr.nameLen, dr.nameLen, &drDot, pathIndex, i);
			}
		}

		static int SortFunc(const void* va, const void* vb)
		{
			SQueuedFile *a = (SQueuedFile*)va, *b = (SQueuedFile*)vb;
			int la = (int)(a->wpathX - a->wpath), lb = (int)(b->wpathX - b->wpath), res = memcmp(a->wpath, b->wpath, ZIP_MIN(la, lb));
			return (res ? res : la < lb ? -1 : 1);
		}

		virtual bool Finalize(char* XmlGameInner)
		{
			if (failed) return false;

			// See if there is a <isolabel> element we can use as the label for the ISO 9660 file system
			char *label = NULL, *labelX = NULL, *pXml = XmlGameInner, *pXmlEnd, *pXmlNext, *pXmlText, *pXmlTextX;
			for (EXml x; pXml && (x = XMLParse(pXml, pXmlEnd)) != XML_END && x != XML_ELEM_END && (pXmlNext = XMLLevel(pXmlEnd, x, &pXmlText, &pXmlTextX)) != NULL; pXml = pXmlNext)
				if (XMLMatchTag(pXml, pXmlEnd, "isolabel", 8, NULL))
					{ XMLInlineStringConvert(pXmlText, pXmlTextX); label = pXmlText; labelX = pXmlTextX; break; }

			// Sort files by filename
			if (!filequeue.empty()) qsort(&filequeue[0], filequeue.size(), sizeof(filequeue[0]), SortFunc);

			//Log("Preparing CD-ROM ISO 9660 Structure ...\n");
			FillDir((!filequeue.empty() ? &filequeue[0] : NULL));

			const Bit32u lePathTableSector = ISO_FIRST_VD + 1 + 1;
			const Bit32u pathTableSectors = ((pathTableSize + (ISO_FRAMESIZE-1)) / ISO_FRAMESIZE);
			const Bit32u bePathTableSector = lePathTableSector + pathTableSectors;
			const Bit32u firstDirRecordSector = bePathTableSector + pathTableSectors;
			const Bit32u firstFileDataSector = firstDirRecordSector + dirRecordSectors;
			const Bit32u totalISOSectors = firstFileDataSector + fileSectors;
			//Log("Got %u files in %u directories which will result in a %u MB size ISO\n", (unsigned)filequeue.size(), (unsigned)pathRecords.size(), (unsigned)(totalISOSectors * 2048 / 1024 / 1024));

			// 16 boot sectors, volume descriptor, volume terminator
			//Log("Writing header sectors...\n");
			if (mode == MODE_CHD) ChdStartOutput(totalISOSectors);
			for (int i = 0; i != ISO_FIRST_VD; i++) WriteSector(0);
			sec[0] = 1; // type primary volume
			memcpy(sec+1, "CD001", 5); // id
			sec[6] = 1; // version
			sec[7] = 0; // unused
			memset(sec+8, ' ', 32); // system id string
			memset(sec+40, ' ', 32); // volume id string
			if (label) memcpy(sec+40, label, ZIP_MIN((labelX - label), 32));
			memset(sec+72, 0, 8); // unused
			ZIP_WRITE_LB32(sec+80, totalISOSectors) // total logical sectors
			memset(sec+88, 0, 32); // unused
			ZIP_WRITE_LB16(sec+120, 1) // set number
			ZIP_WRITE_LB16(sec+124, 1) // sequence number
			ZIP_WRITE_LB16(sec+128, ISO_FRAMESIZE) // logical block size
			ZIP_WRITE_LB32(sec+132, pathTableSize) // path table size
			ZIP_WRITE_LE32(sec+140, lePathTableSector) // path table sector le
			ZIP_WRITE_LE32(sec+144, 0) // path table opt le
			ZIP_WRITE_BE32(sec+148, bePathTableSector) // path table sector be
			ZIP_WRITE_BE32(sec+152, 0) // path table opt be
			ZIP_ASSERT(dirRecords[0].recordLen == 34 && (dirRecords[0].fileFlags & DirRecord::FLAG_DIR) && dirRecords[0].name[0] == '\0');
			ZIP_WRITE_LB32(dirRecords[0].dataSector, firstDirRecordSector);
			ZIP_WRITE_LB32(dirRecords[0].dataSize, pathRecords[0]._DirRecordSectors * ISO_FRAMESIZE);
			memcpy(sec+156, &dirRecords[0], DirRecord::RECORD_LEN_BASE + 1);
			memset(sec+190, ' ', 128); // set id
			memset(sec+318, ' ', 128); // publisher id
			memset(sec+446, ' ', 128); // preparer id
			memset(sec+574, ' ', 128); // application id
			memset(sec+702, ' ', 37); // copyright file id
			memset(sec+739, ' ', 37); // abstract file id
			memset(sec+776, ' ', 37); // bibliographic file id
			memcpy(sec+813, "0000000000000000\0", 17); // creation time
			memcpy(sec+830, "0000000000000000\0", 17); // modification time
			memcpy(sec+847, "0000000000000000\0", 17); // expiration time
			memcpy(sec+864, "0000000000000000\0", 17); // effective time
			sec[881] = 1; // file struct version
			WriteSector(882);
			sec[0] = 255; // type terminator
			memcpy(sec+1, "CD001", 5); // id
			sec[6] = 1; // version
			WriteSector(7);
			if (failed) return false;

			PathRecord *prBegin = &pathRecords[0], *prEnd = prBegin + pathRecords.size();
			Bit32u dirSec = firstDirRecordSector;
			for (PathRecord* pr = prBegin; pr != prEnd; dirSec += (pr++)->_DirRecordSectors) pr->_DirSector = dirSec;
			ZIP_ASSERT(dirSec == firstFileDataSector);

			//Log("Writing %u path records ...\n", (unsigned)pathRecords.size());
			for (Bit32u tableBE = 0; tableBE != 2; tableBE++)
			{
				ZIP_ASSERT(numSectors == (!tableBE ? lePathTableSector : bePathTableSector));
				Bit32u ofs = 0, remain = ISO_FRAMESIZE;
				for (PathRecord* pr = prBegin; pr != prEnd; remain = ISO_FRAMESIZE)
				{
					while (remain && pr != prEnd)
					{
						Bit16u parentNumber = (Bit16u)(pr->_parentPathIndex + 1);
						if (!tableBE) { ZIP_WRITE_LE32(pr->dirSector, pr->_DirSector); ZIP_WRITE_LE16(pr->parentNumber, parentNumber) }
						else          { ZIP_WRITE_BE32(pr->dirSector, pr->_DirSector); ZIP_WRITE_BE16(pr->parentNumber, parentNumber) }
						Bit32u step = (pr->RecordLen() - ofs);
						if (remain >= step) { memcpy((sec+ISO_FRAMESIZE)-remain, ((Bit8u*)pr) + ofs, step  ); ofs =      0; remain -= step; pr++; }
						else                { memcpy((sec+ISO_FRAMESIZE)-remain, ((Bit8u*)pr) + ofs, remain); ofs = remain; remain  = 0; }
					}
					WriteSector(ISO_FRAMESIZE-remain);
				}
			}
			ZIP_ASSERT(numSectors == firstDirRecordSector);

			//Log("Writing %u directory records ...\n", (unsigned)dirRecords.size());
			Bit32u fileSec = firstFileDataSector;
			for (PathRecord* pr = prBegin; pr != prEnd; pr++)
			{
				ZIP_ASSERT(numSectors == pr->_DirSector);
				Bit32u remain = ISO_FRAMESIZE;
				for (DirRecord *dr = &dirRecords[pr->_DirRecordStart], *drEnd = &dirRecords[0] + pr->_DirRecordEnd; dr != drEnd; remain = ISO_FRAMESIZE)
				{
					for (; remain >= dr->recordLen && dr != drEnd; remain -= (dr++)->recordLen)
					{
						if (dr->fileFlags & DirRecord::FLAG_DIR)
						{
							PathRecord* subpr = &pathRecords[dr->_pathIndex];
							ZIP_WRITE_LB32(dr->dataSector, subpr->_DirSector);
							ZIP_WRITE_LB32(dr->dataSize, subpr->_DirRecordSectors * ISO_FRAMESIZE);
						}
						else
						{
							Bit32u dataSize = ZIP_READ_LE32(dr->dataSize);
							ZIP_WRITE_LB32(dr->dataSector, (dataSize ? fileSec : 0));
							if (dataSize) fileSec += (dataSize + (ISO_FRAMESIZE-1)) / ISO_FRAMESIZE;
						}
						memcpy((sec+ISO_FRAMESIZE)-remain, dr, dr->recordLen);
					}
					WriteSector(ISO_FRAMESIZE-remain);
				}
			}
			ZIP_ASSERT(numSectors == firstFileDataSector && fileSec == totalISOSectors);

			//Log("Writing file contents ...\n");
			for (DirRecord *dr = &dirRecords[0], *drEnd = &dirRecords[0] + dirRecords.size(); dr != drEnd; dr++)
			{
				if ((dr->fileFlags & DirRecord::FLAG_DIR) || !ZIP_READ_LE32(dr->dataSize)) continue;
				ZIP_ASSERT(numSectors == ZIP_READ_LE32(dr->dataSector));
				SFile* fsrc = filequeue[dr->_fileIndex].src;
				bool wasOpen = fsrc->IsOpen();
				if (wasOpen) fsrc->Seek(0); else if (!fsrc->Open()) { failed = true; return false; }
				for (Bit64u step; (step = fsrc->Read(sec, ISO_FRAMESIZE)) != 0;) WriteSector((size_t)step);
				if (!wasOpen) fsrc->Close();
			}
			ZIP_ASSERT(numSectors == totalISOSectors);

			if (mode == MODE_CHD && !failed) ChdEndOutput();
			//Log("Done!\n\n");
			return !failed;
		}
	};

	static SFile* BuildCHDFromTracks(std::vector<BuiltTrack*>& builtTracks, Bit64u chdRomSize, const char* chdRomSha1)
	{
		for (BuiltTrack* bt : builtTracks) if (!bt) return NULL;

		Bit32u totalunits = 0;
		for (BuiltTrack* bt : builtTracks)
		{
			totalunits += (Bit32u)(bt->bufsize / bt->data_size);
			totalunits = (totalunits + (CHD_CD_TRACK_PADDING - 1)) / CHD_CD_TRACK_PADDING * CHD_CD_TRACK_PADDING;
		}
		const Bit32u totalunmappedhunks = (totalunits + 7) / 8;

		static const Bit8u zeroedHunkSha1[20] { 0x32, 0x6b, 0xf7, 0xa9, 0x91, 0x84, 0x0c, 0x66, 0x90, 0x49, 0x00, 0xcd, 0x96, 0x89, 0xf5, 0x89, 0xf4, 0x73, 0x10, 0xfa }; // sha1 of HUNKBYTES zero bytes

		Bit64u chdMaxSize = // uncompressed chd file structure
			CHD_V5_HEADER_SIZE // 124 bytes header
			+ (totalunmappedhunks * CHD_V5_UNCOMPMAPENTRYBYTES) // hunk map (4 bytes index)
			+ ((CHD_METADATA_HEADER_SIZE + 256) * builtTracks.size() + CHD_HUNKBYTES) // track meta array, zeros until next hunk boundary
			+ (totalunmappedhunks * CHD_HUNKBYTES); // first actual hunk (index is fileoffset / hunksize), all hunks until last, then eof (must be at hunk boundary)
		SFileMemory* res = new SFileMemory(chdMaxSize);
		Bit8u *rawheader = res->buf, *hunkmap = rawheader + CHD_V5_HEADER_SIZE, *meta = hunkmap + (totalunmappedhunks * CHD_V5_UNCOMPMAPENTRYBYTES);
		IsoWriter::ChdWriteHeader(rawheader, (totalunits * CHD_UNITBYTES), (Bit64u)(meta - rawheader));

		int tnum = 1;
		for (BuiltTrack* bt : builtTracks)
		{
			int len = sprintf((char*)meta + CHD_METADATA_HEADER_SIZE, "TRACK:%d TYPE:%s SUBTYPE:%s FRAMES:%d PREGAP:%d PGTYPE:%s%s PGSUB:%s POSTGAP:%d",
				tnum++, bt->ttype, "NONE", (int)(bt->bufsize / bt->data_size), (bt->pregap ? bt->pregap : bt->omitted_pregap), (bt->pregap ? "V" : ""), (bt->pregap ? bt->ttype : "MODE1"), "NONE", 0);

			Bit8u* metanext = meta + CHD_METADATA_HEADER_SIZE + len + 1;
			ZIP_WRITE_BE32(&meta[0], CHD_CDROM_TRACK_METADATA2_TAG);
			ZIP_WRITE_BE32(&meta[4], len + 1); // len of formatted string with \0 terminator
			meta[4] = 0x1; // ALWAYS 0x01 (defined as CHD_MDFLAGS_CHECKSUM)
			ZIP_WRITE_BE64(&meta[8], (bt == builtTracks.back() ? 0 : (metanext - rawheader))); // offset from file start to next meta element, 0 for last element
			meta = metanext;
		}

		struct Local
		{
			//// We could store only unique hunks as an optimization but chdman doesn't do this, so we also don't
			//struct HunkHash { Bit32u next; Bit8u sha[20]; };
			//HunkHash* hunkHashes;
			//Bit32u hunkHashMap[256];
			//Local(Bit32u headhunks, Bit32u totalunmappedhunks) { hunkHashes = (HunkHash*)malloc((headhunks + totalunmappedhunks) * sizeof(HunkHash)); memset(hunkHashMap, 0, sizeof(hunkHashMap)); }
			//~Local() { free(hunkHashes); }
			//Bit32u FindHunkIdx(Bit8u hunksha[20]) { for (Bit32u next = hunkHashMap[hunksha[0]]; next; next = hunkHashes[next].next) { if (!memcmp(hunksha, hunkHashes[next].sha, 20)) return next; } return 0; }
			//void KeepHunkHash(Bit32u hunkidx, Bit8u hunksha[20]) { hunkHashes[hunkidx].next = hunkHashMap[hunksha[0]]; memcpy(hunkHashes[hunkidx].sha, hunksha, 20); hunkHashMap[hunksha[0]] = hunkidx; }

			static void WriteHunk(Bit8u* temphunk, Bit32u& hunkcounter, Bit8u*& hunks, Bit8u*& hunkmap)
			{
				Bit8u hunksha[20];
				SHA1_CTX::Run(temphunk, CHD_HUNKBYTES, hunksha);
				Bit32u hunkidx = 0;
				if (memcmp(hunksha, zeroedHunkSha1, 20) /*&& (hunkidx = FindHunkIdx(hunksha)) == 0*/)
				{
					hunkidx = hunkcounter++;
					memcpy(hunks, temphunk, CHD_HUNKBYTES);
					hunks += CHD_HUNKBYTES;
					//KeepHunkHash(hunkidx, hunksha);
				}
				ZIP_WRITE_BE32(hunkmap, hunkidx);
				hunkmap += 4;
			}
		};

		Bit8u *temphunk = (Bit8u*)malloc(CHD_HUNKBYTES), *hnk = temphunk;
		Bit32u headhunks = (Bit32u)(((meta - rawheader) + (CHD_HUNKBYTES - 1)) / CHD_HUNKBYTES), hunkcounter = headhunks;
		Bit8u* hunks = rawheader + headhunks * CHD_HUNKBYTES;
		memset(meta, 0, (hunks - meta));

		totalunits = 0;
		for (BuiltTrack* bt : builtTracks)
		{
			const Bit32u btdsize = (Bit32u)bt->data_size, btunits = (Bit32u)(bt->bufsize / btdsize);
			const bool btaudio = !memcmp(bt->ttype, "AUDIO", 6);
			for (Bit8u *p = bt->buf, *pEnd = p + btdsize * btunits, clear = 8; p != pEnd; p += btdsize)
			{
				memcpy(hnk, p, btdsize);
				if (clear) { memset(hnk + btdsize, 0, (CHD_UNITBYTES - btdsize)); clear--; }
				if (btaudio) // CHD audio endian swap
					for (Bit8u *a = hnk, *aEnd = a + RAW_SECTOR_SIZE, tmp; a < aEnd; a += 2)
						{ tmp = a[0]; a[0] = a[1]; a[1] = tmp; }

				hnk += CHD_UNITBYTES;
				if (hnk == &temphunk[CHD_HUNKBYTES])
				{
					hnk = temphunk;
					Local::WriteHunk(temphunk, hunkcounter, hunks, hunkmap);
				}
			}

			for (totalunits += btunits; totalunits % CHD_CD_TRACK_PADDING; totalunits++)
			{
				memset(hnk, 0, CHD_UNITBYTES);
				hnk += CHD_UNITBYTES;
				if (hnk == &temphunk[CHD_HUNKBYTES])
				{
					hnk = temphunk;
					Local::WriteHunk(temphunk, hunkcounter, hunks, hunkmap);
				}
			}
		}
		if (hnk != temphunk)
		{
			memset(hnk, 0, temphunk + CHD_HUNKBYTES - hnk);
			if (Bit32u garbagehunkidx = ((hnk <= temphunk + CHD_HUNKBYTES / 2 && totalunmappedhunks > 256) ? ZIP_READ_BE32(hunkmap - (256 * 4)) : 0))
			{
				// An unintended (but consistent) behavior of chdman can add garbage at the end of the final chunk from 256 hunks ago
				memcpy(temphunk + CHD_HUNKBYTES / 2, rawheader + (garbagehunkidx * CHD_HUNKBYTES) + (CHD_HUNKBYTES / 2), CHD_HUNKBYTES / 2);
			}
			Local::WriteHunk(temphunk, hunkcounter, hunks, hunkmap);
		}
		ZIP_ASSERT(hunkmap == rawheader + CHD_V5_HEADER_SIZE + (totalunmappedhunks * CHD_V5_UNCOMPMAPENTRYBYTES));
		free(temphunk);

		res->size = (hunks - rawheader);

		Bit8u chdRomSha1b[20];
		if (res->size == chdRomSize && res->GetSHA1() && hextouint8(chdRomSha1, chdRomSha1b, 20) && !memcmp(chdRomSha1b, res->sha1, 20))
			return res;

		delete res;
		return NULL;
	}

	static bool TestOrBuildCHD(const std::vector<SFile*>& files, char* pCHDRomOpenTagEnd, Bit64u chdRomSize, const char* chdRomSha1 = NULL, SFile** builtFile = NULL)
	{
		std::vector<BuiltTrack*> builtTracks;
		SFileIso::IsoReader* lastReader = NULL;
		for (SFile* fil : files)
		{
			if (fil->typ != SFile::T_ISO || lastReader == &((SFileIso*)fil)->reader) continue;
			lastReader = &((SFileIso*)fil)->reader;

			EXml x;
			for (char *p = pCHDRomOpenTagEnd, *pEnd; p && (x = XMLParse(p, pEnd)) != XML_END && x != XML_ELEM_END; p = XMLLevel(pEnd, x))
			{
				char *tnumber, *ttype, *ttypeX, *tframes, *tpregap, *tomitted_pregap, *tsize, *tsha1, *tsha1X, *tin_zeros, *tout_zeros;
				if (!XMLMatchTag(p, pEnd, "track", 5, "number", &tnumber, NULL, "type", &ttype, &ttypeX, "frames", &tframes, NULL, "pregap", &tpregap, NULL, "omitted_pregap", &tomitted_pregap, NULL, "size", &tsize, NULL, "sha1", &tsha1, &tsha1X, "in_zeros", &tin_zeros, NULL, "out_zeros", &tout_zeros, NULL, NULL)) continue;
				const char *missField = (!tnumber ? "number" : !ttype ? "type" : !tframes ? "frames" : !tsize ? "size" : (!tsha1 || (tsha1X - tsha1) != 40) ? "sha1" : NULL);
				if (missField) { LogErr("<%s> element missing '%s' field!\n", "track", missField); continue; }

				Bit64u size = atoi64(tsize), frames = atoi64(tframes); int num = atoi(tnumber);
				if (!frames || (size % frames) || num <= 0 || num > 255) { ZIP_ASSERT(false); continue; }
				int data_size = (int)(size / frames), pregap = (tpregap ? atoi(tpregap) : 0), omitted_pregap = (tomitted_pregap ? atoi(tomitted_pregap) : 0), in_zeros = (tin_zeros ? atoi(tin_zeros) : -1), out_zeros = (tout_zeros ? atoi(tout_zeros) : -1);
				if (num == 1 && in_zeros == 1 && out_zeros == 0) in_zeros = out_zeros = -1; // ignore zeros on data tracks

				BuiltTrack* pBT = ((builtFile && (int)builtTracks.size() >= num) ? builtTracks[num - 1] : NULL);
				bool res = lastReader->TestOrFillTrackBuf((builtFile ? &pBT : NULL), (int)frames, data_size, in_zeros, out_zeros, (omitted_pregap > 0), tsha1);
				if (!builtFile) { if (res) return true; break; } // only test track 1
				if (res)
				{
					pBT->pregap = pregap;
					pBT->omitted_pregap = omitted_pregap;
					sprintf(pBT->ttype, "%.*s", ZIP_MIN((int)(ttypeX - ttype), (int)15), ttype);
					if (num > (int)builtTracks.size()) builtTracks.resize(num);
					builtTracks[num - 1] = pBT;
				}
			}
			if (builtFile && builtTracks.size() && (*builtFile = BuildCHDFromTracks(builtTracks, chdRomSize, chdRomSha1)) != NULL)
			{
				(*builtFile)->path.assign(lastReader->src.path).append("|AS_CHD");
				break;
			}
		}
		for (BuiltTrack* bt : builtTracks) delete bt;
		return false;
	}

	static SFile* BuildCHD(const std::vector<SFile*>& files, char* pCHDRomOpenTagEnd, Bit64u chdRomSize, const char* chdRomSha1)
	{
		SFile* builtFile = NULL;
		TestOrBuildCHD(files, pCHDRomOpenTagEnd, chdRomSize, chdRomSha1, &builtFile);
		return builtFile;
	}

	static bool CanPotentiallyBuildCHD(const std::vector<SFile*>& files, char* pCHDRomOpenTagEnd, Bit64u chdRomSize)
	{
		return TestOrBuildCHD(files, pCHDRomOpenTagEnd, chdRomSize);
	}

	static SFile* BuildBINOGGFromTrack(BuiltTrack& builtTrack, Bit64u romSize, const char* romSha1, int quality, const char* sourceSha1)
	{
		if (romSize == builtTrack.bufsize && (!sourceSha1 || sourceSha1 == romSha1 || !strncasecmp(romSha1, sourceSha1, 40)))
		{
			SFileMemory* res = new SFileMemory(0);
			res->buf = builtTrack.buf;
			res->size = romSize;
			builtTrack.buf = NULL; // don't free
			return res;
		}

		typedef Bit32u (*fnEncodeVorbisFeedSamples)(float* bufL, float* bufR, Bit32u num, void* user_data);
		typedef void (*fnEncodeVorbisOutput)(const void* data, Bit32u len, void* user_data);
		extern void WasmEncodeVorbis(int quality, fnEncodeVorbisFeedSamples feed, fnEncodeVorbisOutput outpt, void* user_data);

		// Very simple test if the OGG encoding produces the expected bits
		struct TestEncode
		{
			enum { TEST_LEN = 5000, TEST_EXPECT_CRC = 0x79d89c91 };
			float buf[TEST_LEN], *bufp; Bit32u crc;
			static Bit32u FeedSamples(float* bufL, float* bufR, Bit32u num, TestEncode* self)
			{
				Bit32u remain = (Bit32u)(self->buf + TEST_LEN - self->bufp);
				if (remain < num) num = remain;
				memcpy(bufL, self->bufp, num*4); memcpy(bufR, self->bufp, num*4);
				self->bufp += num;
				return num;
			}
			static void OggOutput(const void* data, Bit32u len, TestEncode* self) { self->crc ^= CRC32(data, len); }
		} *testenc = (TestEncode*)malloc(sizeof(TestEncode));

		for (float *bufp = testenc->buf, *bufpend = bufp + TestEncode::TEST_LEN, seed = 0; bufp != bufpend; bufp++)
			*bufp = (seed += (seed > 1 ? -1 : 0.000188019f*(bufpend-bufp)));
		testenc->bufp = testenc->buf;
		testenc->crc = 0;
		WasmEncodeVorbis(5, (fnEncodeVorbisFeedSamples)TestEncode::FeedSamples, (fnEncodeVorbisOutput)TestEncode::OggOutput, testenc);
		Bit32u testrescrc = testenc->crc;
		free(testenc);
		if (testrescrc != TestEncode::TEST_EXPECT_CRC)
		{
			LogErr("  Tried to encode an audio track to OGG but this system failed to produce the expected encoding results.\n");
			LogErr("  Expected result: 0x%08x - Test result: 0x%08x - Please report this as a bug at https://github.com/schellingb/DoDAT\n\n\n", TestEncode::TEST_EXPECT_CRC, testrescrc);
			return NULL;
		}

		struct Encode
		{
			size_t wavpcmlen, wavpcmpos, romcap, romlen;
			Bit8u *wavpcm, *rombuf;

			static Bit32u FeedSamples(float* bufL, float* bufR, Bit32u num, Encode* self)
			{
				Bit32u remain = (Bit32u)((self->wavpcmlen - self->wavpcmpos) / 4);
				if (remain < num) num = remain;
				signed char* pcm = (signed char*)(self->wavpcm + self->wavpcmpos);
				for (Bit32u i = 0; i != num; i++, pcm += 4)
				{
					bufL[i] = ((pcm[1] << 8) | (0x00ff & (int)pcm[0])) / 32768.f;
					bufR[i] = ((pcm[3] << 8) | (0x00ff & (int)pcm[2])) / 32768.f;
				}
				if (!self->wavpcmpos && self->wavpcmlen >= 1024*1024) { Log("  Encoding CD audio track to OGG: 0%%"); fflush(stderr); }
				self->wavpcmpos += num * 4;
				if ((self->wavpcmpos / (1024*1024)) != ((self->wavpcmpos - (num * 4)) / (1024*1024))) { Log(" .. %u%%", (Bit32u)(((Bit64u)self->wavpcmpos * 100 + 50) / self->wavpcmlen)); fflush(stderr); }
				if (self->wavpcmpos == self->wavpcmlen && self->wavpcmlen >= 1024*1024 && num) Log("\n");
				return num;
			}
			static void OggOutput(const void* data, Bit32u len, Encode* self)
			{
				while (self->romlen + len > self->romcap) self->rombuf = (Bit8u*)realloc(self->rombuf, (self->romcap += 1024*1024));
				memcpy(self->rombuf + self->romlen, data, len);
				self->romlen += len;
			}
		} enc = {0};
		enc.wavpcm = builtTrack.buf;
		enc.wavpcmlen = builtTrack.bufsize;

		WasmEncodeVorbis(quality, (fnEncodeVorbisFeedSamples)Encode::FeedSamples, (fnEncodeVorbisOutput)Encode::OggOutput, &enc);

		Bit8u oggSha1b[20], romSha1b[20];
		SHA1_CTX::Run(enc.rombuf, enc.romlen, oggSha1b);
		if (!hextouint8(romSha1, romSha1b, 20) || memcmp(romSha1b, oggSha1b, 20)) { free(enc.rombuf); return NULL; }

		SFileMemory* res = new SFileMemory(0);
		res->buf = enc.rombuf;
		res->size = enc.romlen;
		return res;
	}

	static bool TestOrBuildBINOGG(const std::vector<SFile*>& files, char* pRomOpenTagEnd, Bit64u romSize, const char* romSha1 = NULL, SFile** builtFile = NULL)
	{
		char *p = pRomOpenTagEnd, *pEnd, *stype, *stypeX, *sframes, *somitted_pregap, *ssize, *ssha1, *sin_zeros, *sout_zeros, *squality;
		if (XMLParse(p, pEnd) == XML_END || !XMLMatchTag(p, pEnd, "source", 6, "type", &stype, &stypeX, "frames", &sframes, NULL, "omitted_pregap", &somitted_pregap, NULL, "size", &ssize, NULL, "sha1", &ssha1, NULL, "in_zeros", &sin_zeros, NULL, "out_zeros", &sout_zeros, NULL, "quality", &squality, NULL, NULL)) return false;
		const char *missField = (!stype ? "type" : !sframes ? "frames" : NULL);
		if (missField) { LogErr("<%s> element missing '%s' field!\n", "source", missField); return false; }
		Bit64u size = (ssize ? atoi64(ssize) : romSize), frames = atoi64(sframes);
		if (!frames || (size % frames)) { ZIP_ASSERT(false); return false; }
		int data_size = (int)(size / frames), omitted_pregap = (somitted_pregap ? atoi(somitted_pregap) : 0), in_zeros = (sin_zeros ? atoi(sin_zeros) : -1), out_zeros = (sout_zeros ? atoi(sout_zeros) : -1);

		SFileIso::IsoReader* lastReader = NULL;
		for (SFile* fil : files)
		{
			if (fil->typ != SFile::T_ISO || lastReader == &((SFileIso*)fil)->reader) continue;
			lastReader = &((SFileIso*)fil)->reader;

			BuiltTrack* pBT = NULL;
			if (!lastReader->TestOrFillTrackBuf((builtFile ? &pBT : NULL), (int)frames, data_size, in_zeros, out_zeros, (omitted_pregap > 0), (ssha1 ? ssha1 : romSha1))) continue;
			if (!builtFile) return true; // potential match
			*builtFile = BuildBINOGGFromTrack(*pBT, romSize, romSha1, (squality ? atoi(squality) : 8), ssha1);
			delete pBT;
			if (*builtFile) { (*builtFile)->path.assign(lastReader->src.path).append("|TRACK"); return true; }
		}
		return false;
	}

	static SFile* BuildBINOGG(const std::vector<SFile*>& files, char* pRomOpenTagEnd, Bit64u romSize, const char* romSha1)
	{
		SFile* builtFile = NULL;
		TestOrBuildBINOGG(files, pRomOpenTagEnd, romSize, romSha1, &builtFile);
		return builtFile;
	}

	static bool CanPotentiallyBuildBINOGG(const std::vector<SFile*>& files, char* pRomOpenTagEnd, Bit64u romSize)
	{
		return TestOrBuildBINOGG(files, pRomOpenTagEnd, romSize);
	}

	static SFile* BuildCUE(char* cueName, char* cueNameX, char* pGameInner, Bit64u needCueSize)
	{
		size_t baseLen = (size_t)(cueNameX - cueName - 4), pathDirLen = baseLen, builtCueLen = 0;
		for (;pathDirLen > 0; pathDirLen--) { if (cueName[pathDirLen-1] == '/' || cueName[pathDirLen-1] == '\\') break; }

		EXml x;
		std::vector<std::vector<char>> cueTracks;
		for (char* p = pGameInner, *pEnd, *pNext; p && (x = XMLParse(p, pEnd)) != XML_END && x != XML_ELEM_END && (pNext = XMLLevel(pEnd, x)) != NULL; p = pNext)
		{
			char *romName, *romNameX, *romSize;
			if (!XMLMatchTag(p, pEnd, "rom", 3, "name", &romName, &romNameX, "size", &romSize, NULL, NULL)) continue;
			XMLInlineStringConvert(romName, romNameX);

			// Rom name needs to match everything up to the extension and then have a track number after (i.e. "GAME.cue" finds "GAME (Track 1).bin")
			size_t romLen = (size_t)(romNameX - romName);
			if (romLen < (baseLen + 12) || strncasecmp(cueName, romName, baseLen) || romName[baseLen] == '.') continue;
			char *romBracket = (char*)memchr(romName + baseLen, '(', romLen - baseLen), *romTrackNo = (romBracket ? (char*)memchr(romBracket, ' ', (size_t)(romNameX - romBracket)) : NULL);
			int trackNo = (romTrackNo ? atoi(romTrackNo) : 0);
			if (trackNo < 1 || trackNo > 200) continue;

			char *pSrc = pEnd, *stype = NULL, *sframes = NULL, *spregap = NULL, *somitted_pregap = NULL, *ssize = NULL;
			if (XMLParse(pSrc, pEnd) != XML_END) XMLMatchTag(pSrc, pEnd, "source", 6, "type", &stype, NULL, "frames", &sframes, NULL, "pregap", &spregap, NULL, "omitted_pregap", &somitted_pregap, NULL, "size", &ssize, NULL, NULL);
			Bit64u size = (ssize ? atoi64(ssize) : atoi64(romSize));
			int data_size = (sframes ? (int)(size / atoi64(sframes)) : !(size % 2352) ? 2352 : !(size % 2048) ? 2048 : 2336);
			int pregap = (spregap ? atoi(spregap) : 0), omitted_pregap = (somitted_pregap ? atoi(somitted_pregap) : 0);

			if (cueTracks.size() < (size_t)trackNo) cueTracks.resize((size_t)trackNo);
			std::vector<char> &cueTrack = cueTracks[trackNo-1];

			const char* ttype = (stype ? (const char*)stype : (trackNo > 1 ? "AUDIO" : "MODE1"));
			const bool isAudio = !strncasecmp(ttype, "AUDIO", 5);

			cueTrack.resize(160 + (romLen - pathDirLen));
			char *pcue = &cueTrack[0], binTrackType[16];
			sprintf(binTrackType, (isAudio ? "AUDIO" : "MODE%c/%04d"), ttype[4], (int)data_size);
			pcue += sprintf(pcue, "FILE \"%.*s\" %s\r\n", (int)(romLen - pathDirLen), (romName + pathDirLen), (isAudio ? "MP3" : "BINARY"));
			pcue += sprintf(pcue, "  TRACK %02d %s\r\n", trackNo, binTrackType);
			if (!pregap && !omitted_pregap)
			{
				// Data or audio track without pregap
				pcue += sprintf(pcue, "    INDEX 01 00:00:00\r\n");
			}
			else if (pregap)
			{
				// Data or audio track with included pregap use a pair of INDEX 00 and INDEX 01 tags
				pcue += sprintf(pcue, "    INDEX 00 00:00:00\r\n");
				pcue += sprintf(pcue, "    INDEX 01 %02d:%02d:%02d\r\n", (pregap/(60*75))%60, (pregap/75)%60, pregap%75);
			}
			else
			{
				// Data or audio track with omitted pregap use PREGAP and INDEX 01 tags
				pcue += sprintf(pcue, "    PREGAP %02d:%02d:%02d\r\n", (omitted_pregap/(60*75))%60, (omitted_pregap/75)%60, omitted_pregap%75);
				pcue += sprintf(pcue, "    INDEX 01 00:00:00\r\n");
			}
			cueTrack.resize((size_t)(pcue - &cueTrack[0]));
			if ((builtCueLen += cueTrack.size()) >= needCueSize) break;
		}
		if (builtCueLen != needCueSize) return NULL;

		SFileMemory* res = new SFileMemory(builtCueLen);
		Bit8u *pout = res->buf;
		for (std::vector<char> &cueTrack : cueTracks)
		{
			if (!cueTrack.size()) continue;
			memcpy(pout, &cueTrack[0], cueTrack.size());
			pout += cueTrack.size();
		}
		res->path.assign(cueName, (size_t)(cueNameX - cueName)).append("|GENERATED");
		return res;
	}
};

struct SFileFat : SFile
{
	struct FatReader
	{
		// BASED ON drive_fat.cpp of DOSBox (GPL2)
		// Copyright (C) 2002-2021  The DOSBox Team
		#pragma pack(1)
		struct SectorBoot
		{
			Bit8u nearjmp[3], oemname[8]; Bit16u bytespersector; Bit8u sectorspercluster; Bit16u reservedsectors; Bit8u fatcopies; Bit16u rootdirentries, totalsectorcount; Bit8u mediadescriptor;
			Bit16u sectorsperfat, sectorspertrack, headcount;
			Bit32u hiddensectorcount, totalsecdword; // 32-bit FAT extensions
			Bit8u bootcode[474], magic[2]; // 0x55 , 0xaa
		};
		struct SectorMBR
		{
			Bit8u booter[446];
			struct { Bit8u bootflag, beginchs[3], parttype, endchs[3]; Bit32u absSectStart, partSize; } pentry[4];
			Bit8u magic[2]; // 0x55 , 0xaa
		};
		struct DirEntry
		{
			Bit8u entryname[11], attrib, NTRes, milliSecondStamp;
			Bit16u crtTime, crtDate, accessDate, hiFirstClust, modTime, modDate, loFirstClust;
			Bit32u entrysize;
		};
		#pragma pack()

		enum { SECTOR_SIZE = 512 };
		FatReader(SFile* _imgfile, Bit16u _track_sectors, Bit16u _heads, Bit32u _cylinders, Bit32u startSector, const SectorBoot& _boot)
			: imgfile(_imgfile), refs(0), cylinders(_cylinders), start_sector(startSector), track_sectors(_track_sectors), heads(_heads), partition_heads(_boot.headcount), partition_track_sectors(_boot.sectorspertrack), partition_cluster_sectors(_boot.sectorspercluster), partition_reserved_sectors(_boot.reservedsectors)
		{
			// File system must be contiguous to use absolute sectors, otherwise CHS will be used
			absolute = ((_boot.headcount == heads) && (_boot.sectorspertrack == _track_sectors));

			// Get size of root dir in sectors
			Bit32u rootDirSectors = ((_boot.rootdirentries * 32) + (SECTOR_SIZE - 1)) / SECTOR_SIZE;
			Bit32u dataSectors = (_boot.totalsectorcount ? _boot.totalsectorcount : _boot.totalsecdword) - (_boot.reservedsectors + (_boot.fatcopies * _boot.sectorsperfat) + rootDirSectors);
			Bit32u clusterCount = dataSectors / _boot.sectorspercluster;
			firstDataSector = (_boot.reservedsectors + (_boot.fatcopies * _boot.sectorsperfat) + rootDirSectors) + startSector;
			firstRootDirSect = _boot.reservedsectors + (_boot.fatcopies * _boot.sectorsperfat) + startSector;
			lastFatChainSect = lastSector = 0xffffffff;

			// Determine FAT format
			if      (clusterCount < 4085)  fattype = FAT12;
			else if (clusterCount < 65525) fattype = FAT16;
			else                           fattype = FAT32;
		}
		~FatReader() { imgfile->Close(); }
		SFile* imgfile;
		Bit32u refs, cylinders, start_sector, firstDataSector, firstRootDirSect, lastFatChainSect, lastSector;
		Bit16u track_sectors, heads, partition_heads, partition_track_sectors, partition_cluster_sectors, partition_reserved_sectors;
		Bit8u fatChainBuffer[SECTOR_SIZE * 2], sectorBuffer[SECTOR_SIZE];
		enum EFatType { FAT12, FAT16, FAT32 } fattype;
		bool absolute;
		void AddRef() { refs++; }
		void DelRef() { ZIP_ASSERT(refs); if (!--refs) delete this; }

		static bool Read_AbsoluteSector(SFile& fi, Bit32u sectnum, Bit8u* data)
		{
			Bit64u pos = sectnum * SECTOR_SIZE;
			return (fi.Seek(pos) == pos && fi.Read(data, SECTOR_SIZE));
		}
		inline bool Read_Sector(Bit32u head, Bit32u cylinder, Bit32u sector, Bit8u* data)
		{
			return Read_AbsoluteSector(*imgfile, ((cylinder * heads + head) * track_sectors ) + sector - 1L, data);
		}
		bool ReadFatSector(Bit32u sectnum, Bit8u* data)
		{
			if (absolute) return Read_AbsoluteSector(*imgfile, sectnum, data);
			Bit32u cylindersize = partition_heads * partition_track_sectors;
			Bit32u cylinder = sectnum / cylindersize;
			sectnum %= cylindersize;
			Bit32u head = sectnum / partition_track_sectors;
			Bit32u sector = sectnum % partition_track_sectors + 1L;
			return Read_Sector(head, cylinder, sector, data);
		}
		const Bit8u* CacheSector(Bit32u sectnum)
		{
			if (lastSector == sectnum) return sectorBuffer;
			if (!ReadFatSector(sectnum, sectorBuffer)) return NULL;
			lastSector = sectnum;
			return sectorBuffer;
		}

		#ifdef WORDS_BIGENDIAN
		static inline Bit16u VarRead(Bit16u var) { return __builtin_bswap16(var); }
		static inline Bit32u VarRead(Bit32u var) { return __builtin_bswap32(var); }
		#else
		static inline Bit16u VarRead(Bit16u var) { return var; }
		static inline Bit32u VarRead(Bit32u var) { return var; }
		#endif

		Bit32u getAbsoluteSectFromChain(Bit32u clustNum, Bit32u logicalSector)
		{
			for (Bit32u skipClust = (logicalSector / partition_cluster_sectors); skipClust; skipClust--)
			{
				const bool isOddCluster = (clustNum & 0x1);
				switch (fattype)
				{
					case FAT12: clustNum += (clustNum / 2); break;
					case FAT16: clustNum *= 2; break;
					case FAT32: clustNum *= 4; break;
				}

				const Bit32u fatChainSect = (partition_reserved_sectors + (clustNum / SECTOR_SIZE) + start_sector);
				if (lastFatChainSect != fatChainSect)
				{
					// Load two sectors at once for FAT12
					ReadFatSector(fatChainSect, &fatChainBuffer[0]);
					if (fattype == FAT12) ReadFatSector(fatChainSect + 1, &fatChainBuffer[SECTOR_SIZE]);
					lastFatChainSect = fatChainSect;
				}

				const Bit32u chainOfs = (clustNum % SECTOR_SIZE);
				switch (fattype)
				{
					case FAT12: clustNum = VarRead(*(Bit16u*)&fatChainBuffer[chainOfs]); clustNum = (isOddCluster ? (clustNum >> 4) : (clustNum & 0xfff)); if (clustNum >= 0xff8) return 0; break;
					case FAT16: clustNum = VarRead(*(Bit16u*)&fatChainBuffer[chainOfs]); if (clustNum >= 0xfff8) return 0; break;
					case FAT32: clustNum = VarRead(*(Bit32u*)&fatChainBuffer[chainOfs]) & 0x0fffffff; if (clustNum >= 0x0ffffff8) return 0; break; // upper 4 bits are reserved
				}
			}
			return ((clustNum - 2) * partition_cluster_sectors) + firstDataSector + (logicalSector % partition_cluster_sectors);
		}

		bool IterateDir(const Bit32u dirClustNumber, const Bit32u parentDirClustNumber, std::vector<SFile*>& files, std::string& ipath, Bit16u root_dir_entries = 0)
		{
			enum { DOS_ATTR_READ_ONLY = 0x01, DOS_ATTR_HIDDEN = 0x02, DOS_ATTR_SYSTEM = 0x04, DOS_ATTR_VOLUME = 0x08, DOS_ATTR_DIRECTORY = 0x10, DOS_ATTR_ARCHIVE = 0x20, DOS_ATTR_DEVICE = 0x40 };

			ipath += '/';
			size_t pathlen = ipath.length();

			DirEntry sectbuf[16]; // 16 directory entries per sector
			for (Bit16u dirPos = 0;; dirPos++)
			{
				Bit32u logentsector = (dirPos / 16); // Logical entry sector
				Bit32u entryoffset  = (dirPos % 16); // Index offset within sector
				if (!entryoffset)
				{
					if (dirClustNumber == 0 && dirPos >= root_dir_entries) return false;
					Bit32u fatSectorNum = (dirClustNumber == 0 ? (firstRootDirSect + logentsector) : getAbsoluteSectFromChain(dirClustNumber, logentsector));
					if (fatSectorNum == 0) return false;
					ReadFatSector(fatSectorNum, (Bit8u*)sectbuf);
				}

				const DirEntry& entry = sectbuf[entryoffset];
				if (entry.entryname[0] == 0xe5) continue; // Deleted file entry
				if (entry.entryname[0] == 0x00) return false; // End of directory list
				if (entry.attrib & (DOS_ATTR_VOLUME|DOS_ATTR_DEVICE)) continue; // ignore volume description entries

				const Bit32u entryClustNumber = (VarRead(entry.hiFirstClust) << 16) | VarRead(entry.loFirstClust);
				if (entryClustNumber == dirClustNumber || entryClustNumber == parentDirClustNumber) continue; // probably . or .. directory entries

				char name[13], *name_src = (char*)entry.entryname, *name_end = name_src+8, *ext_src = name_src + 8, *ext_end = name_src+11;
				while (name_end > name_src && (name_end[-1] == ' ' || name_end[-1] == '\0')) name_end--;
				while (ext_end  > ext_src  && (ext_end[-1]  == ' ' || ext_end[-1]  == '\0')) ext_end--;
				memcpy(name, name_src, (size_t)(name_end - name_src));
				if (ext_end > ext_src) { name[name_end - name_src] = '.'; memcpy(&name[name_end - name_src + 1], ext_src, (size_t)(ext_end - ext_src)); }
				size_t name_len = (name_end - name_src + (ext_end > ext_src ? 1 + (ext_end - ext_src) : 0));

				ipath.resize(pathlen);
				ipath.append(name, name_len);
				if (entry.attrib & DOS_ATTR_DIRECTORY)
				{
					files.push_back(new SFileFat(*this, (ipath += '/'), 0, entry.modDate, entry.modTime, entryClustNumber));
					IterateDir(entryClustNumber, dirClustNumber, files, ipath);
				}
				else
					files.push_back(new SFileFat(*this, ipath, entry.entrysize, entry.modDate, entry.modTime, entryClustNumber));
			}
		}
	};

	static bool UsesExtension(const char* ext3)
	{
		return (ext3 && (!strncasecmp(ext3, "IMG", 3) || !strncasecmp(ext3, "IMA", 3) || !strncasecmp(ext3, "VHD", 3)));
	}

	static bool IndexFiles(SFile& fi, std::vector<SFile*>& files)
	{
		Bit16u trackSectors = 63, heads = 16; // sectors per track, tracks per cylinder (aka heads)
		Bit32u cylinders = (Bit32u)(fi.size / (FatReader::SECTOR_SIZE * trackSectors * heads)), startSector = 0, partSize = 0, sizekb = (Bit32u)(fi.size / 1024);
		FatReader::SectorMBR mbr;
		FatReader::SectorBoot boot;
		bool is_hdd = (sizekb > 2880);
		if (is_hdd)
		{
			fi.Open();
			for (int m = (FatReader::Read_AbsoluteSector(fi, 0, (Bit8u*)&mbr) ? 0 : 4); m != 4; m++)
			{
				if (!mbr.pentry[m].partSize) continue; // should this also test valid FAT partition types?
				startSector  = FatReader::VarRead(mbr.pentry[m].absSectStart);
				partSize     = FatReader::VarRead(mbr.pentry[m].partSize);
				break;
			}
			if (!partSize || mbr.magic[0] != 0x55 || mbr.magic[1] != 0xaa) { fi.Close(); return false; }
		}
		else
		{
			static const struct DiskGeo { Bit32u kbsize; Bit16u track_sectors, heads, cylinders, biosval; } DiskGeometryList[] = 
			{
				{  160,  8, 1, 40, 0 }, // SS/DD 5.25"
				{  180,  9, 1, 40, 0 }, // SS/DD 5.25"
				{  200, 10, 1, 40, 0 }, // SS/DD 5.25" (booters)
				{  320,  8, 2, 40, 1 }, // DS/DD 5.25"
				{  360,  9, 2, 40, 1 }, // DS/DD 5.25"
				{  400, 10, 2, 40, 1 }, // DS/DD 5.25" (booters)
				{  720,  9, 2, 80, 3 }, // DS/DD 3.5"
				{ 1200, 15, 2, 80, 2 }, // DS/HD 5.25"
				{ 1440, 18, 2, 80, 4 }, // DS/HD 3.5"
				{ 1680, 21, 2, 80, 4 }, // DS/HD 3.5"  (DMF)
				{ 2880, 36, 2, 80, 6 }, // DS/ED 3.5"
			};
			trackSectors = 0;
			for (const DiskGeo* dg = DiskGeometryList, *dgEnd = dg + (sizeof(DiskGeometryList)/sizeof(*DiskGeometryList)); dg != dgEnd; dg++)
			{
				if (dg->kbsize != sizekb && dg->kbsize+1 != sizekb) continue;
				trackSectors = dg->track_sectors;
				heads        = dg->heads;
				cylinders    = dg->cylinders;
				//floppybiostyoe = dg->biosval;
				break;
			}
			if (!trackSectors) return false;
			fi.Open();
		}

		if (!FatReader::Read_AbsoluteSector(fi, startSector, (Bit8u*)&boot)) { fi.Close(); return false; }
		boot.bytespersector    = FatReader::VarRead(boot.bytespersector);
		boot.reservedsectors   = FatReader::VarRead(boot.reservedsectors);
		boot.rootdirentries    = FatReader::VarRead(boot.rootdirentries);
		boot.totalsectorcount  = FatReader::VarRead(boot.totalsectorcount);
		boot.sectorsperfat     = FatReader::VarRead(boot.sectorsperfat);
		boot.sectorspertrack   = FatReader::VarRead(boot.sectorspertrack);
		boot.headcount         = FatReader::VarRead(boot.headcount);
		boot.totalsecdword     = FatReader::VarRead(boot.totalsecdword);

		if (is_hdd)
		{
			trackSectors = FatReader::VarRead(boot.sectorspertrack);
			heads        = FatReader::VarRead(boot.headcount);
			cylinders    = (startSector + partSize + trackSectors * heads - 1) / (trackSectors * heads);
		}
		else
		{
			// Identify floppy format
			if ((boot.nearjmp[0] == 0x69 || boot.nearjmp[0] == 0xe9 || (boot.nearjmp[0] == 0xeb && boot.nearjmp[2] == 0x90)) && (boot.mediadescriptor & 0xf0) == 0xf0)
			{
				// DOS 2.x or later format, BPB assumed valid
				if ((boot.mediadescriptor != 0xf0 && !(boot.mediadescriptor & 0x1)) && (boot.oemname[5] != '3' || boot.oemname[6] != '.' || boot.oemname[7] < '2'))
				{
					// Fix pre-DOS 3.2 single-sided floppy
					boot.sectorspercluster = 1;
				}
			}
			else
			{
				// Read media descriptor in FAT
				Bit8u sectorBuffer[FatReader::SECTOR_SIZE];
				FatReader::Read_AbsoluteSector(fi, 1, sectorBuffer);
				Bit8u mdesc = sectorBuffer[0];
				if (mdesc < 0xf8)
				{
					// Unknown format
					fi.Close();
					return false;
				}

				// DOS 1.x format, create BPB for 160kB floppy
				boot.bytespersector = FatReader::SECTOR_SIZE;
				boot.sectorspercluster = 1;
				boot.reservedsectors = 1;
				boot.fatcopies = 2;
				boot.rootdirentries = 64;
				boot.totalsectorcount = 320;
				boot.mediadescriptor = mdesc;
				boot.sectorsperfat = 1;
				boot.sectorspertrack = 8;
				boot.headcount = 1;
				boot.magic[0] = 0x55; // to silence warning
				boot.magic[1] = 0xaa;
				if (!(mdesc & 0x2))
				{
					// Adjust for 9 sectors per track
					boot.totalsectorcount = 360;
					boot.sectorsperfat = 2;
					boot.sectorspertrack = 9;
				}
				if (mdesc & 0x1)
				{
					// Adjust for 2 sides
					boot.sectorspercluster = 2;
					boot.rootdirentries = 112;
					boot.totalsectorcount *= 2;
					boot.headcount = 2;
				}
			}
		}

		//if ((bootbuffer.magic[0] != 0x55) || (bootbuffer.magic[1] != 0xaa)) // Not a FAT filesystem
		//	LogErr("Image has no valid magicnumbers at the end!\n");

		// Sanity checks (FAT32 and non-standard sector sizes not implemented)
		if (!boot.sectorsperfat || boot.bytespersector != FatReader::SECTOR_SIZE || !boot.sectorspercluster || !boot.rootdirentries || !boot.fatcopies || !boot.headcount || boot.headcount > heads || !boot.sectorspertrack || boot.sectorspertrack > trackSectors)
			{ fi.Close(); return false; }

		FatReader* reader = new FatReader(&fi, trackSectors, heads, cylinders, startSector, boot); // pass already opened file
		std::string path = fi.path;
		size_t old_files_count = files.size();
		reader->IterateDir(0, 0, files, path, boot.rootdirentries);
		if (old_files_count == files.size()) delete reader;
		return true;
	}

	Bit64u pos; FatReader& reader; Bit32u chaincluster;
	inline SFileFat(FatReader& _reader, const std::string& _path, Bit64u _size, Bit16u _date, Bit16u _time, Bit32u _chaincluster) : pos((Bit64u)-1), reader(_reader), chaincluster(_chaincluster)
	{
		typ = T_FAT;
		path = _path;
		size = _size;
		date = _date;
		time = _time;
		reader.AddRef();
	}
	virtual inline ~SFileFat() { reader.DelRef(); }
	virtual bool Open() { ZIP_ASSERT(pos == (Bit64u)-1); pos = 0; return true; }
	virtual bool IsOpen() { return (pos != (Bit64u)-1); }
	virtual bool Close() { pos = (Bit64u)-1; return true; }
	virtual Bit64u Seek(Bit64s ofs, int origin = SEEK_SET) { switch (origin) { case SEEK_SET: default: pos = (Bit64u)ofs; break; case SEEK_CUR: pos += ofs; break; case SEEK_END: pos = size + ofs; break; } return (pos > size ? (pos = size) : pos); }
	virtual Bit64u Read(Bit8u* data, Bit64u len)
	{
		Bit64u posAndLen = pos+len, readEnd = (posAndLen > size ? size : posAndLen), readLen = (readEnd - pos);
		for (Bit64u remain = readLen; remain;)
		{
			Bit32u sectorNum = reader.getAbsoluteSectFromChain(chaincluster, (Bit32u)(pos / FatReader::SECTOR_SIZE));
			const Bit8u* sectorBuffer = reader.CacheSector(sectorNum);
			if (!sectorNum || !sectorBuffer) { ZIP_ASSERT(0); return 0; }
			Bit16u sectorOfs = (Bit16u)(pos % FatReader::SECTOR_SIZE), sectorRemain = (Bit16u)FatReader::SECTOR_SIZE - sectorOfs, step = (remain < sectorRemain ? (Bit16u)remain : sectorRemain);
			memcpy(data, sectorBuffer + sectorOfs, step);
			data += step;
			remain -= step;
			pos += step;
		}
		return readLen;
	}
};

static bool VerifyGame(char* pGameInner, char* gameName, char* gameNameX, const std::string& outBase, std::string& workPath, bool fixMode = false, bool crcOnlyCheck = false, char** pGameEn = NULL, bool* notFound = NULL);

static bool BuildRom(char* pGameInner, char* gameName, char* gameNameX, const std::string& outBase, std::string& workPath, const std::vector<SFile*>& files, bool isFix = false, bool forceTry = false, bool useSrcDates = false, bool logPartialMatch = true, bool verifyExisting = true, char** pGameEn = NULL)
{
	Bit32u needRoms = 0, haveSizeMatches = 0, generatable = 0;
	char* p, *pEnd, *pNext, *textStart, *textEnd;
	EXml x;
	for (p = pGameInner; p && (x = XMLParse(p, pEnd)) != XML_END && x != XML_ELEM_END && (pNext = XMLLevel(pEnd, x)) != NULL; p = pNext)
	{
		char *romName, *romNameX, *romSize, *romCrc, *romSha1, *romSha1X, *romData;
		if (!XMLMatchTag(p, pEnd, "rom", 3, "name", &romName, &romNameX, "size", &romSize, NULL, "crc", &romCrc, NULL, "sha1", &romSha1, &romSha1X, "data", &romData, NULL, NULL)) continue;

		const char *missField = (!romName ? "name" : !romSize ? "size" : !romCrc ? "crc" : (!romSha1 || (romSha1X - romSha1) != 40) ? "sha1" : NULL);
		if (missField) { char ce = *pEnd; *pEnd = '\0'; if (!strstr(p, "status=\"nodump\"")) LogErr("<%s> element missing '%s' field!\n", "rom", missField); *pEnd = ce; haveSizeMatches = 0; break; }
		Bit64u size = atoi64(romSize);
		needRoms++;
		if (size < 7 || size == 43008 || romData) goto potentialMatch; // can auto generate
		for (SFile* fil : files) if (fil->size == size) goto potentialMatch;
		if (x == XML_ELEM_START) generatable++;
		continue;
		potentialMatch:
		haveSizeMatches++;
	}
	if (p != pGameInner && pGameEn) *pGameEn = p;
	if (!forceTry)
	{
		if (!needRoms || (haveSizeMatches + generatable) < (1 + needRoms * 2 / 3)) return false;
		if (generatable)
		{
			for (p = pGameInner; p && (x = XMLParse(p, pEnd)) != XML_END && x != XML_ELEM_END && (pNext = XMLLevel(pEnd, x)) != NULL; p = pNext)
			{
				char *romSize;
				if (x != XML_ELEM_START || !XMLMatchTag(p, pEnd, "rom", 3, "size", &romSize, NULL, NULL)) continue;
				while (*pEnd && *pEnd != '<') { pEnd++; } if (!*pEnd) break; // skip whitespace to first child tag
				if (pEnd[1] == 't') // <track> tag
				{
					if (SFileIso::CanPotentiallyBuildCHD(files, pEnd, atoi64(romSize))) haveSizeMatches++;
				}
				else if (pEnd[1] == 'p') // <patch> tag
				{
					if (SFileMemory::CanPotentiallyBuildPatched(files, pEnd)) haveSizeMatches++;
				}
				else if (pEnd[1] == 's') // <source> tag
				{
					if (SFileIso::CanPotentiallyBuildBINOGG(files, pEnd, atoi64(romSize))) haveSizeMatches += 2; // count as 2 to include potential for .CUE to be generated
				}
			}
			if (haveSizeMatches < (1 + needRoms * 2 / 3)) return false;
		}
	}

	XMLInlineStringConvert(gameName, gameNameX);
	workPath.assign(outBase).append(gameName, gameNameX - gameName);
	if (workPath.length() < 5 || ((&workPath.back())[-3] != '.' && (&workPath.back())[-4] != '.')) workPath.append(".zip");
	if (!isFix && verifyExisting && stat_utf8(workPath.c_str()))
	{
		if (VerifyGame(pGameInner, gameName, gameNameX, outBase, workPath, true)) return true;
		Log("  Game failed to verify or fix, run with -r to force rebuilding games\n");
		return false;
	}
	if (isFix) workPath.append(".fix");
	const char *outPath = workPath.c_str(), *ext3, *ext4; size_t outPathLen = workPath.length();
	PathGetExt(outPath, outPathLen - (isFix ? 4 : 0), ext3, ext4);

	if (!isFix && logPartialMatch) Log("Trying to build %.*s, finding matches for %u files ...\n", (int)(gameNameX - gameName), gameName, needRoms);
	if (!needRoms) { Log("  Done! Not building game with no files\n\n"); return true; }
	std::vector<SFile*> gameFiles;
	gameFiles.resize(needRoms); // all NULL

	// First match files by size and content
	Bit32u r, matches = 0;
	bool closeInfoSection = false;
	for (r = 0, p = pGameInner; p && (x = XMLParse(p, pEnd)) != XML_END && x != XML_ELEM_END && (pNext = XMLLevel(pEnd, x, &textStart, &textEnd)) != NULL; p = pNext)
	{
		char *romName, *romNameX, *romSize, *romCrc, *romSha1, *romData, *romDataX;
		if (!XMLMatchTag(p, pEnd, "rom", 3, "name", &romName, &romNameX, "size", &romSize, NULL, "crc", &romCrc, NULL, "sha1", &romSha1, NULL, "data", &romData, &romDataX, NULL))
		{
			char *linkType, *linkTypeX;
			if (forceTry && !isFix && (XMLMatchTag(p, pEnd, "link", 4, "type", &linkType, &linkTypeX, NULL) || XMLMatchTag(p, pEnd, "comment", 7, NULL)))
			{
				XMLInlineStringConvert(textStart, textEnd);
				if (!closeInfoSection) { Log("  ----------------------------------------------------------------------------------\n"); closeInfoSection = true; };
				if (p[1] == 'c') { Log("  Comment: %.*s\n", (int)(textEnd - textStart), textStart); }
				else { Log("  Link [%.*s]: %.*s\n", (int)(linkTypeX - linkType), linkType, (int)(textEnd - textStart), textStart); }
			}
			continue;
		}

		if (!r && closeInfoSection) Log("  ----------------------------------------------------------------------------------\n");
		r++; //make sure to increment r before continue
		Bit64u size = atoi64(romSize);
		if (!size && (romNameX[-1] == '/' || romNameX[-1] == '\\')) { matches++; continue; } // directory
		if (size > (Bit64u)0xFFFFFFFF) { LogErr("  ERROR: Rom [%.*s] file size exceeds 4GB\n", (int)(romNameX - romName), romName); continue; }

		SFile* romFile = NULL;
		for (SFile* fi : files)
		{
			if (fi->size != size || fi->IsContainedBy(outPath, outPathLen) || fi->GetCRC32() != (Bit32u)atoi64(romCrc, 0x10)) continue;
			if (!size && (fi->path.back() == '\\' || fi->path.back() == '/')) continue; // don't assign directory to empty files
			Bit8u romSha1b[20];
			if (!fi->GetSHA1() || !hextouint8(romSha1, romSha1b, 20) || memcmp(fi->sha1, romSha1b, 20)) continue;
			if (useSrcDates)
			{
				XMLInlineStringConvert(romName, romNameX);
				size_t romNameLen = (size_t)(romNameX - romName), filMatch = fi->PathMatch(romName, romNameLen);
				if (romNameLen > filMatch) // not yet a full match
				{
					if (!romFile || filMatch > romFile->PathMatch(romName, romNameLen)) romFile = fi; // but a better match
					continue; // continue search
				}
			}
			romFile = fi;
			break;
		}
		if (!romFile) // attempt to generate simple files
		{
			Bit8u romSha1b[20], verify = 0;
			static const unsigned char emptyDataBinComp[] = "\355\331\305A\4\61\0\5\320\37.#7\354\214T0\324\0\5\320\177\61\254\260\356\212\356{\23\237\344\32\r\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\204\362\372\326u/%\217'\312\330\375$\333\241\f\302\60\246\256\323\346S{\223\251\333\f<\347.\237\356Rg\240\316{>]M\306?~\37\350\226\344\210\206\22\200_\241\67^\377\1\200\313Qr\367\231\2\0\227\243d\340n\224\1\0\27a\367\33\373\356\36%\0\300\237\322\7";
			static const size_t emptyDataBinSize = 43008, emptyDataBinCompSize = sizeof(emptyDataBinComp) - 1; //exclude string null terminator

			// If the file is less than 7 bytes we can just generate it
			if      (size < 7 && hextouint8(romSha1, romSha1b, 20) && (romFile = SFileMemory::BuildFromCRC(size, (Bit32u)atoi64(romCrc, 0x10), romSha1b)) != NULL) {}
			// If the XML has the file content encoded in Base64, use that
			else if (romData && (romFile = new SFileMemory(romData, (size_t)(romDataX - romData))) != NULL) verify = 1;
			// See if this is the known embedded empty data bin file
			else if (size == 43008 && !strncasecmp(romSha1, "8a2846aac1e2ceb8a08a9cd5591e9a85228d5cab", 40) && (romFile = SFileZip::BuildDeflated(emptyDataBinComp, emptyDataBinCompSize, emptyDataBinSize)) != NULL) {}
			// See if this is a CUE file we can perhaps generate out of the rom listing
			else if (!strncasecmp(romNameX - 4, ".CUE", 4) && (romFile = (XMLInlineStringConvert(romName, romNameX), SFileIso::BuildCUE(romName, romNameX, pGameInner, size))) != NULL) verify = 1;
			// Skip failing this file for now if it might be generatable in the next step (count generatable again, it might have not been counted yet due to matching file size)
			else if (x == XML_ELEM_START) { generatable++; continue; }

			if (romFile) gameFiles.push_back(romFile); // remember to delete during cleanup
			if (verify && (romFile->size != size || !romFile->GetSHA1() || !hextouint8(romSha1, romSha1b, 20) || memcmp(romFile->sha1, romSha1b, 20))) romFile = NULL;
		}
		if (romFile) { gameFiles[r-1] = romFile; matches++; continue; }
		if (logPartialMatch) { XMLInlineStringConvert(romName, romNameX); Log("  Failed to find a match for [%.*s]!\n", (int)(romNameX - romName), romName); generatable = 0; }
	}

	// If needed, generate files not yet matched
	for (r = 0, p = pGameInner; matches != needRoms && matches >= r && p && (x = XMLParse(p, pEnd)) != XML_END && x != XML_ELEM_END && (pNext = XMLLevel(pEnd, x, &textStart, &textEnd)) != NULL; p = pNext)
	{
		char *romName, *romNameX, *romSize, *romCrc, *romSha1;
		if (!XMLMatchTag(p, pEnd, "rom", 3, "name", &romName, &romNameX, "size", &romSize, NULL, "crc", &romCrc, NULL, "sha1", &romSha1, NULL, NULL)) continue;
		if (gameFiles[r++] || x != XML_ELEM_START) continue; // make sure to increment r before continue, skip already matched and entries without inner elements in this step
		Bit64u size = atoi64(romSize);
		if ((!size && (romNameX[-1] == '/' || romNameX[-1] == '\\')) || size > (Bit64u)0xFFFFFFFF) continue; // directory or invalid size
		if (!generatable) { if (logPartialMatch) { XMLInlineStringConvert(romName, romNameX); Log("  Have missing files, skip attempt to generate [%.*s]!\n", (int)(romNameX - romName), romName); } continue; }
		SFile* romFile = NULL;

		// See if this is a file we perhaps can build with an embedded patch
		if      ((romFile = SFileMemory::BuildPatched(files, pEnd, size, romSha1)) != NULL) {}
		// See if this is a CHD image we perhaps can build out of ISO/CUE/BIN file(s)
		else if ((romFile = SFileIso::BuildCHD(files, pEnd, size, romSha1)) != NULL) {}
		// See if this is a BIN/OGG file we perhaps can build out of a CHD/ISO/BIN file
		else if ((romFile = SFileIso::BuildBINOGG(files, pEnd, size, romSha1)) != NULL) {}
		// Give up generating files
		else generatable = 0;

		if (romFile) gameFiles.push_back(romFile); // remember to delete during cleanup
		if (romFile) { gameFiles[r-1] = romFile; matches++; continue; }
		if (logPartialMatch) { XMLInlineStringConvert(romName, romNameX); Log("  Failed to find a match for [%.*s]!\n", (int)(romNameX - romName), romName); }
	}

	bool res = (matches == needRoms);
	if (!res) { if (logPartialMatch) Log("  Unable to build %.*s\n\n", (int)(gameNameX - gameName), gameName); }
	else
	{
		if (!isFix) Log("  Writing output %s ...\n", outPath);
		SFile::Writer *w = (SFileIso::UsesExtension(ext3, true) ? (SFile::Writer*)new SFileIso::IsoWriter(outPath, ext3) : new SFileZip::ZipWriter(outPath));
		if (w->failed) LogErr("  ERROR: Could not open output file %s\n\n", outPath);
		for (r = 0, p = pGameInner; !w->failed && p && (x = XMLParse(p, pEnd)) != XML_END && x != XML_ELEM_END && (pNext = XMLLevel(pEnd, x)) != NULL; p = pNext)
		{
			char *romName, *romNameX, *romSize, *romCrc, *romSha1, *romDate, *romDateX;
			if (!XMLMatchTag(p, pEnd, "rom", 3, "name", &romName, &romNameX, "size", &romSize, NULL, "crc", &romCrc, NULL, "sha1", &romSha1, NULL, "date", &romDate, &romDateX, NULL)) continue;

			SFile* romFile = gameFiles[r++]; //make sure to increment r before continue
			Bit16u zdate = 0, ztime = 0;
			if (useSrcDates && romFile && (romFile->date != (Bit16u)-1 || romFile->time != (Bit16u)-1))
			{
				// use dates in sources, ignoring the dates in the XML
				zdate = romFile->date;
				ztime = romFile->time;
			}
			else if (romDate)
			{
				*romDateX = '\0'; // temporarily null terminate
				int dYear, dMon, dDay, tHour, tMin, tSec;
				if (sscanf(romDate, "%04d-%02d-%02d %02d:%02d:%02d", &dYear, &dMon, &dDay, &tHour, &tMin, &tSec) == 6)
				{
					zdate = (Bit16u)(((dYear - 1980) << 9) | ((dMon & 0xf) << 5) | (dDay & 0x1f));
					ztime = (Bit16u)(((tHour & 0x1f) << 11) | ((tMin & 0x3f) << 5) | ((tSec & 0x3f) / 2));
				}
				*romDateX = romDate[-1]; // undo null terminate
			}

			Bit64u size = atoi64(romSize);
			ZIP_ASSERT(size == (romFile ? romFile->size : 0));
			XMLInlineStringConvert(romName, romNameX);
			if (!isFix) Log("    %sing [%s] as [%.*s]...\n", (romFile ? "Stor" : "Writ"), (romFile ? romFile->path.c_str() : ((romNameX[-1] == '/' || romNameX[-1] == '\\') ? "<DIRECTORY>" : "<EMPTY FILE>")), (int)(romNameX - romName), romName);
			w->WriteFile(romName, (size_t)(romNameX - romName), zdate, ztime, romFile, isFix);
		}
		if (!w->Finalize(pGameInner)) LogErr("  ERROR: Unknown error writing output file %s\n\n", outPath);
		else if (!isFix) Log("  Done! Successfully wrote %.*s with %u files!\n\n", (int)(gameNameX - gameName), gameName, needRoms);
		res = !w->failed;
		delete w;
	}
	for (size_t i = gameFiles.size(); i-- != needRoms;) delete gameFiles[i]; // delete generated CHDs
	return res;
}

static bool VerifyGame(char* pGameInner, char* gameName, char* gameNameX, const std::string& outBase, std::string& workPath, bool fixMode, bool crcOnlyCheck, char** pGameEn, bool* notFound)
{
	XMLInlineStringConvert(gameName, gameNameX);
	workPath.assign(outBase).append(gameName, gameNameX - gameName);
	if (workPath.length() < 5 || ((&workPath.back())[-3] != '.' && (&workPath.back())[-4] != '.')) workPath.append(".zip");
	SFileRaw gameFi(workPath, false);
	if (!gameFi.size) { if (notFound) *notFound = true; return false; }

	bool isISO = false;
	const char *gameFiPath = gameFi.path.c_str(), *ext3, *ext4;
	PathGetExt(gameFiPath, gameFi.path.length(), ext3, ext4);
	std::vector<SFile*> gameFiles;
	if (SFileIso::UsesExtension(ext3, true) && SFileIso::IndexFiles(gameFi, gameFiles)) isISO = true;
	else if (!SFileZip::IndexFiles(gameFi, gameFiles)) { LogErr("Invalid game file %s (not a ZIP file)\n", gameFiPath); return false; }

	Log("Verifying game %s ...\n", gameFiPath);
	unsigned romBasePathLen = (unsigned)gameFi.path.length() + 1, romTotal = 0, romCorrect = 0, romUnfixable = 0, romSuperflous = 0;
	char* p = pGameInner, *pEnd, *pNext;
	for (EXml x; p && (x = XMLParse(p, pEnd)) != XML_END && x != XML_ELEM_END && (pNext = XMLLevel(pEnd, x)) != NULL; p = pNext)
	{
		char *romName, *romNameX, *romSize, *romCrc, *romCrcX, *romSha1, *romSha1X, *romDate, *romDateX, *romData;
		if (!XMLMatchTag(p, pEnd, "rom", 3, "name", &romName, &romNameX, "size", &romSize, NULL, "crc", &romCrc, &romCrcX, "sha1", &romSha1, &romSha1X, "date", &romDate, &romDateX, "data", &romData, NULL, NULL)) continue;

		const char *missField = (!romName ? "name" : !romSize ? "size" : !romCrc ? "crc" : (!romSha1 || (romSha1X - romSha1) != 40) ? "sha1" : NULL);
		if (missField) { LogErr("<%s> element missing '%s' field!\n", "rom", missField); break; }

		SFile* matchFile = NULL;
		bool matchDate = false, matchTime = false, matchSize = false, matchCrc32 = false, matchSha1 = false, matchName = false;
		Bit64u size = atoi64(romSize);
		Bit16u zdate = 0, ztime = 0;
		Bit8u romSha1b[20];
		if (romDate)
		{
			*romDateX = '\0'; // temporarily null terminate
			int dYear, dMon, dDay, tHour, tMin, tSec;
			if (sscanf(romDate, "%04d-%02d-%02d %02d:%02d:%02d", &dYear, &dMon, &dDay, &tHour, &tMin, &tSec) == 6)
			{
				zdate = (Bit16u)(((dYear - 1980) << 9) | ((dMon & 0xf) << 5) | (dDay & 0x1f));
				ztime = (Bit16u)(((tHour & 0x1f) << 11) | ((tMin & 0x3f) << 5) | ((tSec & 0x3f) / 2));
			}
			*romDateX = romDate[-1]; // undo null terminate
		}
		XMLInlineStringConvert(romName, romNameX);
		for (SFile* fi : gameFiles)
		{
			if ((size_t)(romNameX - romName) != (size_t)(fi->path.length() - romBasePathLen)) continue;
			if (memcmp(romName, fi->path.c_str() + romBasePathLen, (romNameX - romName))) continue;
			matchName = fi->was_matched = true;
			matchFile = fi;
			matchDate = (zdate == fi->date);
			matchTime = (ztime == fi->time);
			if ((matchSize = (size == fi->size)) == false) break;
			if ((matchCrc32 = (fi->GetCRC32() == (Bit32u)atoi64(romCrc, 0x10))) == false) break;
			matchSha1 = (crcOnlyCheck || (fi->GetSHA1() && hextouint8(romSha1, romSha1b, 20) && !memcmp(fi->sha1, romSha1b, 20)));
			break;
		}

		if (!matchFile && size)
			for (SFile* fi : gameFiles)
			{
				if ((matchSize = (size == fi->size)) == false) continue;
				if ((matchCrc32 = (fi->GetCRC32() == (Bit32u)atoi64(romCrc, 0x10))) == false) continue;
				if ((matchSha1 = (crcOnlyCheck || (fi->GetSHA1() && hextouint8(romSha1, romSha1b, 20) && !memcmp(fi->sha1, romSha1b, 20)))) == false) continue;
				fi->was_matched = true;
				matchFile = fi;
				matchDate = (zdate == fi->date);
				matchTime = (ztime == fi->time);
				break;
			}

		romTotal++;
		if (matchName && matchSha1 && matchDate && matchTime) { romCorrect++; continue; }
		if (!matchFile)
			Log("  Rom '%.*s' not found in game file\n", (int)(romNameX - romName), romName);
		else
		{
			if (!matchDate && !matchTime)
				Log("  Rom '%.*s' has mismatching date/time (have %04d-%02d-%02d %02d:%02d:%02d, need %04d-%02d-%02d %02d:%02d:%02d)\n", (int)(romNameX - romName), romName, ((matchFile->date >> 9) + 1980), ((matchFile->date >> 5) & 0xf), (matchFile->date & 0x1f), (matchFile->time >> 11), ((matchFile->time >> 5) & 0x3f), ((matchFile->time & 0x1f) * 2), ((zdate >> 9) + 1980), ((zdate >> 5) & 0xf), (zdate & 0x1f), (ztime >> 11), ((ztime >> 5) & 0x3f), ((ztime & 0x1f) * 2));
			else if (!matchDate)
				Log("  Rom '%.*s' has mismatching date (have %04d-%02d-%02d, need %04d-%02d-%02d)\n", (int)(romNameX - romName), romName, ((matchFile->date >> 9) + 1980), ((matchFile->date >> 5) & 0xf), (matchFile->date & 0x1f), ((zdate >> 9) + 1980), ((zdate >> 5) & 0xf), (zdate & 0x1f));
			else if (!matchTime)
				Log("  Rom '%.*s' has mismatching time (have %02d:%02d:%02d, need %02d:%02d:%02d)\n", (int)(romNameX - romName), romName, (matchFile->time >> 11), ((matchFile->time >> 5) & 0x3f), ((matchFile->time & 0x1f) * 2), (ztime >> 11), ((ztime >> 5) & 0x3f), ((ztime & 0x1f) * 2));

			if (!matchName)
				Log("  Rom '%.*s' has mismatching name ('%s')\n", (int)(romNameX - romName), romName, matchFile->path.c_str() + romBasePathLen);
			else if (!matchSize)
				Log("  Rom '%.*s' has mismatching size (have %u, need %u)\n", (int)(romNameX - romName), romName, (unsigned)matchFile->size, (unsigned)size);
			else if (!matchCrc32)
				Log("  Rom '%.*s' has mismatching content (have %08x, need %.*s)\n", (int)(romNameX - romName), romName, matchFile->GetCRC32(), (int)(romCrcX - romCrc), romCrc);
			else if (!matchSha1)
			{
				Log("  Rom '%.*s' has mismatching content (have ", (int)(romNameX - romName), romName);
				const Bit8u* sha1 = matchFile->GetSHA1();
				for (int n = 0; n != 20; n++) Log("%02x", (sha1 ? sha1[n] : 0));
				Log(", need %.*s)\n", (int)(romSha1X - romSha1), romSha1);
			}
		}
		if (!matchSha1 && size >= 7 && (size != 43008 || strncasecmp(romSha1, "8a2846aac1e2ceb8a08a9cd5591e9a85228d5cab", 40)) && !romData)
		{
			bool unfixable = true;
			for (SFile* fi : gameFiles)
				if (size == fi->size && fi->GetCRC32() == (Bit32u)atoi64(romCrc, 0x10) && fi->GetSHA1() && hextouint8(romSha1, romSha1b, 20) && !memcmp(fi->sha1, romSha1b, 20)) { unfixable = false; break; }
			if (unfixable) romUnfixable++;
		}
	}
	if (p != pGameInner && pGameEn) *pGameEn = p;

	for (SFile* fi : gameFiles)
	{
		// Check IsContainedBy to ignore auxiliary files like CUE sheet track binaries
		if (fi->was_matched || !fi->IsContainedBy(gameFiPath, gameFi.path.length()) || (isISO && SFileIso::ValidSuperflous(gameFiles, fi))) continue;
		Log("  Unnecessary rom '%.*s' exists in game file\n", (int)(fi->path.length() - romBasePathLen), fi->path.c_str() + romBasePathLen);
		romSuperflous++;
	}

	bool wasFixed = false;
	if (romCorrect == romTotal && !romSuperflous)
		Log("  [OK] Correctly matched all %u roms\n\n", romCorrect);
	else if (romUnfixable)
		Log("  [ERROR] Matched %u of %u roms - Automatic fix not available, there are %d missing roms%s\n\n", romCorrect, romTotal, romUnfixable, (strncasecmp((&gameFi.path.back()) - 3, ".ZIP", 4) ? "\n         Run with -r to rebuild from scratch or rename to .ZIP and run without -v / -f to rebuild game with additional source files" : ""));
	else if (!fixMode && romSuperflous)
		Log("  [ERROR] Matched %u of %u roms and there are %u unnecessary extra files%s\n\n", romCorrect, romTotal, romSuperflous, " - Run program with -f instead of -v to fix game");
	else if (!fixMode)
		Log("  [ERROR] Matched %u of %u roms%s\n\n", romCorrect, romTotal, " - Run program with -f instead of -v to fix game");
	else
	{
		Log("  Matched %u of %u roms - Rebuilding fixed game ...\n", romCorrect, romTotal);
		if ((wasFixed = BuildRom(pGameInner, gameName, gameNameX, outBase, workPath, gameFiles, true, true)) == true)
			Log("  [OK] Game has been fixed\n\n");
		else
			Log("  [ERROR] Error while building fixed game\n\n");
	}

	if (wasFixed)
	{
		// swap old and fix file
		gameFi.Close();
		unlink(gameFiPath);
		rename(workPath.assign(gameFi.path).append(".fix").c_str(), gameFiPath);
	}

	for (size_t i = gameFiles.size(); i--;) delete gameFiles[i]; // delete backwards to delete contained files before their container
	return ((romCorrect == romTotal && !romSuperflous) || wasFixed);
}

int main(int argc, char *argv[])
{
	const char *xmlPath = NULL, *srcPath = NULL, *outPath = NULL, *useSrcDates = NULL, *onlyFullMatch = NULL, *rebuild = NULL, *verifyMode = NULL, *fixMode = NULL, *crcOnlyCheck = NULL, *noQuitConfirm = NULL;
	for (int i = 1; i < argc; i++)
	{
		if ((argv[i][0] != '-' && argv[i][0] != '/') || !argv[i][1] || argv[i][2]) goto argerr;
		switch (argv[i][1])
		{
			case 'x': if (xmlPath || ++i == argc) goto argerr; xmlPath       = argv[i]; continue;
			case 's': if (srcPath || ++i == argc) goto argerr; srcPath       = argv[i]; continue;
			case 'o': if (outPath || ++i == argc) goto argerr; outPath       = argv[i]; continue;
			case 'd': if (useSrcDates           ) goto argerr; useSrcDates   = argv[i]; continue;
			case 'p': if (onlyFullMatch         ) goto argerr; onlyFullMatch = argv[i]; continue;
			case 'r': if (rebuild               ) goto argerr; rebuild       = argv[i]; continue;
			case 'v': if (verifyMode            ) goto argerr; verifyMode    = argv[i]; continue;
			case 'f': if (fixMode               ) goto argerr; fixMode       = argv[i]; continue;
			case 'c': if (crcOnlyCheck          ) goto argerr; crcOnlyCheck  = argv[i]; continue;
			case 'q': if (noQuitConfirm         ) goto argerr; noQuitConfirm = argv[i]; continue;
		}
		argerr: LogErr("Unknown command line option '%s'.\n\n", argv[i]); goto help;
	}
	if (!xmlPath)
	{
		help:
		LogErr("%s v%s - Command line options:\n"
			"  -x <PATH>  : Path to input XML file (or - to pass XML via stdin)\n"
			"  -s <PATH>  : Path to source file directory (defaults to XML file or current directory)\n"
			"  -o <PATH>  : Path to output file directory (defaults to XML file or current directory)\n"
			"  -d         : Use date/time stamps in source instead of XML\n"
			"  -p         : Don't report build failure with only a partial match\n"
			"  -r         : Force rebuild output files (otherwise validate existing)\n"
			"  -v         : Only verify existing files in output file directory\n"
			"  -f         : Fix meta data in existing files that fail verification\n"
			"  -c         : Use fast CRC only check for verification and fixing\n"
			"  -q         : Don't ask for pressing a key at the end\n"
			"\n", "DoDAT", "0.8");
		return 1;
	}

	bool useStdin = (!xmlPath || (xmlPath[0] == '-' && xmlPath[1] == '\0'));
	std::string xml;
	if (!noQuitConfirm) Log("Loading DAT XML from %s ...\n", (useStdin ? "<console input> (press CTRL+C to abort input)" : xmlPath));
	FILE* fXML = (useStdin ? stdin : fopen(xmlPath, "rb"));
	if (!fXML) { LogErr("Failed to open DAT XML %s\n\n", xmlPath); return 1; }
	if (!useStdin) { fseek_wrap(fXML, 0, SEEK_END); xml.reserve((size_t)ftell_wrap(fXML) + 1); fseek_wrap(fXML, 0, SEEK_SET); }

	char xmlreadbuf[2048];
	size_t readStep = (useStdin ? 1 : sizeof(xmlreadbuf));
	for (int rootTagOfs = 0, rootTagLen = 0, got = 0, ofs = 0;;)
	{
		if (ofs == got)
		{
			got = (int)fread(xmlreadbuf, 1, readStep, fXML);
			ofs = 0;
			if (got > 0) { if (useStdin) xml.reserve((xml.length()+65535)/32768*32768); xml.append(xmlreadbuf, got); }
		}
		int c = (ofs >= got ? 0 : xmlreadbuf[ofs++]);
		if (c == 0 || c == 4 || c == 23) // 4 is CTRL+D, 23 is CTRL+W
		{
			incompleteXml:
			LogErr("Received incomplete XML\n");
			return 1;
		}
		if (c != '>') continue;
		char *pXml = &xml[0], *pTag, *pTagEn;
		if (!rootTagLen)
		{
			EXml xmlRoot = XMLParse((pTag = pXml), pTagEn);
			if (xmlRoot == XML_END || pTagEn > pXml + xml.size() - (got - ofs)) continue;;
			if (xmlRoot == XML_ELEM_END || xmlRoot == XML_TEXT) goto incompleteXml;
			if (xmlRoot == XML_ELEM_SOLO) break;
			rootTagOfs = (int)(pTag + 1 - &xml[0]);
			while (pTag[rootTagLen+1] != '>' && pTag[rootTagLen+1] != ' ') rootTagLen++;
		}
		else if (!memcmp(pXml + xml.size() - 1 - (got - ofs) - rootTagLen, pXml + rootTagOfs, rootTagLen) && XMLLevel(pXml + rootTagOfs))
			{ xml.resize(xml.size() - (got - ofs) + 1); xml.back() = '\0'; break; } // force null terminate
	}
	fclose(fXML);

	const char *xmlPathEnd = xmlPath + (useStdin ? 0 : strlen(xmlPath));
	while (xmlPathEnd != xmlPath && *xmlPathEnd != '/' && *xmlPathEnd != '\\') xmlPathEnd--;

	std::string outBase, workPath;
	((outPath || xmlPathEnd == xmlPath) ? outBase.assign(outPath ? outPath : ".") : outBase.assign(xmlPath, (xmlPathEnd - xmlPath))) += '/';

	if (verifyMode || fixMode)
	{
		Log("%sing games in output path %s%s...\n\n", (fixMode ? "Fix" : "Verify"), (outPath ? outPath : ""), (crcOnlyCheck ? " (quick CRC32 only check)" : " (full SHA1 data verification)"));

		EXml x;
		char *firstGameName = NULL, *firstGameNameX = NULL;
		bool haveMultipleGames = false, notFound = false;
		for  (char* pGame = &xml[0], *pGameEn = NULL; (x = XMLParse(pGame, pGameEn)) != XML_END; pGame = pGameEn)
		{
			char *gameName, *gameNameX;
			if (x == XML_TEXT || x == XML_ELEM_END || !XMLMatchTag(pGame, pGameEn, (pGame[1] == 'g' ? "game" : "machine"), (pGame[1] == 'g' ? 4 : 7), "name", &gameName, &gameNameX, NULL) || x == XML_ELEM_SOLO) continue;
			if (!haveMultipleGames) { if (!firstGameName) { firstGameName = gameName; firstGameNameX = gameNameX; } else { haveMultipleGames = true; } }

			VerifyGame(pGameEn, gameName, gameNameX, outBase, workPath, !!fixMode, !!crcOnlyCheck, &pGameEn, &notFound);
		}
		if (!haveMultipleGames && firstGameName && notFound) 
			Log("Failed to locate %.*s to %s!\n\n", (int)(firstGameNameX - firstGameName), firstGameName, (fixMode ? "fix" : "verify"));
	}
	else
	{
		std::string sourcePathTmp;
		if (!srcPath) srcPath = (xmlPathEnd == xmlPath ? "." : sourcePathTmp.assign(xmlPath, xmlPathEnd - xmlPath).c_str());

		Log("Indexing available files in source path %s...\n", (srcPath ? srcPath : ""));
		std::vector<SFile*> files;
		SFileRaw::IndexFiles(srcPath, files);
		for (size_t i = 0, numFiles = files.size(); i != numFiles; i++)
		{
			SFile& fil = *files[i];
			const char *ext3, *ext4;
			PathGetExt(fil.path.c_str(), fil.path.length(), ext3, ext4);
			if      (SFileZip::UsesExtension(ext3, ext4, false) &&  SFileZip::IndexFiles(fil, files)) {}
			else if (SFileIso::UsesExtension(ext3, false) &&        SFileIso::IndexFiles(fil, files)) {}
			else if (SFileFat::UsesExtension(ext3) &&               SFileFat::IndexFiles(fil, files)) {}
			else continue;
			numFiles = files.size();
		}
		//for (const SFile* fil : files) Log(" - %s (size=\"%u\" date=\"%04d-%02d-%02d %02d:%02d:%02d\")\n", fil->path.c_str(), (unsigned)fil->size, ((fil->date >> 9) + 1980), ((fil->date >> 5) & 0xf), (fil->date & 0x1f), (fil->time >> 11), ((fil->time >> 5) & 0x3f), ((fil->time & 0x1f) * 2));return 0;
		Log("Finished indexing available files\n\n");

		#if /* Write all files we found into a ZIP */ 0
		SFileZip::ZipWriter allz(sourcePathTmp.assign(xmlPath).append(".allsources.dosz").c_str());
		for (SFile* fil : files)
			if (strncasecmp(fil->path.c_str()+fil->path.length()-4, ".zip", 4) && strncasecmp(fil->path.c_str()+fil->path.length()-5, ".dosz", 5) && strncasecmp(fil->path.c_str()+fil->path.length()-4, ".bin", 4))
				allz.WriteFile(fil->path.c_str(), fil->path.length(), fil->date, fil->time, fil, false);
		allz.Finalize(NULL);
		return 1;
		#endif

		EXml x;
		bool firstGame = true, onlyOneGame = false, bUseSrcDates = !!useSrcDates, bLogPartialMatch = !onlyFullMatch, verifyExisting = !rebuild;
		for (char* pGame = &xml[0], *pGameEn = NULL; (x = XMLParse(pGame, pGameEn)) != XML_END; pGame = pGameEn)
		{
			char *gameName, *gameNameX;
			if (x == XML_TEXT || x == XML_ELEM_END || !XMLMatchTag(pGame, pGameEn, (pGame[1] == 'g' ? "game" : "machine"), (pGame[1] == 'g' ? 4 : 7), "name", &gameName, &gameNameX, NULL) || x == XML_ELEM_SOLO) continue;

			if (firstGame)
			{
				firstGame = false;
				onlyOneGame = !strstr(pGameEn, "<game ") && !strstr(pGameEn, "<machine ");
			}
			BuildRom(pGameEn, gameName, gameNameX, outBase, workPath, files, false, onlyOneGame, bUseSrcDates, bLogPartialMatch, verifyExisting, &pGameEn);
			if (pGameEn[0] != '<' || pGameEn[1] != '/' || pGameEn[2] != pGame[1] || pGameEn[3] != pGame[2]) { LogErr("Invalid XML near\n----------------------------\n%.*s\n----------------------------\n%.*s\n----------------------------\n", 200, pGame, 200, pGameEn); break; }
		}

		for (size_t i = files.size(); i--;) delete files[i]; // delete backwards to delete contained files before their container
	}

	if (!noQuitConfirm) { Log("Finished. Press enter to exit\n"); fgetc(stdin); }
	else Log("Finished.\n");

	return 0;
}

struct mz_inflate
{
	// BASED ON MINIZ
	// miniz.c v1.15 - public domain deflate
	// Rich Geldreich <richgel99@gmail.com>, last updated Oct. 13, 2013

	// Set MINIZ_HAS_64BIT_REGISTERS to 1 if operations on 64-bit integers are reasonably fast (and don't involve compiler generated calls to helper functions).
	#if defined(_M_X64) || defined(_WIN64) || defined(__MINGW64__) || defined(_LP64) || defined(__LP64__) || defined(__ia64__) || defined(__x86_64__)
	#define MINIZ_HAS_64BIT_REGISTERS 1
	#endif

	enum
	{
		// Decompression flags used by tinfl_decompress().
		TINFL_FLAG_HAS_MORE_INPUT = 2,                // If set, there are more input bytes available beyond the end of the supplied input buffer. If clear, the input buffer contains all remaining input.
		TINFL_FLAG_USING_NON_WRAPPING_OUTPUT_BUF = 4, // If set, the output buffer is large enough to hold the entire decompressed stream. If clear, the output buffer is at least the size of the dictionary (typically 32KB).

		// Max size of read buffer.
		MZ_ZIP_MAX_IO_BUF_SIZE = 16*1024, // Was 64*1024 originally (though max size readable through DOS_File would be 0xFFFF).

		// Max size of LZ dictionary (output buffer).
		TINFL_LZ_DICT_SIZE = 32*1024, // fixed for zip

		// Internal/private bits follow.
		TINFL_MAX_HUFF_TABLES = 3, TINFL_MAX_HUFF_SYMBOLS_0 = 288, TINFL_MAX_HUFF_SYMBOLS_1 = 32, TINFL_MAX_HUFF_SYMBOLS_2 = 19,
		TINFL_FAST_LOOKUP_BITS = 10, TINFL_FAST_LOOKUP_SIZE = 1 << TINFL_FAST_LOOKUP_BITS,

		// Number coroutine states consecutively
		TINFL_STATE_INDEX_BLOCK_BOUNDRY = 1,
		TINFL_STATE_3 , TINFL_STATE_5 , TINFL_STATE_6 , TINFL_STATE_7 , TINFL_STATE_51, TINFL_STATE_52,
		TINFL_STATE_9 , TINFL_STATE_38, TINFL_STATE_11, TINFL_STATE_14, TINFL_STATE_16, TINFL_STATE_18,
		TINFL_STATE_23, TINFL_STATE_24, TINFL_STATE_25, TINFL_STATE_26, TINFL_STATE_27, TINFL_STATE_53,
		TINFL_STATE_END
	};

	// Return status.
	enum tinfl_status
	{
		TINFL_STATUS_BAD_PARAM = -3,
		TINFL_STATUS_FAILED = -1,
		TINFL_STATUS_DONE = 0,
		TINFL_STATUS_NEEDS_MORE_INPUT = 1,
		TINFL_STATUS_HAS_MORE_OUTPUT = 2,
	};

	#if MINIZ_HAS_64BIT_REGISTERS
	typedef Bit64u tinfl_bit_buf_t;
	#else
	typedef Bit32u tinfl_bit_buf_t;
	#endif

	struct tinfl_huff_table
	{
		Bit16s m_look_up[TINFL_FAST_LOOKUP_SIZE];
		Bit16s m_tree[TINFL_MAX_HUFF_SYMBOLS_0 * 2];
		Bit8u m_code_size[TINFL_MAX_HUFF_SYMBOLS_0];
	};

	struct tinfl_decompressor
	{
		tinfl_huff_table m_tables[TINFL_MAX_HUFF_TABLES];
		Bit32u m_state, m_num_bits, m_final, m_type, m_dist, m_counter, m_num_extra, m_table_sizes[TINFL_MAX_HUFF_TABLES];
		tinfl_bit_buf_t m_bit_buf;
		size_t m_dist_from_out_buf_start;
		Bit8u m_raw_header[4], m_len_codes[TINFL_MAX_HUFF_SYMBOLS_0 + TINFL_MAX_HUFF_SYMBOLS_1 + 137];
	};

	// Initializes the decompressor to its initial state.
	static void tinfl_init(tinfl_decompressor *r) { r->m_state = 0; }

	// Main low-level decompressor coroutine function. This is the only function actually needed for decompression. All the other functions are just high-level helpers for improved usability.
	// This is a universal API, i.e. it can be used as a building block to build any desired higher level decompression API. In the limit case, it can be called once per every byte input or output.
	static tinfl_status tinfl_decompress(tinfl_decompressor *r, const Bit8u *pIn_buf_next, Bit32u *pIn_buf_size, Bit8u *pOut_buf_start, Bit8u *pOut_buf_next, Bit32u *pOut_buf_size, const Bit32u decomp_flags)
	{
		// An attempt to work around MSVC's spammy "warning C4127: conditional expression is constant" message.
		#ifdef _MSC_VER
		#define TINFL_MACRO_END while (0, 0)
		#else
		#define TINFL_MACRO_END while (0)
		#endif

		#define TINFL_MEMCPY(d, s, l) memcpy(d, s, l)
		#define TINFL_MEMSET(p, c, l) memset(p, c, l)
		#define TINFL_CLEAR(obj) memset(&(obj), 0, sizeof(obj))

		#define TINFL_CR_BEGIN switch(r->m_state) { case 0:
		#define TINFL_CR_RETURN(state_index, result) do { status = result; r->m_state = state_index; goto common_exit; case state_index:; } TINFL_MACRO_END
		#define TINFL_CR_RETURN_FOREVER(state_index, result) do { status = result; r->m_state = TINFL_STATE_END; goto common_exit; } TINFL_MACRO_END
		#define TINFL_CR_FINISH }

		// TODO: If the caller has indicated that there's no more input, and we attempt to read beyond the input buf, then something is wrong with the input because the inflator never
		// reads ahead more than it needs to. Currently TINFL_GET_BYTE() pads the end of the stream with 0's in this scenario.
		#define TINFL_GET_BYTE(state_index, c) do { \
			if (pIn_buf_cur >= pIn_buf_end) { \
				for ( ; ; ) { \
					if (decomp_flags & TINFL_FLAG_HAS_MORE_INPUT) { \
						TINFL_CR_RETURN(state_index, TINFL_STATUS_NEEDS_MORE_INPUT); \
						if (pIn_buf_cur < pIn_buf_end) { \
							c = *pIn_buf_cur++; \
							break; \
						} \
					} else { \
						c = 0; \
						break; \
					} \
				} \
			} else c = *pIn_buf_cur++; } TINFL_MACRO_END

		#define TINFL_NEED_BITS(state_index, n) do { Bit32u c; TINFL_GET_BYTE(state_index, c); bit_buf |= (((tinfl_bit_buf_t)c) << num_bits); num_bits += 8; } while (num_bits < (Bit32u)(n))
		#define TINFL_SKIP_BITS(state_index, n) do { if (num_bits < (Bit32u)(n)) { TINFL_NEED_BITS(state_index, n); } bit_buf >>= (n); num_bits -= (n); } TINFL_MACRO_END
		#define TINFL_GET_BITS(state_index, b, n) do { if (num_bits < (Bit32u)(n)) { TINFL_NEED_BITS(state_index, n); } b = bit_buf & ((1 << (n)) - 1); bit_buf >>= (n); num_bits -= (n); } TINFL_MACRO_END

		// TINFL_HUFF_BITBUF_FILL() is only used rarely, when the number of bytes remaining in the input buffer falls below 2.
		// It reads just enough bytes from the input stream that are needed to decode the next Huffman code (and absolutely no more). It works by trying to fully decode a
		// Huffman code by using whatever bits are currently present in the bit buffer. If this fails, it reads another byte, and tries again until it succeeds or until the
		// bit buffer contains >=15 bits (deflate's max. Huffman code size).
		#define TINFL_HUFF_BITBUF_FILL(state_index, pHuff) \
			do { \
				temp = (pHuff)->m_look_up[bit_buf & (TINFL_FAST_LOOKUP_SIZE - 1)]; \
				if (temp >= 0) { \
					code_len = temp >> 9; \
					if ((code_len) && (num_bits >= code_len)) \
					break; \
				} else if (num_bits > TINFL_FAST_LOOKUP_BITS) { \
					 code_len = TINFL_FAST_LOOKUP_BITS; \
					 do { \
							temp = (pHuff)->m_tree[~temp + ((bit_buf >> code_len++) & 1)]; \
					 } while ((temp < 0) && (num_bits >= (code_len + 1))); if (temp >= 0) break; \
				} TINFL_GET_BYTE(state_index, c); bit_buf |= (((tinfl_bit_buf_t)c) << num_bits); num_bits += 8; \
			} while (num_bits < 15);

		// TINFL_HUFF_DECODE() decodes the next Huffman coded symbol. It's more complex than you would initially expect because the zlib API expects the decompressor to never read
		// beyond the final byte of the deflate stream. (In other words, when this macro wants to read another byte from the input, it REALLY needs another byte in order to fully
		// decode the next Huffman code.) Handling this properly is particularly important on raw deflate (non-zlib) streams, which aren't followed by a byte aligned adler-32.
		// The slow path is only executed at the very end of the input buffer.
		#define TINFL_HUFF_DECODE(state_index, sym, pHuff) do { \
			int temp; Bit32u code_len, c; \
			if (num_bits < 15) { \
				if ((pIn_buf_end - pIn_buf_cur) < 2) { \
					 TINFL_HUFF_BITBUF_FILL(state_index, pHuff); \
				} else { \
					 bit_buf |= (((tinfl_bit_buf_t)pIn_buf_cur[0]) << num_bits) | (((tinfl_bit_buf_t)pIn_buf_cur[1]) << (num_bits + 8)); pIn_buf_cur += 2; num_bits += 16; \
				} \
			} \
			if ((temp = (pHuff)->m_look_up[bit_buf & (TINFL_FAST_LOOKUP_SIZE - 1)]) >= 0) \
				code_len = temp >> 9, temp &= 511; \
			else { \
				code_len = TINFL_FAST_LOOKUP_BITS; do { temp = (pHuff)->m_tree[~temp + ((bit_buf >> code_len++) & 1)]; } while (temp < 0); \
			} sym = temp; bit_buf >>= code_len; num_bits -= code_len; } TINFL_MACRO_END

		static const int s_length_base[31] = { 3,4,5,6,7,8,9,10,11,13, 15,17,19,23,27,31,35,43,51,59, 67,83,99,115,131,163,195,227,258,0,0 };
		static const int s_length_extra[31]= { 0,0,0,0,0,0,0,0,1,1,1,1,2,2,2,2,3,3,3,3,4,4,4,4,5,5,5,5,0,0,0 };
		static const int s_dist_base[32] = { 1,2,3,4,5,7,9,13,17,25,33,49,65,97,129,193, 257,385,513,769,1025,1537,2049,3073,4097,6145,8193,12289,16385,24577,0,0};
		static const int s_dist_extra[32] = { 0,0,0,0,1,1,2,2,3,3,4,4,5,5,6,6,7,7,8,8,9,9,10,10,11,11,12,12,13,13};
		static const Bit8u s_length_dezigzag[19] = { 16,17,18,0,8,7,9,6,10,5,11,4,12,3,13,2,14,1,15 };
		static const int s_min_table_sizes[3] = { 257, 1, 4 };

		tinfl_status status = TINFL_STATUS_FAILED; Bit32u num_bits, dist, counter, num_extra; tinfl_bit_buf_t bit_buf;
		const Bit8u *pIn_buf_cur = pIn_buf_next, *const pIn_buf_end = pIn_buf_next + *pIn_buf_size, *const pIn_buf_end_m_4 = pIn_buf_end - 4;
		Bit8u *pOut_buf_cur = pOut_buf_next, *const pOut_buf_end = pOut_buf_next + *pOut_buf_size, *const pOut_buf_end_m_2 = pOut_buf_end - 2;
		size_t out_buf_size_mask = (decomp_flags & TINFL_FLAG_USING_NON_WRAPPING_OUTPUT_BUF) ? (size_t)-1 : ((pOut_buf_next - pOut_buf_start) + *pOut_buf_size) - 1, dist_from_out_buf_start;

		Bit16s* r_tables_0_look_up = r->m_tables[0].m_look_up;

		// Ensure the output buffer's size is a power of 2, unless the output buffer is large enough to hold the entire output file (in which case it doesn't matter).
		if (((out_buf_size_mask + 1) & out_buf_size_mask) || (pOut_buf_next < pOut_buf_start)) { *pIn_buf_size = *pOut_buf_size = 0; return TINFL_STATUS_BAD_PARAM; }

		num_bits = r->m_num_bits; bit_buf = r->m_bit_buf; dist = r->m_dist; counter = r->m_counter; num_extra = r->m_num_extra; dist_from_out_buf_start = r->m_dist_from_out_buf_start;
		TINFL_CR_BEGIN

		bit_buf = num_bits = dist = counter = num_extra = 0;

		do
		{
			if (pIn_buf_cur - pIn_buf_next) { TINFL_CR_RETURN(TINFL_STATE_INDEX_BLOCK_BOUNDRY, TINFL_STATUS_HAS_MORE_OUTPUT); }
			TINFL_GET_BITS(TINFL_STATE_3, r->m_final, 3); r->m_type = r->m_final >> 1;
			if (r->m_type == 0)
			{
				TINFL_SKIP_BITS(TINFL_STATE_5, num_bits & 7);
				for (counter = 0; counter < 4; ++counter) { if (num_bits) TINFL_GET_BITS(TINFL_STATE_6, r->m_raw_header[counter], 8); else TINFL_GET_BYTE(TINFL_STATE_7, r->m_raw_header[counter]); }
				if ((counter = (r->m_raw_header[0] | (r->m_raw_header[1] << 8))) != (Bit32u)(0xFFFF ^ (r->m_raw_header[2] | (r->m_raw_header[3] << 8)))) { TINFL_CR_RETURN_FOREVER(39, TINFL_STATUS_FAILED); }
				while ((counter) && (num_bits))
				{
					TINFL_GET_BITS(TINFL_STATE_51, dist, 8);
					while (pOut_buf_cur >= pOut_buf_end) { TINFL_CR_RETURN(TINFL_STATE_52, TINFL_STATUS_HAS_MORE_OUTPUT); }
					*pOut_buf_cur++ = (Bit8u)dist;
					counter--;
				}
				while (counter)
				{
					size_t n; while (pOut_buf_cur >= pOut_buf_end) { TINFL_CR_RETURN(TINFL_STATE_9, TINFL_STATUS_HAS_MORE_OUTPUT); }
					while (pIn_buf_cur >= pIn_buf_end)
					{
						if (decomp_flags & TINFL_FLAG_HAS_MORE_INPUT)
						{
							TINFL_CR_RETURN(TINFL_STATE_38, TINFL_STATUS_NEEDS_MORE_INPUT);
						}
						else
						{
							TINFL_CR_RETURN_FOREVER(40, TINFL_STATUS_FAILED);
						}
					}
					n = ZIP_MIN(ZIP_MIN((size_t)(pOut_buf_end - pOut_buf_cur), (size_t)(pIn_buf_end - pIn_buf_cur)), counter);
					TINFL_MEMCPY(pOut_buf_cur, pIn_buf_cur, n); pIn_buf_cur += n; pOut_buf_cur += n; counter -= (Bit32u)n;
				}
			}
			else if (r->m_type == 3)
			{
				TINFL_CR_RETURN_FOREVER(10, TINFL_STATUS_FAILED);
			}
			else
			{
				if (r->m_type == 1)
				{
					Bit8u *p = r->m_tables[0].m_code_size; Bit32u i;
					r->m_table_sizes[0] = 288; r->m_table_sizes[1] = 32; TINFL_MEMSET(r->m_tables[1].m_code_size, 5, 32);
					for (i = 0; i <= 143; ++i) { *p++ = 8; } for (; i <= 255; ++i) { *p++ = 9; } for (; i <= 279; ++i) { *p++ = 7; } for (; i <= 287; ++i) { *p++ = 8; }
				}
				else
				{
					for (counter = 0; counter < 3; counter++) { TINFL_GET_BITS(TINFL_STATE_11, r->m_table_sizes[counter], "\05\05\04"[counter]); r->m_table_sizes[counter] += s_min_table_sizes[counter]; }
					TINFL_CLEAR(r->m_tables[2].m_code_size); for (counter = 0; counter < r->m_table_sizes[2]; counter++) { Bit32u s; TINFL_GET_BITS(TINFL_STATE_14, s, 3); r->m_tables[2].m_code_size[s_length_dezigzag[counter]] = (Bit8u)s; }
					r->m_table_sizes[2] = 19;
				}
				for ( ; (int)r->m_type >= 0; r->m_type--)
				{
					int tree_next, tree_cur; tinfl_huff_table *pTable;
					Bit32u i, j, used_syms, total, sym_index, next_code[17], total_syms[16]; pTable = &r->m_tables[r->m_type]; TINFL_CLEAR(total_syms); TINFL_CLEAR(pTable->m_look_up); TINFL_CLEAR(pTable->m_tree);
					for (i = 0; i < r->m_table_sizes[r->m_type]; ++i) total_syms[pTable->m_code_size[i]]++;
					used_syms = 0, total = 0; next_code[0] = next_code[1] = 0;
					for (i = 1; i <= 15; ++i) { used_syms += total_syms[i]; next_code[i + 1] = (total = ((total + total_syms[i]) << 1)); }
					if ((65536 != total) && (used_syms > 1))
					{
						TINFL_CR_RETURN_FOREVER(35, TINFL_STATUS_FAILED);
					}
					for (tree_next = -1, sym_index = 0; sym_index < r->m_table_sizes[r->m_type]; ++sym_index)
					{
						Bit32u rev_code = 0, l, cur_code, code_size = pTable->m_code_size[sym_index]; if (!code_size) continue;
						cur_code = next_code[code_size]++; for (l = code_size; l > 0; l--, cur_code >>= 1) rev_code = (rev_code << 1) | (cur_code & 1);
						if (code_size <= TINFL_FAST_LOOKUP_BITS) { Bit16s k = (Bit16s)((code_size << 9) | sym_index); while (rev_code < TINFL_FAST_LOOKUP_SIZE) { pTable->m_look_up[rev_code] = k; rev_code += (1 << code_size); } continue; }
						if (0 == (tree_cur = pTable->m_look_up[rev_code & (TINFL_FAST_LOOKUP_SIZE - 1)])) { pTable->m_look_up[rev_code & (TINFL_FAST_LOOKUP_SIZE - 1)] = (Bit16s)tree_next; tree_cur = tree_next; tree_next -= 2; }
						rev_code >>= (TINFL_FAST_LOOKUP_BITS - 1);
						for (j = code_size; j > (TINFL_FAST_LOOKUP_BITS + 1); j--)
						{
							tree_cur -= ((rev_code >>= 1) & 1);
							if (!pTable->m_tree[-tree_cur - 1]) { pTable->m_tree[-tree_cur - 1] = (Bit16s)tree_next; tree_cur = tree_next; tree_next -= 2; } else tree_cur = pTable->m_tree[-tree_cur - 1];
						}
						tree_cur -= ((rev_code >>= 1) & 1); pTable->m_tree[-tree_cur - 1] = (Bit16s)sym_index;
					}
					if (r->m_type == 2)
					{
						for (counter = 0; counter < (r->m_table_sizes[0] + r->m_table_sizes[1]); )
						{
							Bit32u s; TINFL_HUFF_DECODE(TINFL_STATE_16, dist, &r->m_tables[2]); if (dist < 16) { r->m_len_codes[counter++] = (Bit8u)dist; continue; }
							if ((dist == 16) && (!counter))
							{
								TINFL_CR_RETURN_FOREVER(17, TINFL_STATUS_FAILED);
							}
							num_extra = "\02\03\07"[dist - 16]; TINFL_GET_BITS(TINFL_STATE_18, s, num_extra); s += "\03\03\013"[dist - 16];
							TINFL_MEMSET(r->m_len_codes + counter, (dist == 16) ? r->m_len_codes[counter - 1] : 0, s); counter += s;
						}
						if ((r->m_table_sizes[0] + r->m_table_sizes[1]) != counter)
						{
							TINFL_CR_RETURN_FOREVER(21, TINFL_STATUS_FAILED);
						}
						TINFL_MEMCPY(r->m_tables[0].m_code_size, r->m_len_codes, r->m_table_sizes[0]); TINFL_MEMCPY(r->m_tables[1].m_code_size, r->m_len_codes + r->m_table_sizes[0], r->m_table_sizes[1]);
					}
				}
				for ( ; ; )
				{
					Bit8u *pSrc;
					for ( ; ; )
					{
						if (((pIn_buf_end_m_4 < pIn_buf_cur)) || ((pOut_buf_end_m_2 < pOut_buf_cur)))
						{
							TINFL_HUFF_DECODE(TINFL_STATE_23, counter, &r->m_tables[0]);
							if (counter >= 256)
								break;
							while (pOut_buf_cur >= pOut_buf_end) { TINFL_CR_RETURN(TINFL_STATE_24, TINFL_STATUS_HAS_MORE_OUTPUT); }
							*pOut_buf_cur++ = (Bit8u)counter;
						}
						else
						{
							int sym2; Bit32u code_len;
							#if MINIZ_HAS_64BIT_REGISTERS
							if (num_bits < 30) { bit_buf |= (((tinfl_bit_buf_t)ZIP_READ_LE32(pIn_buf_cur)) << num_bits); pIn_buf_cur += 4; num_bits += 32; }
							#else
							if (num_bits < 15) { bit_buf |= (((tinfl_bit_buf_t)ZIP_READ_LE16(pIn_buf_cur)) << num_bits); pIn_buf_cur += 2; num_bits += 16; }
							#endif

							sym2 = r_tables_0_look_up[bit_buf & (TINFL_FAST_LOOKUP_SIZE - 1)];
							if (sym2 < 0)
							{
								code_len = TINFL_FAST_LOOKUP_BITS;
								do { sym2 = r->m_tables[0].m_tree[~sym2 + ((bit_buf >> code_len++) & 1)]; } while (sym2 < 0);
							}
							else
								code_len = sym2 >> 9;
							counter = sym2;
							bit_buf >>= code_len;
							num_bits -= code_len;
							if (counter & 256)
								break;

							#if !MINIZ_HAS_64BIT_REGISTERS
							if (num_bits < 15) { bit_buf |= (((tinfl_bit_buf_t)ZIP_READ_LE16(pIn_buf_cur)) << num_bits); pIn_buf_cur += 2; num_bits += 16; }
							#endif

							sym2 = r_tables_0_look_up[bit_buf & (TINFL_FAST_LOOKUP_SIZE - 1)];
							if (sym2 >= 0)
								code_len = sym2 >> 9;
							else
							{
								code_len = TINFL_FAST_LOOKUP_BITS;
								do { sym2 = r->m_tables[0].m_tree[~sym2 + ((bit_buf >> code_len++) & 1)]; } while (sym2 < 0);
							}
							bit_buf >>= code_len;
							num_bits -= code_len;

							pOut_buf_cur[0] = (Bit8u)counter;
							if (sym2 & 256)
							{
								pOut_buf_cur++;
								counter = sym2;
								break;
							}
							pOut_buf_cur[1] = (Bit8u)sym2;
							pOut_buf_cur += 2;
						}
					}
					if ((counter &= 511) == 256) break;

					num_extra = s_length_extra[counter - 257]; counter = s_length_base[counter - 257];
					if (num_extra) { Bit32u extra_bits; TINFL_GET_BITS(TINFL_STATE_25, extra_bits, num_extra); counter += extra_bits; }

					TINFL_HUFF_DECODE(TINFL_STATE_26, dist, &r->m_tables[1]);
					num_extra = s_dist_extra[dist]; dist = s_dist_base[dist];
					if (num_extra) { Bit32u extra_bits; TINFL_GET_BITS(TINFL_STATE_27, extra_bits, num_extra); dist += extra_bits; }

					dist_from_out_buf_start = pOut_buf_cur - pOut_buf_start;
					if ((dist > dist_from_out_buf_start) && (decomp_flags & TINFL_FLAG_USING_NON_WRAPPING_OUTPUT_BUF))
					{
						TINFL_CR_RETURN_FOREVER(37, TINFL_STATUS_FAILED);
					}

					pSrc = pOut_buf_start + ((dist_from_out_buf_start - dist) & out_buf_size_mask);

					if ((ZIP_MAX(pOut_buf_cur, pSrc) + counter) <= pOut_buf_end)
					{
						do
						{
							pOut_buf_cur[0] = pSrc[0];
							pOut_buf_cur[1] = pSrc[1];
							pOut_buf_cur[2] = pSrc[2];
							pOut_buf_cur += 3; pSrc += 3;
						} while ((int)(counter -= 3) > 2);
						if ((int)counter > 0)
						{
							*(pOut_buf_cur++) = pSrc[0];
							if (counter == 2)
								*(pOut_buf_cur++) = pSrc[1];
						}
					}
					else
					{
						while (counter--)
						{
							while (pOut_buf_cur >= pOut_buf_end) { TINFL_CR_RETURN(TINFL_STATE_53, TINFL_STATUS_HAS_MORE_OUTPUT); }
							*pOut_buf_cur++ = pOut_buf_start[(dist_from_out_buf_start++ - dist) & out_buf_size_mask];
						}
					}
				}
			}
		} while (!(r->m_final & 1));
		TINFL_CR_RETURN_FOREVER(34, TINFL_STATUS_DONE);
		TINFL_CR_FINISH

		common_exit:
		r->m_num_bits = num_bits; r->m_bit_buf = bit_buf; r->m_dist = dist; r->m_counter = counter; r->m_num_extra = num_extra; r->m_dist_from_out_buf_start = dist_from_out_buf_start;
		*pIn_buf_size = (Bit32u)(pIn_buf_cur - pIn_buf_next); *pOut_buf_size = (Bit32u)(pOut_buf_cur - pOut_buf_next);
		return status;

		#undef TINFL_MACRO_END
		#undef TINFL_MEMCPY
		#undef TINFL_MEMSET
		#undef TINFL_CR_BEGIN
		#undef TINFL_CR_RETURN
		#undef TINFL_CR_RETURN_FOREVER
		#undef TINFL_CR_FINISH
		#undef TINFL_GET_BYTE
		#undef TINFL_NEED_BITS
		#undef TINFL_SKIP_BITS
		#undef TINFL_GET_BITS
		#undef TINFL_HUFF_BITBUF_FILL
		#undef TINFL_HUFF_DECODE
	}
};

struct oz_unshrink
{
	// BASED ON OZUNSHRINK
	// Ozunshrink / Old ZIP Unshrink (ozunshrink.h) (public domain)
	// By Jason Summers - https://github.com/jsummers/oldunzip

	enum
	{
		OZ_ERRCODE_OK                  = 0,
		OZ_ERRCODE_GENERIC_ERROR       = 1,
		OZ_ERRCODE_BAD_CDATA           = 2,
		OZ_ERRCODE_READ_FAILED         = 6,
		OZ_ERRCODE_WRITE_FAILED        = 7,
		OZ_ERRCODE_INSUFFICIENT_CDATA  = 8,
	};

	Bit8u *out_start, *out_cur, *out_end;
	Bit8u *in_start, *in_cur, *in_end;

	// The code table (implements a dictionary)
	enum { OZ_VALBUFSIZE = 7936, OZ_NUM_CODES = 8192 };
	Bit8u valbuf[OZ_VALBUFSIZE]; // Max possible chain length (8192 - 257 + 1 = 7936)
	struct { Bit16u parent; Bit8u value; Bit8u flags; } ct[OZ_NUM_CODES];

	static int Run(oz_unshrink *oz)
	{
		enum { OZ_INITIAL_CODE_SIZE = 9, OZ_MAX_CODE_SIZE = 13, OZ_INVALID_CODE = 256 };
		Bit32u oz_bitreader_buf = 0;
		Bit8u  oz_bitreader_nbits_in_buf = 0;
		Bit8u  oz_curr_code_size = OZ_INITIAL_CODE_SIZE;
		Bit16u oz_oldcode = 0;
		Bit16u oz_highest_code_ever_used = 0;
		Bit16u oz_free_code_search_start = 257;
		Bit8u  oz_last_value = 0;
		bool   oz_have_oldcode = false;
		bool   oz_was_clear = false;

		memset(oz->ct, 0, sizeof(oz->ct));
		for (Bit16u i = 0; i < 256; i++)
		{
			// For entries <=256, .parent is always set to OZ_INVALID_CODE.
			oz->ct[i].parent = OZ_INVALID_CODE;
			oz->ct[i].value = (Bit8u)i;
		}
		for (Bit16u j = 256; j < OZ_NUM_CODES; j++)
		{
			// For entries >256, .parent==OZ_INVALID_CODE means code is unused
			oz->ct[j].parent = OZ_INVALID_CODE;
		}

		for (;;)
		{
			while (oz_bitreader_nbits_in_buf < oz_curr_code_size)
			{
				if (oz->in_cur >= oz->in_end) return OZ_ERRCODE_INSUFFICIENT_CDATA;
				Bit8u b = *(oz->in_cur++);
				oz_bitreader_buf |= ((Bit32u)b) << oz_bitreader_nbits_in_buf;
				oz_bitreader_nbits_in_buf += 8;
			}

			Bit16u code = (Bit16u)(oz_bitreader_buf & ((1U << oz_curr_code_size) - 1U));
			oz_bitreader_buf >>= oz_curr_code_size;
			oz_bitreader_nbits_in_buf -= oz_curr_code_size;

			if (code == 256)
			{
				oz_was_clear = true;
				continue;
			}

			if (oz_was_clear)
			{
				oz_was_clear = false;

				if (code == 1 && (oz_curr_code_size < OZ_MAX_CODE_SIZE))
				{
					oz_curr_code_size++;
					continue;
				}
				if (code != 2) return OZ_ERRCODE_BAD_CDATA;

				// partial clear
				Bit16u i;
				for (i = 257; i <= oz_highest_code_ever_used; i++)
				{
					if (oz->ct[i].parent != OZ_INVALID_CODE)
					{
						oz->ct[oz->ct[i].parent].flags = 1; // Mark codes that have a child
					}
				}

				for (i = 257; i <= oz_highest_code_ever_used; i++)
				{
					if (oz->ct[i].flags == 0)
					{
						oz->ct[i].parent = OZ_INVALID_CODE; // Clear this code
						oz->ct[i].value = 0;
					}
					else
					{
						oz->ct[i].flags = 0; // Leave all flags at 0, for next time.
					}
				}

				oz_free_code_search_start = 257;
				continue;
			}

			// Process a single (nonspecial) LZW code that was read from the input stream.
			if (code >= OZ_NUM_CODES) return OZ_ERRCODE_GENERIC_ERROR;

			Bit16u emit_code;
			bool late_add, code_is_in_table = (code < 256 || oz->ct[code].parent != OZ_INVALID_CODE);
			if      (!oz_have_oldcode) { late_add = false; goto OZ_EMIT_CODE;         } //emit only
			else if (code_is_in_table) { late_add =  true; goto OZ_EMIT_CODE;         } //emit, then add
			else                       { late_add = false; goto OZ_ADD_TO_DICTIONARY; } //add, then emit

			// Add a code to the dictionary.
			OZ_ADD_TO_DICTIONARY:
			Bit16u newpos, valbuf_pos;
			for (newpos = oz_free_code_search_start; ; newpos++)
			{
				if (newpos >= OZ_NUM_CODES) return OZ_ERRCODE_BAD_CDATA;
				if (oz->ct[newpos].parent == OZ_INVALID_CODE) break;
			}
			oz->ct[newpos].parent = oz_oldcode;
			oz->ct[newpos].value = oz_last_value;
			oz_free_code_search_start = newpos + 1;
			if (newpos > oz_highest_code_ever_used)
			{
				oz_highest_code_ever_used = newpos;
			}
			if (late_add) goto OZ_FINISH_PROCESS_CODE;

			// Decode an LZW code to one or more values, and write the values. Updates oz_last_value.
			OZ_EMIT_CODE:
			for (emit_code = code, valbuf_pos = OZ_VALBUFSIZE;;) // = First entry that's used
			{
				if (emit_code >= OZ_NUM_CODES) return OZ_ERRCODE_GENERIC_ERROR;

				// Check if infinite loop (probably an internal error).
				if (valbuf_pos == 0) return OZ_ERRCODE_GENERIC_ERROR;

				// valbuf is a stack, essentially. We fill it in the reverse direction, to make it simpler to write the final byte sequence.
				valbuf_pos--;

				if (emit_code >= 257 && oz->ct[emit_code].parent == OZ_INVALID_CODE)
				{
					oz->valbuf[valbuf_pos] = oz_last_value;
					emit_code = oz_oldcode;
					continue;
				}

				oz->valbuf[valbuf_pos] = oz->ct[emit_code].value;

				if (emit_code < 257)
				{
					oz_last_value = oz->ct[emit_code].value;

					// Write out the collected values.
					size_t n = OZ_VALBUFSIZE - valbuf_pos;
					if (oz->out_cur + n > oz->out_end) return OZ_ERRCODE_WRITE_FAILED;
					memcpy(oz->out_cur, &oz->valbuf[valbuf_pos], n);
					oz->out_cur += n;
					if (oz->out_cur == oz->out_end) return OZ_ERRCODE_OK;

					break;
				}

				// Traverse the tree, back toward the root codes.
				emit_code = oz->ct[emit_code].parent;
			}
			if (late_add) goto OZ_ADD_TO_DICTIONARY;

			if (!oz_have_oldcode)
			{
				oz_have_oldcode = true;
				oz_last_value = (Bit8u)code;
			}

			OZ_FINISH_PROCESS_CODE:
			oz_oldcode = code;
		}
	}
};

struct unz_explode
{
	// BASED ON INFO-ZIP UNZIP
	// Info-ZIP UnZip v5.4 (explode.c and inflate.c)
	// Put in the public domain by Mark Adler

	enum
	{
		UNZ_ERRCODE_OK                  = 0,
		UNZ_ERRCODE_INCOMPLETE_SET      = 1,
		UNZ_ERRCODE_INVALID_TABLE_INPUT = 2,
		UNZ_ERRCODE_OUTOFMEMORY         = 3,
		UNZ_ERRCODE_INVALID_TREE_INPUT  = 4,
		UNZ_ERRCODE_INTERNAL_ERROR      = 5,
		UNZ_ERRCODE_OUTPUT_ERROR        = 6,
	};

	Bit8u *out_start, *out_cur, *out_end;
	Bit8u *in_start, *in_cur, *in_end;

	enum { WSIZE = 0x8000 }; // window size--must be a power of two
	Bit8u slide[WSIZE];

	static Bit8u GetByte(unz_explode* exploder)
	{
		return (exploder->in_cur < exploder->in_end ? *(exploder->in_cur++) : 0);
	}

	struct huft
	{
		// number of extra bits or operation, number of bits in this code or subcode
		Bit8u e, b;
		// literal, length base, or distance base || pointer to next level of table
		union { Bit16u n; huft *t; } v;
	};

	static void huft_free(huft *t)
	{
		for (huft *p = t, *q; p != (huft *)NULL; p = q)
		{
			q = (--p)->v.t;
			free(p);
		}
	}

	static int get_tree_build_huft(unz_explode* exploder, Bit32u *b, Bit32u n, Bit32u s, const Bit16u *d, const Bit16u *e, huft **t, int *m)
	{
		// Get the bit lengths for a code representation from the compressed stream.
		// If get_tree() returns 4, then there is an error in the data
		Bit32u bytes_remain;    // bytes remaining in list
		Bit32u lengths_entered; // lengths entered
		Bit32u ncodes;  // number of codes
		Bit32u bitlen; // bit length for those codes

		// get bit lengths
		bytes_remain = (Bit32u)GetByte(exploder) + 1; // length/count pairs to read
		lengths_entered = 0; // next code
		do
		{
			bitlen = ((ncodes = (Bit32u)GetByte(exploder)) & 0xf) + 1; //bits in code (1..16)
			ncodes = ((ncodes & 0xf0) >> 4) + 1; // codes with those bits (1..16)
			if (lengths_entered + ncodes > n) return UNZ_ERRCODE_INVALID_TREE_INPUT; // don't overflow bit_lengths
			do
			{
				b[lengths_entered++] = bitlen;
			} while (--ncodes);
		} while (--bytes_remain);
		if (lengths_entered != n) return UNZ_ERRCODE_INVALID_TREE_INPUT;

		// Mystery code, the original (huft_build function) wasn't much more readable IMHO (see inflate.c)
		// Given a list of code lengths and a maximum table size, make a set of tables to decode that set of codes.  Return zero on success, one if
		// the given code set is incomplete (the tables are still built in this case), two if the input is invalid (all zero length codes or an
		// oversubscribed set of lengths), and three if not enough memory.
		enum { BMAX = 16, N_MAX = 288 }; Bit32u a, c[BMAX + 1], f, i, j, *p, v[N_MAX], x[BMAX + 1], *xp, z; int g, h, k, l, w, y; huft *q, r, *u[BMAX];
		memset(c, 0, sizeof(c)); p = b; i = n; do { c[*p++]++; } while (--i); if (c[0] == n) { *t = (huft *)NULL; *m = 0; return UNZ_ERRCODE_OK; }
		l = *m; for (j = 1; j <= BMAX; j++) if (c[j]) break; k = j; if ((Bit32u)l < j) l = j; for (i = BMAX; i; i--) if (c[i]) break;
		g = i; if ((Bit32u)l > i) l = i; *m = l; for (y = 1 << j; j < i; j++, y <<= 1) if ((y -= c[j]) < 0) return UNZ_ERRCODE_INVALID_TABLE_INPUT;
		if ((y -= c[i]) < 0) { return UNZ_ERRCODE_INVALID_TABLE_INPUT; } c[i] += y; x[1] = j = 0; p = c + 1; xp = x + 2; while (--i) { *xp++ = (j += *p++); }
		p = b; i = 0; do { if ((j = *p++) != 0) v[x[j]++] = i; } while (++i < n); x[0] = i = 0; p = v; h = -1; w = -l;
		u[0] = (huft *)NULL; q = (huft *)NULL; z = 0; for (; k <= g; k++) { a = c[k]; while (a--) { while (k > w + l)
		{ h++; w += l; z = (z = g - w) > (Bit32u)l ? l : z; if ((f = 1 << (j = k - w)) > a + 1) { f -= a + 1; xp = c + k; while (++j < z)
		{ if ((f <<= 1) <= *++xp) break; f -= *xp; } } z = 1 << j; if ((q = (huft *)malloc((z + 1)*sizeof(huft))) == (huft *)NULL)
		{ if (h) huft_free(u[0]); return UNZ_ERRCODE_OUTOFMEMORY; } *t = q + 1; *(t = &(q->v.t)) = (huft *)NULL; u[h] = ++q; if (h)
		{ x[h] = i; r.b = (Bit8u)l; r.e = (Bit8u)(16 + j); r.v.t = q; j = i >> (w - l); u[h - 1][j] = r; } } r.b = (Bit8u)(k - w); if (p >= v + n) r.e = 99; else if (*p < s)
		{ r.e = (Bit8u)(*p < 256 ? 16 : 15); r.v.n = (Bit16u)*p++; } else
		{ r.e = (Bit8u)e[*p - s]; r.v.n = d[*p++ - s]; } f = 1 << (k - w); for (j = i >> w; j < z; j += f) q[j] = r; for (j = 1 << (k - 1);
		i & j; j >>= 1) { i ^= j; } i ^= j; while ((i & ((1 << w) - 1)) != x[h]) { h--; w -= l; } } }
		return (y == 0 || g == 1 ? UNZ_ERRCODE_OK : UNZ_ERRCODE_INCOMPLETE_SET);
	}

	static int flush(unz_explode* exploder, Bit32u w)
	{
		Bit8u *out_w = exploder->out_cur + w;
		int ret = (out_w > exploder->out_end ? 1 : 0);
		if (ret) out_w = exploder->out_end;
		memcpy(exploder->out_cur, exploder->slide, (out_w - exploder->out_cur));
		exploder->out_cur = out_w;
		return ret;
	}

	static int Run(unz_explode* exploder, Bit16u zip_bit_flag)
	{
		// Tables for length and distance
		static const Bit16u cplen2[]    = { 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65 };
		static const Bit16u cplen3[]    = { 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66 };
		static const Bit16u extra[]     = { 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8 };
		static const Bit16u cpdist4[]   = { 1, 65, 129, 193, 257, 321, 385, 449, 513, 577, 641, 705, 769, 833, 897, 961, 1025, 1089, 1153, 1217, 1281, 1345, 1409, 1473, 1537, 1601, 1665, 1729, 1793, 1857, 1921, 1985, 2049, 2113, 2177, 2241, 2305, 2369, 2433, 2497, 2561, 2625, 2689, 2753, 2817, 2881, 2945, 3009, 3073, 3137, 3201, 3265, 3329, 3393, 3457, 3521, 3585, 3649, 3713, 3777, 3841, 3905, 3969, 4033 };
		static const Bit16u cpdist8[]   = { 1, 129, 257, 385, 513, 641, 769, 897, 1025, 1153, 1281, 1409, 1537, 1665, 1793, 1921, 2049, 2177, 2305, 2433, 2561, 2689, 2817, 2945, 3073, 3201, 3329, 3457, 3585, 3713, 3841, 3969, 4097, 4225, 4353, 4481, 4609, 4737, 4865, 4993, 5121, 5249, 5377, 5505, 5633, 5761, 5889, 6017, 6145, 6273, 1, 6529, 6657, 6785, 6913, 7041, 7169, 7297, 7425, 7553, 7681, 7809, 7937, 8065 };
		static const Bit16u mask_bits[] = { 0x0000, 0x0001, 0x0003, 0x0007, 0x000f, 0x001f, 0x003f, 0x007f, 0x00ff, 0x01ff, 0x03ff, 0x07ff, 0x0fff, 0x1fff, 0x3fff, 0x7fff, 0xffff };

		huft *tb = NULL, *tl = NULL, *td = NULL; // literal code, length code, distance code tables
		Bit32u l[256]; // bit lengths for codes
		bool is8k  = ((zip_bit_flag & 2) == 2), islit = ((zip_bit_flag & 4) == 4);
		int bb = (islit ? 9 : 0), bl = 7, bd = ((exploder->in_end - exploder->in_start)  > 200000 ? 8 : 7); // bits for tb, tl, td
		Bit32u numbits = (is8k ? 7 : 6);

		int r;
		if (islit && (r = get_tree_build_huft(exploder, l, 256, 256, NULL, NULL, &tb, &bb)) != 0) goto done;
		if ((r = get_tree_build_huft(exploder, l, 64, 0, (islit ? cplen3 : cplen2), extra, &tl, &bl)) != 0) goto done;
		if ((r = get_tree_build_huft(exploder, l, 64, 0, (is8k ? cpdist8 : cpdist4), extra, &td, &bd)) != 0) goto done;

		// The implode algorithm uses a sliding 4K or 8K byte window on the uncompressed stream to find repeated byte strings.
		// This is implemented here as a circular buffer. The index is updated simply by incrementing and then and'ing with 0x0fff (4K-1) or 0x1fff (8K-1).
		// Here, the 32K buffer of inflate is used, and it works just as well to always have a 32K circular buffer, so the index is anded with 0x7fff.
		// This is done to allow the window to also be used as the output buffer.
		Bit32u s;          // bytes to decompress
		Bit32u e;          // table entry flag/number of extra bits
		Bit32u n, d;       // length and index for copy
		Bit32u w;          // current window position
		Bit32u mb, ml, md; // masks for bb (if lit), bl and bd bits
		Bit32u b;          // bit buffer
		Bit32u k;          // number of bits in bit buffer
		Bit32u u;          // true if unflushed
		huft *t;           // pointer to table entry

		#define UNZ_NEEDBITS(n) do {while(k<(n)){b|=((Bit32u)GetByte(exploder))<<k;k+=8;}} while(0)
		#define UNZ_DUMPBITS(n) do {b>>=(n);k-=(n);} while(0)

		// explode the coded data
		b = k = w = 0; // initialize bit buffer, window
		u = 1;         // buffer unflushed

		// precompute masks for speed
		mb = mask_bits[bb];
		ml = mask_bits[bl];
		md = mask_bits[bd];
		s = (Bit32u)(exploder->out_end - exploder->out_start);
		while (s > 0) // do until ucsize bytes uncompressed
		{
			UNZ_NEEDBITS(1);
			if (b & 1) // then literal
			{
				UNZ_DUMPBITS(1);
				s--;
				if (tb)
				{
					// LIT: Decompress the imploded data using coded literals and an 8K sliding window.
					UNZ_NEEDBITS((Bit32u)bb); // get coded literal
					if ((e = (t = tb + ((~(Bit32u)b) & mb))->e) > 16)
					{
						do
						{
							if (e == 99) { r = UNZ_ERRCODE_INTERNAL_ERROR; goto done; }
							UNZ_DUMPBITS(t->b);
							e -= 16;
							UNZ_NEEDBITS(e);
						} while ((e = (t = t->v.t + ((~(Bit32u)b) & mask_bits[e]))->e) > 16);
					}
					UNZ_DUMPBITS(t->b);
					exploder->slide[w++] = (Bit8u)t->v.n;
					if (w == WSIZE) { if (flush(exploder, w)) { r = UNZ_ERRCODE_OUTPUT_ERROR; goto done; } w = u = 0; }
				}
				else
				{
					// UNLIT: Decompress the imploded data using uncoded literals and an 8K sliding window.
					UNZ_NEEDBITS(8);
					exploder->slide[w++] = (Bit8u)b;
					if (w == WSIZE) { if (flush(exploder, w)) { r = UNZ_ERRCODE_OUTPUT_ERROR; goto done; } w = u = 0; }
					UNZ_DUMPBITS(8);
				}
			}
			else // else distance/length
			{
				UNZ_DUMPBITS(1);
				UNZ_NEEDBITS(numbits); // get distance low bits
				d = (Bit32u)b & ((1 << numbits) - 1);
				UNZ_DUMPBITS(numbits);
				UNZ_NEEDBITS((Bit32u)bd); // get coded distance high bits
				if ((e = (t = td + ((~(Bit32u)b) & md))->e) > 16)
				{
					do
					{
						if (e == 99) { r = UNZ_ERRCODE_INTERNAL_ERROR; goto done; }
						UNZ_DUMPBITS(t->b);
						e -= 16;
						UNZ_NEEDBITS(e);
					} while ((e = (t = t->v.t + ((~(Bit32u)b) & mask_bits[e]))->e) > 16);
				}
				UNZ_DUMPBITS(t->b);
				d = w - d - t->v.n; // construct offset
				UNZ_NEEDBITS((Bit32u)bl); // get coded length
				if ((e = (t = tl + ((~(Bit32u)b) & ml))->e) > 16)
				{
					do
					{
						if (e == 99) { r = UNZ_ERRCODE_INTERNAL_ERROR; goto done; }
						UNZ_DUMPBITS(t->b);
						e -= 16;
						UNZ_NEEDBITS(e);
					} while ((e = (t = t->v.t + ((~(Bit32u)b) & mask_bits[e]))->e) > 16);
				}
				UNZ_DUMPBITS(t->b);
				n = t->v.n;
				if (e) // get length extra bits
				{
					UNZ_NEEDBITS(8);
					n += (Bit32u)b & 0xff;
					UNZ_DUMPBITS(8);
				}

				// do the copy
				s -= n;
				do
				{
					n -= (e = (e = WSIZE - ((d &= WSIZE - 1) > w ? d : w)) > n ? n : e);
					if (u && w <= d)
					{
						memset(exploder->slide + w, 0, e);
						w += e;
						d += e;
					}
					else if (w - d >= e) // (this test assumes unsigned comparison)
					{
						memcpy(exploder->slide + w, exploder->slide + d, e);
						w += e;
						d += e;
					}
					else // do it slow to avoid memcpy() overlap
					{
						do {
							exploder->slide[w++] = exploder->slide[d++];
						} while (--e);
					}
					if (w == WSIZE)
					{
						if (flush(exploder, w)) { r = UNZ_ERRCODE_OUTPUT_ERROR; goto done; }
						w = u = 0;
					}
				} while (n);
			}
		}

		#undef UNZ_NEEDBITS
		#undef UNZ_DUMPBITS

		// flush out slide
		if (flush(exploder, w)) { r = UNZ_ERRCODE_OUTPUT_ERROR; goto done; }

		done:
		huft_free(td);
		huft_free(tl);
		huft_free(tb);
		return r;
	}
};

#include "miniz.inl"

bool SFileZip::Unpack(Bit64u unpack_until)
{
	ZIP_ASSERT(size && method != METHOD_STORED);
	if (!lhskip && !SkipLocalHeader()) return false;
	SFile& fi = reader.archive;
	if (method == METHOD_DEFLATED)
	{
		struct deflate_state { mz_inflate::tinfl_decompressor inflator; Bit8u read_buf[mz_inflate::MZ_ZIP_MAX_IO_BUF_SIZE]; Bit32u read_buf_avail, read_buf_ofs, comp_remaining; } *st = (deflate_state*)decomp_state;
		if (!st)
		{
			decomp_state = st = (deflate_state*)malloc(sizeof(deflate_state));
			mz_inflate::tinfl_init(&st->inflator);
			st->read_buf_avail = st->read_buf_ofs = 0;
			st->comp_remaining = comp_size;
		}

		//printf("Need Unpacking %s until %u ...\n", path.c_str(), (unsigned)unpack_until);
		const Bit64u want_until = unpack_until + 1 * 1024 * 1024, fiseek = data_ofs + comp_size - st->comp_remaining;
		for (unpack_until = unpacked; unpack_until < want_until;) unpack_until += 8*1024*1024;
		if (unpack_until > size) unpack_until = size;
		if (fi.Seek(fiseek) != fiseek) { ZIP_ASSERT(false); }
		buf = (Bit8u*)realloc(buf, (size_t)unpack_until);
		//printf("Unpacking %s until %u ...\n", path.c_str(), (unsigned)unpack_until);

		for (mz_inflate::tinfl_status status = mz_inflate::TINFL_STATUS_NEEDS_MORE_INPUT; (status == mz_inflate::TINFL_STATUS_NEEDS_MORE_INPUT || status == mz_inflate::TINFL_STATUS_HAS_MORE_OUTPUT) && unpacked != unpack_until;)
		{
			if (!st->read_buf_avail)
			{
				st->read_buf_avail = (st->comp_remaining < mz_inflate::MZ_ZIP_MAX_IO_BUF_SIZE ? st->comp_remaining : mz_inflate::MZ_ZIP_MAX_IO_BUF_SIZE);
				if (fi.Read(st->read_buf, st->read_buf_avail) != st->read_buf_avail)
					break;
				st->comp_remaining -= st->read_buf_avail;
				st->read_buf_ofs = 0;
			}
			Bit32u out_buf_size = (Bit32u)(unpack_until - unpacked);
			Bit8u *pWrite_buf_cur = buf + unpacked;
			Bit32u in_buf_size = st->read_buf_avail;
			status = mz_inflate::tinfl_decompress(&st->inflator, st->read_buf + st->read_buf_ofs, &in_buf_size, buf, pWrite_buf_cur, &out_buf_size, mz_inflate::TINFL_FLAG_USING_NON_WRAPPING_OUTPUT_BUF | (st->comp_remaining ? mz_inflate::TINFL_FLAG_HAS_MORE_INPUT : 0));
			st->read_buf_avail -= in_buf_size;
			st->read_buf_ofs += in_buf_size;
			unpacked += out_buf_size;
			ZIP_ASSERT(!out_buf_size || unpacked <= unpack_until);
			ZIP_ASSERT(status == mz_inflate::TINFL_STATUS_NEEDS_MORE_INPUT || status == mz_inflate::TINFL_STATUS_HAS_MORE_OUTPUT || status == mz_inflate::TINFL_STATUS_DONE);
		}
		if (unpacked == size) { free(decomp_state); decomp_state = NULL; }
	}
	else if (method == METHOD_SHRUNK)
	{
		ZIP_ASSERT(buf == NULL);
		buf = (Bit8u*)malloc((size_t)size);
		oz_unshrink *unshrink = (oz_unshrink*)malloc(sizeof(oz_unshrink) + comp_size);
		Bit8u* in_buf = (Bit8u*)(unshrink + 1);
		if (fi.Seek(data_ofs) != data_ofs || fi.Read(in_buf, comp_size) != comp_size) goto bad;
		unshrink->in_start = unshrink->in_cur = in_buf;
		unshrink->in_end = in_buf + comp_size;
		unshrink->out_start = unshrink->out_cur = buf;
		unshrink->out_end = unshrink->out_start + size;
		#ifndef NDEBUG
		int res =
		#endif
		oz_unshrink::Run(unshrink);
		ZIP_ASSERT(res == 0);
		free(unshrink);
		unpacked = size;
	}
	else if (method == METHOD_IMPLODED)
	{
		ZIP_ASSERT(buf == NULL);
		buf = (Bit8u*)malloc((size_t)size);
		unz_explode *explode = (unz_explode*)malloc(sizeof(unz_explode) + comp_size);
		Bit8u* in_buf = (Bit8u*)(explode + 1);
		if (fi.Seek(data_ofs) != data_ofs || fi.Read(in_buf, comp_size) != comp_size) goto bad;
		explode->in_start = explode->in_cur = in_buf;
		explode->in_end = in_buf + comp_size;
		explode->out_start = explode->out_cur = buf;
		explode->out_end = explode->out_start + size;
		#ifndef NDEBUG
		int res =
		#endif
		unz_explode::Run(explode, bit_flags);
		ZIP_ASSERT(res == 0);
		free(explode);
		unpacked = size;
	}
	else { bad: ZIP_ASSERT(false); size = 0; return false; }
	ZIP_ASSERT(size > 5000000 || unpacked < size || CRC32(buf, (size_t)size) == crc32);
	return true;
}

SFileMemory* SFileZip::BuildDeflated(const Bit8u* data, size_t comp_len, size_t uncomp_len)
{
	SFileMemory* res = new SFileMemory(uncomp_len); res->path.assign("<GENERATED>"); Bit8u* trg = res->buf;
	mz_inflate::tinfl_decompressor inflator;
	mz_inflate::tinfl_init(&inflator);
	const Bit8u *src = data, *src_end = src + comp_len, *trg_start = trg, *trg_end = trg_start + uncomp_len;
	for (mz_inflate::tinfl_status status = mz_inflate::TINFL_STATUS_HAS_MORE_OUTPUT; status == mz_inflate::TINFL_STATUS_HAS_MORE_OUTPUT;)
	{
		Bit32u in_size = (Bit32u)(src_end - src), out_size = (Bit32u)(trg_end - trg);
		status = mz_inflate::tinfl_decompress(&inflator, src, &in_size, (Bit8u*)trg_start, trg, &out_size, mz_inflate::TINFL_FLAG_USING_NON_WRAPPING_OUTPUT_BUF);
		src += in_size;
		trg += out_size;
		ZIP_ASSERT(status == mz_inflate::TINFL_STATUS_HAS_MORE_OUTPUT || status == mz_inflate::TINFL_STATUS_DONE);
	}
	return res;
}

bool SFileZip::CompressInto(FILE* f, SFile* fsrc, Bit32u& out_crc, Bit32u& out_compsize)
{
	// create tdefl() compatible flags (we have to compose the low-level flags ourselves
	// The number of dictionary probes to use at each compression level (0-10). 0=implies fastest/minimal possible probing.
	static const mz_uint s_tdefl_num_probes[11] = { 0, 1, 6, 32, 16, 32, 128, 256, 512, 768, 1500 };
	const size_t level = 10;
	const mz_uint comp_flags = /*TDEFL_WRITE_ZLIB_HEADER |*/ s_tdefl_num_probes[MZ_MIN(10, level)] | ((level <= 3) ? TDEFL_GREEDY_PARSING_FLAG : 0);
	Bit32u crc = 0, compsize = 0;

	// Initialize the low-level compressor.
	static tdefl_compressor deflator;
	tdefl_init(&deflator, NULL, NULL, comp_flags);

	static Bit8u s_outbuf[1024 * 512];
	const Bit8u *next_in = NULL;
	Bit8u *next_out = s_outbuf;
	size_t avail_out = sizeof(s_outbuf), avail_in = 0, src_remain = (size_t)fsrc->size;

	// Compression.
	bool wasOpen = fsrc->IsOpen();
	if (wasOpen) fsrc->Seek(0); else if (!fsrc->Open()) return false;
	for (;;)
	{
		if (!avail_in && src_remain)
		{
			size_t n = (src_remain < sizeof(ReadBuf) ? src_remain : sizeof(ReadBuf));
			if (fsrc->Read(ReadBuf, n) != n) return false;
			next_in = ReadBuf;
			avail_in = n;
			src_remain -= n;
			crc = CRC32(next_in, (size_t)avail_in, crc);
		}

		// Compress as much of the input as possible (or all of it) to the output buffer.
		size_t in_bytes = avail_in, out_bytes = avail_out;
		tdefl_status status = tdefl_compress(&deflator, next_in, &in_bytes, next_out, &out_bytes, src_remain ? TDEFL_NO_FLUSH : TDEFL_FINISH);

		next_in += in_bytes;
		avail_in -= in_bytes;

		next_out += out_bytes;
		avail_out -= out_bytes;
		compsize += (Bit32u)out_bytes;

		if (status != TDEFL_STATUS_OKAY || !avail_out)
		{
			// Output buffer is full, or compression is done or failed, so write buffer to output file.
			Bit32u n = sizeof(s_outbuf) - (Bit32u)avail_out;
			if (!fwrite(s_outbuf, n, 1, f)) return false;
			next_out = s_outbuf;
			avail_out = sizeof(s_outbuf);
		}
		if (status == TDEFL_STATUS_DONE) break; // Compression completed successfully.
		if (status != TDEFL_STATUS_OKAY) { ZIP_ASSERT(false); return false; } // Compression somehow failed.
	}
	ZIP_ASSERT(src_remain == 0 && avail_in == 0);
	out_crc = crc;
	out_compsize = compsize;
	return true;
}
