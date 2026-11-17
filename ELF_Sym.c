/*
 * elfsym.c - pure C ELF symbol parser (static / dynamic)
 * gcc -O2 -o elfsym elfsym.c
 *  0 = static  : input so path, parse via SECTION headers
 *  1 = dynamic : input pkg + so name, parse via PROGRAM headers (PT_DYNAMIC)
 */
#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stdbool.h>
#include <dirent.h>
#include <unistd.h>
#include <fcntl.h>
#include <errno.h>
#include <sys/stat.h>
#include <sys/mman.h>
#include <sys/types.h>

/* ---------------- ELF structures ---------------- */
typedef struct {
    uint8_t  e_ident[16]; uint16_t e_type, e_machine; uint32_t e_version;
    uint64_t e_entry, e_phoff, e_shoff; uint32_t e_flags;
    uint16_t e_ehsize, e_phentsize, e_phnum, e_shentsize, e_shnum, e_shstrndx;
} Elf64_Ehdr;
typedef struct {
    uint32_t sh_name, sh_type; uint64_t sh_flags, sh_addr, sh_offset, sh_size;
    uint32_t sh_link, sh_info; uint64_t sh_addralign, sh_entsize;
} Elf64_Shdr;
typedef struct {
    uint32_t st_name; uint8_t st_info, st_other; uint16_t st_shndx;
    uint64_t st_value, st_size;
} Elf64_Sym;
typedef struct { uint32_t p_type, p_flags; uint64_t p_offset, p_vaddr, p_paddr, p_filesz, p_memsz, p_align; } Elf64_Phdr;
typedef struct { int64_t d_tag; uint64_t d_val; } Elf64_Dyn;

typedef struct {
    uint8_t  e_ident[16]; uint16_t e_type, e_machine; uint32_t e_version;
    uint32_t e_entry, e_phoff, e_shoff, e_flags;
    uint16_t e_ehsize, e_phentsize, e_phnum, e_shentsize, e_shnum, e_shstrndx;
} Elf32_Ehdr;
typedef struct {
    uint32_t sh_name, sh_type, sh_flags, sh_addr, sh_offset, sh_size;
    uint32_t sh_link, sh_info, sh_addralign, sh_entsize;
} Elf32_Shdr;
typedef struct {
    uint32_t st_name, st_value, st_size; uint8_t st_info, st_other; uint16_t st_shndx;
} Elf32_Sym;
typedef struct { uint32_t p_type, p_offset, p_vaddr, p_paddr, p_filesz, p_memsz, p_flags, p_align; } Elf32_Phdr;
typedef struct { int32_t d_tag; uint32_t d_val; } Elf32_Dyn;

typedef char chk1[(sizeof(Elf64_Sym)  == 24) ? 1 : -1];
typedef char chk2[(sizeof(Elf64_Shdr) == 64) ? 1 : -1];
typedef char chk3[(sizeof(Elf64_Sym)  == 24) ? 1 : -1];
typedef char chk4[(sizeof(Elf32_Sym)  == 16) ? 1 : -1];
typedef char chk5[(sizeof(Elf64_Phdr) == 56) ? 1 : -1];
typedef char chk6[(sizeof(Elf64_Dyn)  == 16) ? 1 : -1];

/* ---------------- records ---------------- */
typedef struct {
    uint64_t vaddr, size, runtime;
    long     fileoff;
    uint8_t  type, bind;
    uint16_t shndx;
    char     source;
    char    *name;
} SymRec;

typedef struct { SymRec *v; size_t n, cap; } Vec;

static void vec_push(Vec *vc, SymRec r) {
    if (vc->n == vc->cap) {
        vc->cap = vc->cap ? vc->cap * 2 : 4096;
        vc->v = realloc(vc->v, vc->cap * sizeof(SymRec));
        if (!vc->v) { fprintf(stderr, "oom\n"); exit(1); }
    }
    vc->v[vc->n++] = r;
}

/* ---------------- constants ---------------- */
#define ELFCLASS64 2
#define ELFDATA2LSB 1
#define ET_DYN 3

#define SHT_SYMTAB 2
#define SHT_DYNSYM 11
#define SHT_NOBITS 8
#define SHF_ALLOC 2

#define PT_LOAD 1
#define PT_DYNAMIC 2

#define DT_NULL 0
#define DT_HASH 4
#define DT_STRTAB 5
#define DT_SYMTAB 6
#define DT_STRSZ 10
#define DT_SYMENT 11
#define DT_GNU_HASH 0x6ffffef5

#define STT_NOTYPE 0
#define STT_OBJECT 1
#define STT_FUNC 2
#define STT_SECTION 3
#define STT_FILE 4
#define STT_COMMON 5
#define STT_TLS 6
#define STT_GNU_IFUNC 10

#define STB_LOCAL 0
#define STB_GLOBAL 1
#define STB_WEAK 2
#define SHN_UNDEF 0

static const char *type_name(uint8_t t) {
    switch (t) {
        case STT_NOTYPE:    return "NOTYPE";
        case STT_OBJECT:    return "OBJECT";
        case STT_FUNC:      return "FUNC";
        case STT_SECTION:   return "SECTION";
        case STT_FILE:      return "FILE";
        case STT_COMMON:    return "COMMON";
        case STT_TLS:       return "TLS";
        case STT_GNU_IFUNC: return "IFUNC";
        default:            return "UNKNOWN";
    }
}

static const char *bind_name(uint8_t b) {
    switch (b) {
        case STB_LOCAL:  return "LOCAL";
        case STB_GLOBAL: return "GLOBAL";
        case STB_WEAK:   return "WEAK";
        default:         return "UNKNOWN";
    }
}

static void mkdir_p(const char *path) {
    char tmp[2048];
    snprintf(tmp, sizeof tmp, "%s", path);
    char *p = tmp + 1;
    for (; *p; p++)
        if (*p == '/') { *p = 0; mkdir(tmp, 0777); *p = '/'; }
    mkdir(tmp, 0777);
}

static pid_t find_pid(const char *pkg) {
    DIR *d = opendir("/proc");
    if (!d) return -1;
    struct dirent *de;
    pid_t found = -1;
    size_t len = strlen(pkg);
    while ((de = readdir(d))) {
        if (de->d_name[0] < '0' || de->d_name[0] > '9') continue;
        char p[300];
        snprintf(p, sizeof p, "/proc/%s/cmdline", de->d_name);
        int fd = open(p, O_RDONLY);
        if (fd < 0) continue;
        char buf[512];
        ssize_t n = read(fd, buf, sizeof buf - 1);
        close(fd);
        if (n <= 0) continue;
        buf[n] = 0;
        if (strncmp(buf, pkg, len) == 0 && (buf[len] == 0 || buf[len] == ':')) {
            found = (pid_t)atoi(de->d_name);
            break;
        }
    }
    closedir(d);
    return found;
}

/* ================= PROGRAM HEADER PATH (runtime / memory) ================= */

static long ph_va2off64(const Elf64_Phdr *ph, size_t n, uint64_t va) {
    for (size_t i = 0; i < n; i++) {
        if (ph[i].p_type != PT_LOAD) continue;
        if (ph[i].p_filesz == 0) continue;
        if (va >= ph[i].p_vaddr && va < ph[i].p_vaddr + ph[i].p_filesz)
            return (long)(ph[i].p_offset + (va - ph[i].p_vaddr));
    }
    return -1;
}

static long ph_va2off32(const Elf32_Phdr *ph, size_t n, uint32_t va) {
    for (size_t i = 0; i < n; i++) {
        if (ph[i].p_type != PT_LOAD) continue;
        if (ph[i].p_filesz == 0) continue;
        if (va >= ph[i].p_vaddr && va < ph[i].p_vaddr + ph[i].p_filesz)
            return (long)(ph[i].p_offset + (va - ph[i].p_vaddr));
    }
    return -1;
}

/* GNU hash -> symbol count */
static uint32_t gnu_hash_count64(const uint32_t *gh, size_t max_u32)
{
    if (max_u32 < 4) return 0;
    uint32_t nbuckets = gh[0];
    uint32_t symoffset = gh[1];
    uint32_t bloom_size = gh[2];
    size_t hdr = 4 + (size_t)bloom_size * 2;
    if (hdr + nbuckets > max_u32) return 0;
    const uint32_t *buckets = gh + hdr;
    const uint32_t *chain = buckets + nbuckets;
    size_t chainmax = max_u32 - hdr - nbuckets;
    uint32_t last = 0;
    for (uint32_t i = 0; i < nbuckets; i++)
        if (buckets[i] > last) last = buckets[i];
    if (last < symoffset) return symoffset;
    uint32_t idx = last;
    while ((size_t)(idx - symoffset) < chainmax && !(chain[idx - symoffset] & 1u)) idx++;
    return idx + 1;
}

static uint32_t gnu_hash_count32(const uint32_t *gh, size_t max_u32)
{
    if (max_u32 < 4) return 0;
    uint32_t nbuckets = gh[0];
    uint32_t symoffset = gh[1];
    uint32_t bloom_size = gh[2];
    size_t hdr = 4 + bloom_size;
    if (hdr + nbuckets > max_u32) return 0;
    const uint32_t *buckets = gh + hdr;
    const uint32_t *chain = buckets + nbuckets;
    size_t chainmax = max_u32 - hdr - nbuckets;
    uint32_t last = 0;
    for (uint32_t i = 0; i < nbuckets; i++)
        if (buckets[i] > last) last = buckets[i];
    if (last < symoffset) return symoffset;
    uint32_t idx = last;
    while ((size_t)(idx - symoffset) < chainmax && !(chain[idx - symoffset] & 1u)) idx++;
    return idx + 1;
}

/* DT_* 指针有两种可能：
 *   A) 未重定位 -> 已是 ELF vaddr（小值，如 0x48b8）
 *   B) 已重定位 -> 运行时绝对地址（大值，如 0x756b6048b8）
 * 两种都试，谁能落到 PT_LOAD 就用谁。 */
static long ph_resolve64(const Elf64_Phdr *ph, size_t phnum, uint64_t val, uint64_t bias)
{
    long o = ph_va2off64(ph, phnum, val);          /* 情况 A：当 vaddr 用 */
    if (o >= 0) return o;
    if (bias && val >= bias)
        o = ph_va2off64(ph, phnum, val - bias);    /* 情况 B：当绝对地址用 */
    return o;
}

static int parse_dynsym_ph64(const uint8_t *m, size_t fsz, const Elf64_Ehdr *eh,
                             uint64_t bias, Vec *vec, uint64_t *nf, uint64_t *no)
{
    if (!eh->e_phoff || !eh->e_phnum) { fprintf(stderr, "[!] no program headers\n"); return 1; }
    if ((uint64_t)eh->e_phoff + (uint64_t)eh->e_phnum * eh->e_phentsize > fsz) {
        fprintf(stderr, "[!] phdr out of range\n"); return 1;
    }
    const Elf64_Phdr *ph = (const Elf64_Phdr *)(m + eh->e_phoff);
    size_t phnum = eh->e_phnum;

    const Elf64_Dyn *dyn = NULL;
    size_t dyncnt = 0;
    for (size_t i = 0; i < phnum; i++) {
        if (ph[i].p_type != PT_DYNAMIC) continue;
        long o = ph_va2off64(ph, phnum, ph[i].p_vaddr);
        if (o < 0) o = (long)ph[i].p_offset;
        if (o < 0 || (size_t)o >= fsz) continue;
        dyn = (const Elf64_Dyn *)(m + o);
        dyncnt = ph[i].p_filesz / sizeof(Elf64_Dyn);
        fprintf(stderr, "[*] PT_DYNAMIC @ file 0x%lx, %zu entries\n", o, dyncnt);
        break;
    }
    if (!dyn) { fprintf(stderr, "[!] PT_DYNAMIC not found\n"); return 1; }

    uint64_t symtab = 0, strtab = 0, strsz = 0, hash = 0, ghash = 0;
    uint64_t syment = sizeof(Elf64_Sym);
    for (size_t i = 0; i < dyncnt && dyn[i].d_tag != DT_NULL; i++) {
        switch (dyn[i].d_tag) {
            case DT_SYMTAB:   symtab = dyn[i].d_val; break;
            case DT_STRTAB:   strtab = dyn[i].d_val; break;
            case DT_STRSZ:    strsz  = dyn[i].d_val; break;
            case DT_SYMENT:   syment = dyn[i].d_val; break;
            case DT_HASH:     hash   = dyn[i].d_val; break;
            case DT_GNU_HASH: ghash  = dyn[i].d_val; break;
        }
    }
    fprintf(stderr, "[*] DT_SYMTAB=0x%llx DT_STRTAB=0x%llx DT_STRSZ=%llu\n",
            (unsigned long long)symtab, (unsigned long long)strtab, (unsigned long long)strsz);
    if (!symtab || !strtab) { fprintf(stderr, "[!] missing DT_SYMTAB/DT_STRTAB\n"); return 1; }
    if (syment == 0) syment = sizeof(Elf64_Sym);

    long soff = ph_resolve64(ph, phnum, symtab, bias);
    long stroff = ph_resolve64(ph, phnum, strtab, bias);
    if (soff < 0 || stroff < 0) {
        fprintf(stderr, "[!] symtab/strtab outside PT_LOAD (soff=%ld stroff=%ld, bias=0x%llx)\n",
            soff, stroff, (unsigned long long)bias);
        return 1;
    }
    fprintf(stderr, "[*] symtab file off 0x%lx, strtab file off 0x%lx\n", soff, stroff);

    uint32_t nsym = 0;
    if (hash) {
        long ho = ph_resolve64(ph, phnum, hash, bias);
        if (ho > 0 && (size_t)ho + 8 <= fsz) {
            const uint32_t *h = (const uint32_t *)(m + ho);
            nsym = h[1];
            fprintf(stderr, "[*] DT_HASH nchain=%u\n", nsym);
        }
    }
    if (nsym == 0 && ghash) {
        long go = ph_resolve64(ph, phnum, ghash, bias);
        if (go > 0 && (size_t)go < fsz) {
            nsym = gnu_hash_count64((const uint32_t *)(m + go), (fsz - (size_t)go) / 4);
            fprintf(stderr, "[*] DT_GNU_HASH -> %u syms\n", nsym);
        }
    }
    if (nsym == 0) {
        nsym = (uint32_t)((fsz - (size_t)stroff) / sizeof(Elf64_Sym));
        fprintf(stderr, "[!] no hash, fallback count %u\n", nsym);
        if (nsym > 200000) nsym = 200000;
    }

    const char *strbase = (const char *)(m + stroff);
    size_t strmax = fsz - (size_t)stroff;
    if (strsz && strsz < strmax) strmax = (size_t)strsz;

    for (uint32_t i = 0; i < nsym; i++) {
        const Elf64_Sym *sym = (const Elf64_Sym *)(m + soff + (size_t)i * syment);
        if ((size_t)soff + (size_t)i * syment + sizeof(Elf64_Sym) > fsz) break;
        if (sym->st_name >= strmax) continue;
        const char *nm = strbase + sym->st_name;
        if (!nm[0]) continue;
        SymRec r;
        r.vaddr   = sym->st_value;
        r.size    = sym->st_size;
        r.shndx   = sym->st_shndx;
        r.type    = sym->st_info & 0xF;
        r.bind    = sym->st_info >> 4;
        r.source  = 'D';
        r.name    = (char *)nm;
        r.runtime = (sym->st_shndx == SHN_UNDEF) ? 0 : (sym->st_value + bias);
        r.fileoff = (sym->st_shndx == SHN_UNDEF || sym->st_value == 0)
                    ? -1 : ph_va2off64(ph, phnum, sym->st_value);
        if (r.type == STT_FUNC)   (*nf)++;
        if (r.type == STT_OBJECT) (*no)++;
        vec_push(vec, r);
    }
    return 0;
}

/* ================= SECTION HEADER PATH (static file) ================= */

static long sh_va2off64(const Elf64_Shdr *sh, size_t n, uint64_t va) {
    for (size_t i = 0; i < n; i++) {
        if (sh[i].sh_type == SHT_NOBITS) continue;
        if (!(sh[i].sh_flags & SHF_ALLOC)) continue;
        if (sh[i].sh_size == 0) continue;
        if (va >= sh[i].sh_addr && va < sh[i].sh_addr + sh[i].sh_size)
            return (long)(sh[i].sh_offset + (va - sh[i].sh_addr));
    }
    return -1;
}

static long sh_va2off32(const Elf32_Shdr *sh, size_t n, uint32_t va) {
    for (size_t i = 0; i < n; i++) {
        if (sh[i].sh_type == SHT_NOBITS) continue;
        if (!(sh[i].sh_flags & SHF_ALLOC)) continue;
        if (sh[i].sh_size == 0) continue;
        if (va >= sh[i].sh_addr && va < sh[i].sh_addr + sh[i].sh_size)
            return (long)(sh[i].sh_offset + (va - sh[i].sh_addr));
    }
    return -1;
}

static size_t collect_sh64(const uint8_t *m, size_t fsz, const Elf64_Shdr *sh, size_t shnum,
                           const Elf64_Shdr *tab, char src, uint64_t bias, Vec *vec,
                           uint64_t *nf, uint64_t *no)
{
    if (tab->sh_entsize == 0) return 0;
    if (tab->sh_link >= shnum) return 0;
    if (tab->sh_offset + tab->sh_size > fsz) return 0;
    const char *strtab = (const char *)(m + sh[tab->sh_link].sh_offset);
    size_t strsz = sh[tab->sh_link].sh_size;
    size_t cnt = tab->sh_size / tab->sh_entsize;
    for (size_t i = 0; i < cnt; i++) {
        const Elf64_Sym *sym = (const Elf64_Sym *)(m + tab->sh_offset + i * tab->sh_entsize);
        if (sym->st_name >= strsz) continue;
        const char *nm = strtab + sym->st_name;
        if (!nm[0]) continue;
        SymRec r;
        r.vaddr   = sym->st_value;
        r.size    = sym->st_size;
        r.shndx   = sym->st_shndx;
        r.type    = sym->st_info & 0xF;
        r.bind    = sym->st_info >> 4;
        r.source  = src;
        r.name    = (char *)nm;
        r.runtime = (sym->st_shndx == SHN_UNDEF) ? 0 : (sym->st_value + bias);
        r.fileoff = (sym->st_shndx == SHN_UNDEF || sym->st_value == 0)
                    ? -1 : sh_va2off64(sh, shnum, sym->st_value);
        if (r.type == STT_FUNC)   (*nf)++;
        if (r.type == STT_OBJECT) (*no)++;
        vec_push(vec, r);
    }
    return cnt;
}

static size_t collect_sh32(const uint8_t *m, size_t fsz, const Elf32_Shdr *sh, size_t shnum,
                           const Elf32_Shdr *tab, char src, uint64_t bias, Vec *vec,
                           uint64_t *nf, uint64_t *no)
{
    if (tab->sh_entsize == 0) return 0;
    if (tab->sh_link >= shnum) return 0;
    if (tab->sh_offset + tab->sh_size > fsz) return 0;
    const char *strtab = (const char *)(m + sh[tab->sh_link].sh_offset);
    size_t strsz = sh[tab->sh_link].sh_size;
    size_t cnt = tab->sh_size / tab->sh_entsize;
    for (size_t i = 0; i < cnt; i++) {
        const Elf32_Sym *sym = (const Elf32_Sym *)(m + tab->sh_offset + i * tab->sh_entsize);
        if (sym->st_name >= strsz) continue;
        const char *nm = strtab + sym->st_name;
        if (!nm[0]) continue;
        SymRec r;
        r.vaddr   = sym->st_value;
        r.size    = sym->st_size;
        r.shndx   = sym->st_shndx;
        r.type    = sym->st_info & 0xF;
        r.bind    = sym->st_info >> 4;
        r.source  = src;
        r.name    = (char *)nm;
        r.runtime = (sym->st_shndx == SHN_UNDEF) ? 0 : ((uint64_t)sym->st_value + bias);
        r.fileoff = (sym->st_shndx == SHN_UNDEF || sym->st_value == 0)
                    ? -1 : sh_va2off32(sh, shnum, sym->st_value);
        if (r.type == STT_FUNC)   (*nf)++;
        if (r.type == STT_OBJECT) (*no)++;
        vec_push(vec, r);
    }
    return cnt;
}

static int cmp_sym(const void *a, const void *b) {
    const SymRec *x = (const SymRec *)a;
    const SymRec *y = (const SymRec *)b;
    uint64_t kx = (x->shndx == SHN_UNDEF) ? ~0ULL : x->runtime;
    uint64_t ky = (y->shndx == SHN_UNDEF) ? ~0ULL : y->runtime;
    if (kx < ky) return -1;
    if (kx > ky) return 1;
    return strcmp(x->name ? x->name : "", y->name ? y->name : "");
}

/* ================= MAIN PARSE ================= */

static int parse_elf_data(const uint8_t *m, size_t fsz, const char *sopath,
                          uint64_t bias, const char *outdir, const char *soname,
                          int force_ph)
{
    if (fsz < 64 || m[0] != 0x7f || m[1] != 'E' || m[2] != 'L' || m[3] != 'F') {
        fprintf(stderr, "[!] not ELF\n"); return 1;
    }
    int is64 = (m[4] == ELFCLASS64);
    if (m[5] != ELFDATA2LSB) { fprintf(stderr, "[!] only little-endian\n"); return 1; }

    Vec vec; vec.v = NULL; vec.n = 0; vec.cap = 0;
    uint64_t nf = 0, no = 0, n_sym = 0, n_dyn = 0;
    int etype = 0;
    const char *via = "SH";

    if (is64) {
        const Elf64_Ehdr *eh = (const Elf64_Ehdr *)m;
        etype = eh->e_type;

        if (!force_ph && eh->e_shoff && eh->e_shnum &&
            (uint64_t)eh->e_shoff + (uint64_t)eh->e_shnum * eh->e_shentsize <= fsz) {
            const Elf64_Shdr *sh = (const Elf64_Shdr *)(m + eh->e_shoff);
            size_t shnum = eh->e_shnum;
            for (size_t i = 0; i < shnum; i++) {
                if (sh[i].sh_type == SHT_SYMTAB)
                    n_sym += collect_sh64(m, fsz, sh, shnum, &sh[i], 'S', bias, &vec, &nf, &no);
                else if (sh[i].sh_type == SHT_DYNSYM)
                    n_dyn += collect_sh64(m, fsz, sh, shnum, &sh[i], 'D', bias, &vec, &nf, &no);
            }
            fprintf(stderr, "[*] SH path: symtab=%llu dynsym=%llu\n",
                    (unsigned long long)n_sym, (unsigned long long)n_dyn);
        } else {
            fprintf(stderr, "[*] SH path skipped (shoff=%llu shnum=%u)\n",
                    (unsigned long long)eh->e_shoff, (unsigned)eh->e_shnum);
        }

        if (vec.n == 0) {
            fprintf(stderr, "[*] falling back to PH path\n");
            via = "PH";
            parse_dynsym_ph64(m, fsz, eh, bias, &vec, &nf, &no);
            n_dyn = vec.n;
        }
    } else {
        const Elf32_Ehdr *eh = (const Elf32_Ehdr *)m;
        etype = eh->e_type;
        if (eh->e_shoff && eh->e_shnum &&
            (uint64_t)eh->e_shoff + (uint64_t)eh->e_shnum * eh->e_shentsize <= fsz) {
            const Elf32_Shdr *sh = (const Elf32_Shdr *)(m + eh->e_shoff);
            size_t shnum = eh->e_shnum;
            for (size_t i = 0; i < shnum; i++) {
                if (sh[i].sh_type == SHT_SYMTAB)
                    n_sym += collect_sh32(m, fsz, sh, shnum, &sh[i], 'S', bias, &vec, &nf, &no);
                else if (sh[i].sh_type == SHT_DYNSYM)
                    n_dyn += collect_sh32(m, fsz, sh, shnum, &sh[i], 'D', bias, &vec, &nf, &no);
            }
        }
        if (vec.n == 0) fprintf(stderr, "[!] ELF32 PH path not implemented\n");
    }

    if (vec.n == 0) { fprintf(stderr, "[!] zero symbols collected\n"); free(vec.v); return 1; }
    qsort(vec.v, vec.n, sizeof(SymRec), cmp_sym);

    mkdir_p(outdir);
    char path[2300];

    snprintf(path, sizeof path, "%s/%s.symbols.tsv", outdir, soname);
    FILE *out = fopen(path, "w");
    if (!out) { fprintf(stderr, "[!] cannot write %s\n", path); free(vec.v); return 1; }
    fprintf(out, "# ELF symbol dump via %s path\n", via);
    fprintf(out, "# file      = %s\n", sopath);
    fprintf(out, "# class     = %s   type = %s\n", is64 ? "ELF64" : "ELF32",
            etype == ET_DYN ? "DYN(PIC)" : (etype == 2 ? "EXEC" : "OTHER"));
    fprintf(out, "# load_bias = 0x%llx\n", (unsigned long long)bias);
    fprintf(out, "# symtab    = %llu   dynsym = %llu\n",
            (unsigned long long)n_sym, (unsigned long long)n_dyn);
    fprintf(out, "# funcs     = %llu   objects = %llu   total = %zu\n",
            (unsigned long long)nf, (unsigned long long)no, vec.n);
    fprintf(out, "# columns: vaddr\truntime\tfile_off\tsize\ttype\tbind\tshndx\tsrc\tname\n");
    for (size_t i = 0; i < vec.n; i++) {
        SymRec *r = &vec.v[i];
        char ob[32];
        if (r->fileoff >= 0) snprintf(ob, sizeof ob, "0x%lx", r->fileoff);
        else snprintf(ob, sizeof ob, "-");
        fprintf(out, "0x%llx\t0x%llx\t%s\t0x%llx\t%s\t%s\t%u\t%c\t%s\n",
                (unsigned long long)r->vaddr, (unsigned long long)r->runtime, ob,
                (unsigned long long)r->size, type_name(r->type), bind_name(r->bind),
                r->shndx, r->source, r->name);
    }
    fclose(out);

    snprintf(path, sizeof path, "%s/%s.symbols.txt", outdir, soname);
    FILE *tx = fopen(path, "w");
    if (tx) {
        static const char *gname[3] = { "FUNC", "OBJECT", "OTHER" };
        fprintf(tx, "================================================================\n");
        fprintf(tx, "  ELF symbols  %s\n", sopath);
        fprintf(tx, "  path=%s  class=%s  type=%s  load_bias=0x%llx\n", via,
                is64 ? "ELF64" : "ELF32",
                etype == ET_DYN ? "DYN(PIC)" : (etype == 2 ? "EXEC" : "OTHER"),
                (unsigned long long)bias);
        fprintf(tx, "  symtab=%llu  dynsym=%llu  total=%zu  FUNC=%llu  OBJECT=%llu\n",
                (unsigned long long)n_sym, (unsigned long long)n_dyn, vec.n,
                (unsigned long long)nf, (unsigned long long)no);
        fprintf(tx, "================================================================\n\n");
        for (int g = 0; g < 3; g++) {
            size_t cnt = 0, idx = 0;
            for (size_t i = 0; i < vec.n; i++) {
                int gg = (vec.v[i].type == STT_FUNC) ? 0 : (vec.v[i].type == STT_OBJECT ? 1 : 2);
                if (gg == g) cnt++;
            }
            if (cnt == 0) continue;
            fprintf(tx, "==================== %s : %zu ====================\n\n", gname[g], cnt);
            for (size_t i = 0; i < vec.n; i++) {
                SymRec *r = &vec.v[i];
                int gg = (r->type == STT_FUNC) ? 0 : (r->type == STT_OBJECT ? 1 : 2);
                if (gg != g) continue;
                idx++;
                fprintf(tx, "[%04zu] 0x%llx  +0x%llx  %s  %s\n",
                        idx, (unsigned long long)r->vaddr, (unsigned long long)r->size,
                        type_name(r->type), bind_name(r->bind));
                if (r->runtime != r->vaddr)
                    fprintf(tx, "         runtime 0x%llx\n", (unsigned long long)r->runtime);
                fprintf(tx, "         %s\n\n", r->name);
            }
        }
        fclose(tx);
    }

    printf("[+] wrote %s/%s.symbols.tsv, .txt (via %s path)\n", outdir, soname, via);
    printf("    class=%s symtab=%llu dynsym=%llu total=%zu FUNC=%llu OBJECT=%llu\n",
           is64 ? "ELF64" : "ELF32", (unsigned long long)n_sym, (unsigned long long)n_dyn,
           vec.n, (unsigned long long)nf, (unsigned long long)no);
    free(vec.v);
    return 0;
}

/* ================= STATIC ================= */

static int parse_static(const char *sopath, const char *outdir, const char *soname)
{
    int fd = open(sopath, O_RDONLY);
    if (fd < 0) { fprintf(stderr, "[!] open %s: %s\n", sopath, strerror(errno)); return 1; }
    struct stat st;
    if (fstat(fd, &st) != 0 || st.st_size < 64) { fprintf(stderr, "[!] bad file\n"); close(fd); return 1; }
    size_t fsz = (size_t)st.st_size;
    const uint8_t *m = (const uint8_t *)mmap(NULL, fsz, PROT_READ, MAP_PRIVATE, fd, 0);
    if (m == MAP_FAILED) { fprintf(stderr, "[!] mmap failed\n"); close(fd); return 1; }
    int rc = parse_elf_data(m, fsz, sopath, 0, outdir, soname, 0);
    munmap((void *)m, fsz);
    close(fd);
    return rc;
}

/* ================= MEMORY IMAGE ================= */

typedef struct { unsigned long long start, end, off; } MemRange;

static uint8_t *read_so_from_mem(pid_t pid, const char *soname, size_t *out_size,
                                 uint64_t *out_bias, char *pathout, size_t pathcap)
{
    char p[64];
    snprintf(p, sizeof p, "/proc/%d/maps", pid);
    FILE *f = fopen(p, "r");
    if (!f) { fprintf(stderr, "[!] cannot open %s\n", p); return NULL; }

    MemRange *rr = NULL;
    size_t nr = 0, cr = 0;
    char line[4200];
    size_t slen = strlen(soname);
    static const char DEL[] = " (deleted)";
    size_t dl = sizeof DEL - 1;
    unsigned long long maxend = 0;
    int first = 1;
    uint64_t bias = 0;
    pathout[0] = 0;

    while (fgets(line, sizeof line, f)) {
        unsigned long long start = 0, end = 0, off = 0, inode = 0;
        unsigned dmaj = 0, dmin = 0;
        char perms[16] = {0}, path[4096] = {0};
        int n = sscanf(line, "%llx-%llx %15s %llx %x:%x %llu %4095s",
                       &start, &end, perms, &off, &dmaj, &dmin, &inode, path);
        if (n < 8) continue;
        size_t plen = strlen(path);
        if (plen > dl && strcmp(path + plen - dl, DEL) == 0) { path[plen - dl] = 0; plen -= dl; }
        if (plen < slen) continue;
        if (strcmp(path + (plen - slen), soname) != 0) continue;
        if (first) { bias = start - off; snprintf(pathout, pathcap, "%s", path); first = 0; }
        if (nr == cr) {
            cr = cr ? cr * 2 : 64;
            MemRange *tmp = realloc(rr, cr * sizeof(MemRange));
            if (!tmp) { fprintf(stderr, "[!] oom\n"); fclose(f); free(rr); return NULL; }
            rr = tmp;
        }
        rr[nr].start = start; rr[nr].end = end; rr[nr].off = off;
        if (off + (end - start) > maxend) maxend = off + (end - start);
        nr++;
    }
    fclose(f);
    if (!nr) { fprintf(stderr, "[!] %s not found in pid %d maps\n", soname, (int)pid); free(rr); return NULL; }

    size_t sz = (size_t)maxend;
    uint8_t *buf = calloc(1, sz);
    if (!buf) { fprintf(stderr, "[!] oom for %zu bytes\n", sz); free(rr); return NULL; }

    char mp[64];
    snprintf(mp, sizeof mp, "/proc/%d/mem", pid);
    int mfd = open(mp, O_RDONLY);
    if (mfd < 0) {
        fprintf(stderr, "[!] cannot open %s: %s\n", mp, strerror(errno));
        free(buf); free(rr); return NULL;
    }

    size_t ok = 0, covered = 0;
    long badpages = 0;
    for (size_t i = 0; i < nr; i++) {
        unsigned long long a = rr[i].start, o = rr[i].off;
        size_t len = (size_t)(rr[i].end - rr[i].start);
        if (o >= sz) continue;
        if (o + len > sz) len = (size_t)(sz - o);
        ssize_t got = pread(mfd, buf + o, len, (off_t)a);
        if (got == (ssize_t)len) { ok += len; covered += len; continue; }
        for (size_t k = 0; k < len; k += 4096) {
            size_t pl = (len - k < 4096) ? (len - k) : 4096;
            ssize_t g2 = pread(mfd, buf + o + k, pl, (off_t)(a + k));
            if (g2 > 0) ok += (size_t)g2;
            else badpages++;
        }
    }
    close(mfd);
    fprintf(stderr, "[*] mem image: %zu ranges, %zu bytes ok, %ld pages skipped, span %zu bytes\n",
            nr, ok, badpages, sz);
    free(rr);
    *out_size = sz;
    *out_bias = bias;
    return buf;
}

static const char *bn_of(const char *p)
{
    const char *s = strrchr(p, '/');
    return s ? s + 1 : p;
}

/* ================= MAIN ================= */

int main(void)
{
    /* ============ output dir (editable) ============ */
    const char *outdir = "/storage/emulated/0/DUMP";
    /* ============================================== */

    char line[4096];

    printf("============================================\n");
    printf("  ELF 符号解析器\n");
    printf("  0 = 静态解析（输入 so 文件路径，走 SECTION 节表）\n");
    printf("  1 = 动态解析（输入包名 + so 名，走 PROGRAM 段表）\n");
    printf("  输出目录: %s\n", outdir);
    printf("============================================\n");
    printf("请选择 [0/1]: ");
    fflush(stdout);
    if (!fgets(line, sizeof line, stdin)) return 1;
    line[strcspn(line, "\r\n")] = 0;
    int mode = atoi(line);

    if (mode == 0) {
        printf("请输入 so 文件路径: ");
        fflush(stdout);
        if (!fgets(line, sizeof line, stdin)) return 1;
        line[strcspn(line, "\r\n")] = 0;
        if (!line[0]) { fprintf(stderr, "[!] empty path\n"); return 2; }
        printf("[*] STATIC 文件 = %s\n", line);
        return parse_static(line, outdir, bn_of(line));
    }

    if (mode == 1) {
        char pkg[512], so[512];
        printf("请输入进程包名: ");
        fflush(stdout);
        if (!fgets(pkg, sizeof pkg, stdin)) return 1;
        pkg[strcspn(pkg, "\r\n")] = 0;
        printf("请输入 so 名: ");
        fflush(stdout);
        if (!fgets(so, sizeof so, stdin)) return 1;
        so[strcspn(so, "\r\n")] = 0;
        if (!pkg[0] || !so[0]) { fprintf(stderr, "[!] empty input\n"); return 2; }

        printf("[*] DYNAMIC 包名=%s so=%s\n", pkg, so);
        pid_t pid = find_pid(pkg);
        if (pid <= 0) { fprintf(stderr, "[!] process '%s' not running\n", pkg); return 2; }
        printf("[+] pid = %d\n", (int)pid);

        size_t sz = 0;
        uint64_t bias = 0;
        char spath[4096];
        uint8_t *buf = read_so_from_mem(pid, so, &sz, &bias, spath, sizeof spath);
        if (!buf) return 2;
        printf("[+] loaded = %s @ bias 0x%llx\n", spath, (unsigned long long)bias);

        int rc = parse_elf_data(buf, sz, spath, bias, outdir, bn_of(so), 1);
        free(buf);
        return rc;
    }

    fprintf(stderr, "[!] invalid choice\n");
    return 2;
}