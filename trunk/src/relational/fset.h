/* defines */
#define LENGTH        32
#define fempty(f)     (!memcmp ((f), emptyset, sizeof(FSET)))
#define fcopy(s1,s2)  (memcpy ((s1), (s2), sizeof (FSET)))


/* structs and typedefs */
typedef unsigned short FSET[LENGTH];


/* extern */
extern FSET emptyset;


/* prototypes */
void finit  (void);
void funion (register FSET, register FSET, register FSET);
void finter (register FSET, register FSET, register FSET);
void fins   (register unsigned short, register FSET, register FSET);
void fdel   (register unsigned short, register FSET, register FSET);
int  fcmp   (register FSET, register FSET);
void fout   (register FILE *, register FSET);
