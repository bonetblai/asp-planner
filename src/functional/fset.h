/* defines */
#define LENGTH        32
#define MASK          65535
#define fempty(f)     (!memcmp ((f), emptyset, sizeof(FSET)))
#define fcopy(s1,s2)  (memcpy ((s1), (s2), sizeof (FSET)))


/* structs and typedefs */
typedef unsigned int FSET[LENGTH];


/* extern */
extern FSET emptyset;


/* prototypes */
void  finit   (void);
void  funion  (register FSET, register FSET, register FSET);
void  finter  (register FSET, register FSET, register FSET);
void  fins    (register unsigned short, register FSET, register FSET);
void  fdel    (register unsigned int, register FSET, register FSET);
int   fcmp    (register FSET, register FSET);
int   fcomm   (register FSET, register FSET);
void  fucost  (register unsigned short, register FSET, register FSET);
void  fbcost  (register unsigned short, register FSET, register FSET);
short fcost   (register FSET, register FSET);
short focost  (register FSET, register FSET);
int   feother (register unsigned int, register FSET);
short ffirst  (register FSET);
#if 0
void  fout    (register FILE *, register FSET);
#endif
