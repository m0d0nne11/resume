
/*
 * ----------------------------------------------------------------------------
 * FILE clufmirror.c
 * Provided to customers as example usage of NetGuard API
 *
 * Usage:
 *      thisProg -f filename [-w] [-v]
 *
 * -f filename
 * -w write local file to DataSpace (once) instead of reading
 * -v verbose
 * -m mark the metadata with current Quorum View Number (one-shot)
 *
 * A NetGuard file-mirroring utility, part of the NetGuard clustering
 * infrastructure.  Allows files to be mirrored across multiple nodes such
 * that applications (particularly legacy apps) can find their data on the
 * destination node after failover.
 *
 * Oversimplified, this mirroring consists of:
 *  - The single node currently designated as "Writer" pushing
 *    a copy of the mirrored file into a NetGuard DataSpace (DS)
 *    when (via FAM) local changes are noticed.
 *  - Zero or more "Reader" nodes then pulling the contents of
 *    that DS into their local copies of the mirrored file.
 *
 * All parties rendezvous via a (non-persistent) DS holding the "metadata"
 * for the mirrored file.  When changes to those metadata are noticed each
 * party uses those metadata to decide whether to update their local copy
 * of the mirrored file.
 *
 * The actual file data are stored in a separate, unmonitored DS - only
 * metadata DS events are monitored.  The metadata DS and the fileData DS
 * can only be modified under protection of a NetGuard lock.  The names of
 * the lock and both DataSpaces are derived as MD5 hashes of the pathname
 * string of the mirrored file.  An MD5 hash is used because it can be
 * computed for data of any size and any value and is strong enough that,
 * for our purposes, it can be considered "perfect".  All parties can
 * therefore independently compute the names of these entities (as long as
 * they know the pathname of the mirrored file) without having to consult
 * some sort of directory.
 *
 * The metadata includes an MD5 hash of the actual file as well as a
 * "stat" struct.  The readers can decide whether to actually write the
 * DS contents into their local copies of the mirrored file by comparing
 * their own locally computed metadata to those in the DS.
 *
 * This program runs by default in Read mode.  Multiple nodes can all
 * have Readers minding the (local instance of the) specified file, and
 * multiple Readers can execute simultaneously on the same node minding
 * different files.  Multiple Readers can even execute simultaneously on
 * the same node minding the same file: this should merely be a pointless
 * thing to do, rather than being actually harmful.
 *
 * This program can also be run in Write mode where the contents of the
 * specified local file are pushed into the corresponding DS, usually as
 * the result of some local modification having been detected by means of
 * some other facility such as dnotify or FAM.
 *
 * Note that it should (eventually) be possible to coordinate modifications
 * to files that have different local pathnames on various nodes by
 * specifying a local pathname and also a 'canonical' pathname.  The metadata
 * DS would be identified by the canonical pathname while the local file
 * might have a different pathname.
 */

#include <errno.h>
#include <fcntl.h>
#include <netinet/in.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/param.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>
#include <signal.h>

#include <defs.h>
#include <syslog.h>
#include <logger.h>
#include <ngconfig.h>
#include <netg_api.h>
#include "fam.h"

typedef int bool;


void handleFAMevent(FAMEvent* fe);

struct clucfg *cinfo;
extern char    *optarg;
extern int      optind;



/*
 * For use with one-dimensional arrays whose size is known at compile time:
 */
#define ARRAY_INDEX_LIMIT( array )   (sizeof((array)) / sizeof(((array)[0])))
#define ARRAY_POINTER_LIMIT( array ) (&((array)[ ARRAY_INDEX_LIMIT(array) ]))

typedef   __int8_t  s8;
typedef  __int16_t s16;
typedef  __int32_t s32;
typedef  __uint8_t  u8;
typedef __uint16_t u16;
typedef __uint32_t u32;


/*
 * ----------------------------------------------------------------------------
 */
void
setupConfig(
    void     )
{
    if( parse_config( CLUSTER_CFGFILE ) < 0 )  {
        clulog( LOG_CRIT, "main: Unable to parse config data!  %s",
            strerror( errno ) );
        FAULT();
    }

    cinfo = getclucfg();                        /* fill in the global cinfo. */
    if( !cinfo )  {
        clulog( LOG_CRIT, "main: Unable to retrieve cluster "
            "config info." );
        FAULT();
    }
}


/*
 * ----------------------------------------------------------------------------
 */
void
sigterm_handler(
    int __attribute__((unused))signo )
{
    clulog( LOG_CRIT, "%s: Hi, Mom!\n", __FUNCTION__ );
}


int
setup_signals(
    void       )
{
    sigset_t         set;
    struct sigaction act;


    signal( SIGPIPE,  SIG_IGN );
    signal( SIGWINCH, SIG_IGN );
    signal( SIGTTIN,  SIG_IGN );
    signal( SIGTTOU,  SIG_IGN );

    sigemptyset(    &set );
    sigaddset(      &set, SIGTERM );
    act.sa_mask    = set;
    act.sa_handler = sigterm_handler;
    act.sa_flags   = SA_NOCLDSTOP | SA_RESTART;
    if( sigaction( SIGTERM, &act, NULL ) < 0 )  {
        clulog( LOG_CRIT, "%s: sigaction SIGTERM failed %s",
                         __FUNCTION__, strerror( errno ) );
        return( -1 );
    }

    sigemptyset(    &set );
    sigaddset(      &set, SIGCHLD );
    act.sa_mask    = set;
    act.sa_handler = SIG_DFL;
    act.sa_flags   = SA_RESTART;
    if( sigaction( SIGCHLD, &act, NULL ) < 0 )  {
        clulog( LOG_CRIT, "%s: sigaction SIGCHLD failed %s",
                         __FUNCTION__, strerror( errno ) );
        return( -1 );
    }

    return( 0 );
}


/*
 * ----------------------------------------------------------------------------
 * FAM debugging stuff.
 */
char *
eventTypeString(
    int code     )
{
  static
    char *stringFor[] = {
        "<unknown>",
        "FAMChanged ",
        "FAMDeleted ",
        "FAMStartExecuting ",
        "FAMStopExecuting ",
        "FAMCreated ",
        "FAMMoved ",
        "FAMAcknowledge ",
        "FAMExists ",
        "FAMEndExist ",
    };

    if( (code < 0)  ||  (code >= ARRAY_INDEX_LIMIT( stringFor )) )  {
        code = 0;
    }

    return( stringFor[ code ] );
}


/*
 * ----------------------------------------------------------------------------
 */
typedef struct md5hashStruct  {
    u32 datum[ 4 ];   /* Simply a way to carry 128 bits around in one bundle */
} md5hash;

md5hash nullMD5hash = { { 0, 0, 0, 0, } };

#define IS_NULL_MD5( hash )     !md5hashCompare( &nullMD5hash, (hash) )


/*
 * - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
 */
typedef struct statusSnapshotStruct  {
    struct stat stat;            /* Most recent lstat(), st_mtime:0 == never */
    md5hash     hash;    /* Last MD5 hash computed for this file, 0 == never */
    s32         writer;           /* Which netG node generated this snapshot */
} statusSnapshot;

typedef struct pathNameStruct  {
    char specified[ MAXPATHLEN + 1 ];  /* 4096 (!) bytes + 1, including NULL */
    char canonical[ MAXPATHLEN + 1 ];
} pathNames;

/*
 * - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
 * This defines layout of the Metadata DS
 */
typedef struct metadataStruct  {
    u32            magic;                                  /* RFD_META_MAGIC */
    statusSnapshot current;                 /* Describes current DS contents */
    u32            entries;    /* High-water mark for node[] - 0 means none. */
    pathNames      path;
    size_t         size;                     /* sizeof( header plus snap[] ) */
    u32            view; /* Increment atomically whenever current is changed */
    s32            writer;            /* Node currently designated as writer */
    statusSnapshot snap[ 0 ];    /* Variable sized array of per-node entries */
} metadata;

#define RFD_META_MAGIC 0xdebac1e5

/*
 * - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
 * Just a big bag'o'bits as an alternative to these all having global scope...
 */
typedef struct globalStruct  {
    struct  {                                            /* file descriptors */
        int file;                                 /* The actual on-disk file */
        int meta;                               /* metaData dataspace events */
        int member;                                     /* membership events */
    } fd;

    struct  {
        char D[ 40 ];                              /* The actual fileData DS */
        char L[ 40 ];                                                /* Lock */
        char M[ 40 ];                                     /* DS for metaData */
    } DStag;                                /* Derived from MD5 hash of path */

    struct  {
        netg_lk_handle *lock;                        /* Protects metadata DS */
        netg_ds_handle *meta;
        netg_mb_handle *member;
    } handle;

    pathNames      path;
    statusSnapshot snap;            /* Most recent locally obtained snapshot */
    void          *fileData;
    ds_event_t     metaEvent;
    dataspace_t    metaSpace;
    mb_state_t     memberState;
    int            verbose;
    int            writeDS;
    int            resigning;         /* If this node is the Writer, stop it */
    int            thisNode;
    u32            metaView;                /* Last metadata.view we noticed */

    struct  {
        FAMConnection connection;
        FAMEvent      event;
        FAMRequest    request;
    } fam;
} global;


/*
 * ----------------------------------------------------------------------------
 * Something is squonky about libcrypt.a - I can't get it to link
 * using the normal "-lcrypt" idiom; instead, the actual full pathname
 * of the library file has to be mentioned on the linker command line.
 * Further, I don't know why the exported symbol name for the md5_buffer()
 * function has to have a "__" prepended since I don't see that in the
 * sources for glibc.  Anyway, for the time being we need this:
 */
#define XXX_MIKE_STILL_BAFFLED LAST_TIME_ANYBODY_CHECKED
#if     XXX_MIKE_STILL_BAFFLED
#define md5_buffer __md5_buffer
#endif                                         /* #if XXX_MIKE_STILL_BAFFLED */

extern void *md5_buffer( const char *, size_t, void * );

/*
 * - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
 */
int md5hashCompare(
    md5hash *a,
    md5hash *b      )
{
    int      i;

    for( i = 0;  i < ARRAY_INDEX_LIMIT( a->datum );  ++i )  {
        if( a->datum[ i ] != b->datum[ i ] )  {  /* XXX_MIKE - use htonl() ? */
            return( (a->datum[ i ] < b->datum[ i ])?  -1: 1 );
        }
    }
    return( 0 );
}


/*
 * - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
 */
char *
md5asciiHashStringForHash(
    md5hash *hash,
    char    *result        )   /* Must be at least 33 bytes long (32 + NULL) */
{
    sprintf( result, "%08x%08x%08x%08x", htonl( hash->datum[ 0 ] ),
                                         htonl( hash->datum[ 1 ] ),
                                         htonl( hash->datum[ 2 ] ),
                                         htonl( hash->datum[ 3 ] )  );
    return( result );
}


/*
 * - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
 * Compute the MD5 hash of the specified data and generate
 * a string of ASCII hex numerals representing that hash.
 */
char *
md5asciiHashStringForData(
    void   *data,
    size_t  size,
    char   *result         )   /* Must be at least 33 bytes long (32 + NULL) */
{
    md5hash hash;

    md5_buffer( data, size,  (void *)&hash );
    return( md5asciiHashStringForHash( &hash, result )  );
}


/*
 * - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
 * Compute length of specified NULL-terminated string and return
 * the ASCII hex representation of its MD5 hash.  The NULL is
 * not considered to be one of the data used to compute the hash...
 */
char *
md5asciiHashStringForString(
    char   *string,
    char   *result           ) /* Must be at least 33 bytes long (32 + NULL) */
{
    return( md5asciiHashStringForData( string, strlen( string ), result )  );
}


#ifdef  XXX_MIKE_DEBUGGING_ROUTINES_ENABLED
/*
 * ----------------------------------------------------------------------------
 * Just some debugging stuff.
 */

int triggerAbort;

void
trigger(
    int error )
{
    if( !error )  {
        return;
    }
    clulog( LOG_CRIT, "TRIGGER %d\n", error );
    if( error < 0 )  {
        if( triggerAbort < 0 )  {
            abort();
        }
        return;
    }
    if( triggerAbort > 0 )  {                           /* We know error > 0 */
        abort();
    }
}

/*
 * ----------------------------------------------------------------------------
 * More debugging stuff.
 */
void
showStatusSnapshot(
    statusSnapshot *snap,
    FILE           *stream,
    char           *prefix )
{
    md5hash        *hash;
    char            hashString[ 48 ];
    struct stat    *status;


    if( !prefix )  {
        prefix = "";
    }
    hash = &(snap->hash);
    status = &(snap->stat);

    fprintf( stream, "%ssnap[0x%08x]->MD5hash:           %s\n",
                      prefix, (unsigned int)snap,
                      md5asciiHashStringForHash( hash, hashString )  );

    fprintf( stream, "%ssnap[0x%08x]->view:              0x%08x\n",
                      prefix, (unsigned int)snap,
                      (unsigned int)(snap->view)                     );

    fprintf( stream, "%ssnap[0x%08x]->writer             0x%08x\n",
                      prefix, (unsigned int)snap,
                      (unsigned int)(snap->writer)                   );

    fprintf( stream, "%ssnap[0x%08x]->status.st_dev:     0x%08llx\n",
                      prefix, (unsigned int)snap,
                      status->st_dev                                   );

    fprintf( stream, "%ssnap[0x%08x]->status.st_ino:     0x%08lx\n",
                      prefix, (unsigned int)snap,
                      status->st_ino                                   );

    fprintf( stream, "%ssnap[0x%08x]->status.st_mode:    0%011o\n",
                      prefix, (unsigned int)snap,
                      status->st_mode                                  );

    fprintf( stream, "%ssnap[0x%08x]->status.st_nlink:   0x%08x\n",
                      prefix, (unsigned int)snap,
                      status->st_nlink                                 );

    fprintf( stream, "%ssnap[0x%08x]->status.st_uid:     0x%08x/%u\n",
                      prefix, (unsigned int)snap,
                      status->st_uid, status->st_uid                     );

    fprintf( stream, "%ssnap[0x%08x]->status.st_gid:     0x%08x/%u\n",
                      prefix, (unsigned int)snap,
                      status->st_gid, status->st_gid                     );

    fprintf( stream, "%ssnap[0x%08x]->status.st_rdev:    0x%08llx\n",
                      prefix, (unsigned int)snap,
                      status->st_rdev                                  );

    fprintf( stream, "%ssnap[0x%08x]->status.st_size:    0x%08lx/%lu\n",
                      prefix, (unsigned int)snap,
                      status->st_size, status->st_size                   );

    fprintf( stream, "%ssnap[0x%08x]->status.st_blksize: 0x%08lx/%lu\n",
                      prefix, (unsigned int)snap,
                      status->st_blksize, status->st_blksize             );

    fprintf( stream, "%ssnap[0x%08x]->status.st_blocks:  0x%08lx/%lu\n",
                      prefix, (unsigned int)snap,
                      status->st_blocks, status->st_blocks               );

    fprintf( stream, "%ssnap[0x%08x]->status.st_atime:   0x%08lx/%lu\n",
                      prefix, (unsigned int)snap,
                      status->st_atime, status->st_atime                 );

    fprintf( stream, "%ssnap[0x%08x]->status.st_mtime:   0x%08lx/%lu\n",
                      prefix, (unsigned int)snap,
                      status->st_mtime, status->st_mtime                 );

    fprintf( stream, "%ssnap[0x%08x]->status.st_ctime:   0x%08lx/%lu\n",
                      prefix, (unsigned int)snap,
                      status->st_ctime, status->st_ctime                 );
}


/*
 * ----------------------------------------------------------------------------
 * More debugging stuff.
 */
void
showMetadata(
    metadata *meta,
    FILE     *stream,
    char     *prefix  )                                   /* caller's prefix */
{
    int       i;
    char      indentation[ 100 ];


    if( !prefix )  {
        prefix = "";
    }

    strcpy( indentation, "  " );
    strcat( indentation, prefix );

    fprintf( stream, "%smeta[0x%08x]->magic:         0x%08x\n",
                       prefix, (unsigned int)meta, (unsigned int)meta->magic );

    fprintf( stream, "%smeta[0x%08x]->name.specified:<%s>\n",
                       prefix, (unsigned int)meta, meta->name.specified      );

    fprintf( stream, "%smeta[0x%08x]->name.canonical:<%s>\n",
                       prefix, (unsigned int)meta, meta->name.canonical      );

    showStatusSnapshot( &(meta->current), stream, indentation                );

    fprintf( stream, "%smeta[0x%08x]->writer:        %d\n",
                       prefix, (unsigned int)meta, (int)meta->writer         );

    fprintf( stream, "%smeta[0x%08x]->entries:       %d\n",
                       prefix, (unsigned int)meta, (int)meta->entries        );

    fprintf( stream, "%smeta[0x%08x]->size:          %d\n",
                       prefix, (unsigned int)meta, (int)meta->size           );
    for( i = 0;  i < meta->entries;  ++i )  {
        fprintf( stream, "%smeta[0x%08x]->snap[ %2d ]:\n",
                           prefix, (unsigned int)meta, i                     );
        showStatusSnapshot( &(meta->snap[ i ]), stream, indentation          );
    }
}
#endif                         /* #ifdef XXX_MIKE_DEBUGGING_ROUTINES_ENABLED */


/*
 * ----------------------------------------------------------------------------
 * Given a pointer to a metadata pointer, verify that the metadata in
 * question have a snap[] array large enough to hold the specified number
 * of entries.  If necessary we'll (re)allocate the required space and free
 * the old one.  This only involves in-memory operations - no DS accesses.
 */
int
extendMetadataMem(
    metadata **metaP,
    u32        count  )           /* Extend to hold this many snap[] entries */
{
    int        error;
    metadata  *meta;
    void      *newMeta;
    size_t     newSize;
    size_t     oldSize;


    newSize =  sizeof(*meta) + (count * sizeof(meta->snap[0]));
    meta    = *metaP;
    if( !meta )  {
        meta          = calloc( newSize, 1 );  /* XXX_MIKE - error checking? */
        meta->magic   = RFD_META_MAGIC;
        meta->entries = count;
        meta->writer  = ~0;
        meta->view    = ~0;
        meta->size    = newSize;
        *metaP        = meta;
    }

    error   = 0;
    oldSize = sizeof(*meta) + (meta->entries * sizeof(meta->snap[0]));
    if( newSize > oldSize )  {      /* Never true when *metaP initially NULL */
        newMeta = calloc( newSize, 1 );
        if( newMeta )  {
            memcpy( newMeta, meta, oldSize );
            free( meta );
            meta          = (metadata *)newMeta;
            meta->entries = count;
            meta->size    = newSize;
            *metaP        = meta;
        } else  {                                          /* calloc() error */
            error = ENOMEM;
        }
    }

    return( error );
}


/*
 * ----------------------------------------------------------------------------
 * Update the specified entry in the specified in-memory
 * copy of metadata after ensuring that there's enough space.
 * We also update the notion of who's the "official" writer.
 */
int
updateMetadataEntryMem(
    metadata      **meta,
    s32             i,
    statusSnapshot *entry  )
{
    int             error;


    error = extendMetadataMem( meta, (i + 1) );
    if( !error )  {
        (*meta)->current   = *entry;                       /* Structure-copy */
        (*meta)->snap[ i ] = *entry;                       /* Structure-copy */
        (*meta)->writer    =  i;            /* This writer is now "official" */
        (*meta)->view++;                      /* Indicate change in metadata */
    }

    return( error );
}


/*
 * ----------------------------------------------------------------------------
 * Open the indicated file, gather its stat info and read the file
 * into a buffer allocated for the purpose.  Store the MD5 hash of
 * that buffer in the specified statusSnapshot and then discard that
 * buffer unless the caller indicated that we're to preserve it.
 *
 * RETURN: 0 on success
 */
int
snapshotFileState(
    global         *g,
    void          **fileDataP )       /* Nonzero if we're to retain the data */
{
    int             error;
    int             fd;
    void           *fileData;
    char           *name;
    int             result;
    int             size;
    statusSnapshot *snap;


    if( fileDataP )  {
        *fileDataP = 0;                                       /* In any case */
    }

    fd       = -1;
    fileData =  0;
    error    =  0;
    result   =  0;

    if( !g  ||  !(g->path.specified)  )  {
        result = EINVAL;
        goto exit;
    }

    name =   g->path.specified;
    snap = &(g->snap);
    memset( snap, 0, sizeof(*snap)  );
    snap->writer = ~0;

    fd = open( name, O_RDONLY );
    if( fd < 0 )  {
        clulog( LOG_CRIT, "(%s:%d)open(%s) errno:%d\n",
              __FUNCTION__, __LINE__, name, errno );
        result = errno;
        goto exit;
    }

    error = fstat( fd, &(snap->stat) );
    if( error )  {
        clulog( LOG_CRIT, "(%s:%d)fstat(%s) errno:%d\n",
              __FUNCTION__, __LINE__, name, errno );
        result = errno;
        goto exit;
    }

    fileData = malloc( snap->stat.st_size );
    if( !fileData )  {
        clulog( LOG_CRIT, "(%s:%d)malloc() errno:%d\n",
              __FUNCTION__, __LINE__, errno );
        result = errno;
        goto exit;
    }

    size = read( fd, fileData, snap->stat.st_size );
    if( size != snap->stat.st_size )  {
        clulog( LOG_CRIT, "(%s:%d)read(%s) errno:%d\n",
              __FUNCTION__, __LINE__, name, errno );
        result = errno;
        goto exit;
    }

    md5_buffer( fileData, size, (void *)&(snap->hash) );

    if( fileDataP )  {                     /* Caller wants data kept around, */
        *fileDataP = fileData;               /* so let him know where it is. */
        fileData   = 0;                             /* Don't free() it below */
    }

    snap->writer = g->thisNode;
exit:
    if( fd >= 0 )  {
        close( fd );
    }
    if( fileData )  {
        free( fileData );
    }
    return( result );
}


/*
 * ----------------------------------------------------------------------------
 * Read the metadata, transfer our private snapshot into
 * it and then push the new metadata back out to the DS.
 *
 * ASSUME: lock currently held
 */
int
pushMetadataEntry(
    global         *g )
{
    int             error;
    metadata       *meta;
    netg_ds_handle *metaHandle;
    dataspace_t    *metaSpace;
    int             result;


    metaHandle = g->handle.meta;
    if( !metaHandle )  {
        result = EINVAL;
        goto exit;
    }

    metaSpace = &(g->metaSpace);                /* dataspace_t resident in g */
    error     = ds_read( metaHandle, metaSpace );
    if( error )  {
        clulog( LOG_CRIT, "(%s:%d)ds_read() error:%d\n",
              __FUNCTION__, __LINE__, error );
        result = error;
        goto exit;
    }

    /*
     * Note: updateMetadataEntryMem() writes the specified snapshot
     * into the "main" entry as well as our particular slot in the
     * snap[] array.  It also increments the snapshot view number so
     * we'd better be holding the lock for that operation to be atomic.
     *
     * NOTE: dataspace_t.buf_size :: totalAllocatedBufferSize
     *       dataspace_t.db_size  :: bytesActuallyPresent
     */
    meta  = (metadata *)(metaSpace->data);
    error = updateMetadataEntryMem( &meta, g->thisNode, &(g->snap)  );
    if( error  ||  !meta )  {
        result = error;
        goto exit;
    }

    metaSpace->data    = (void *)meta;         /* Possibly different buffer? */
    metaSpace->db_size = metaSpace->buf_size = meta->size;

    result = ds_write( metaHandle, metaSpace );
    if( !result )  {
        g->metaView = meta->view;   /* Remember most recent view if no error */
    }

exit:
    return( result );
}


/*
 * ----------------------------------------------------------------------------
 * We're holding the metadata lock, we have a current buffer from
 * the metadata DS and a current snapshot from our file.  We see that
 * the snapshot in the metadata is different from our local snapshot,
 * so we'll pull the contents of the "file-data" dataspace and write
 * it to the file.
 *
 * TODO: handle case where local file doesn't yet exist.
 */
int
phase5meta(
    global         *g )
{
    netg_ds_handle *dataHandle;
    dataspace_t     dataSpace;
    int             error;
    int             fd;
    char           *name;
    int             result;
    int             shouldUpdate;
    int             size;


    dataHandle   =  0;
    result       =  0;
    shouldUpdate =  0;
    name         =  g->path.specified;
    fd           = -1;

    dataHandle = ds_open( g->DStag.D, 0, &error);       /* Not DS_PERSISTENT */
    if( !dataHandle  ||  error )  {
        result = error;
        goto exit;
    }

    ds_descriptor_init( &dataSpace );
    error = ds_read( dataHandle, &dataSpace );
    if( error )  {        /* XXX_MIKE - could this ever be DS_READ_NO_STATE? */
        result = error;
        goto exit;
    }

    fd = open( name, (O_RDWR|O_TRUNC) );         /* XXX_MIKE - use O_CREAT ? */
    if( fd < 0 )  {
        result = errno;
        perror( name );
        goto exit;
    }

    size = write( fd, dataSpace.data, dataSpace.db_size );
    if( size != dataSpace.db_size )  {
        result = errno;
        perror( "write" );
        goto exit;
    }

if( g->verbose )  {                                             /* DEBUGGING */
    char buf[ 50 ];
    metadata *meta = (metadata *)(g->metaSpace.data);

    md5asciiHashStringForHash( &(meta->current.hash), buf );
    fprintf( stderr, "(%s:%d)%s %u bytes\n",
                     __FUNCTION__, __LINE__, buf, dataSpace.db_size );
}

exit:
    if( fd >= 0 )  {
        close( fd );
    }
    ds_close( dataHandle );                               /* OK even if NULL */
    return( result );
}


/*
 * ----------------------------------------------------------------------------
 * metadata DS and lock are open, got a metadata DS_WRITE event.
 */
int
phase4meta(
    global         *g )
{
    int             error;
    netg_lk_handle *lockHandle;
    metadata       *meta;
    netg_ds_handle *metaHandle;
    dataspace_t    *metaSpace;
    int             result;


    result     = 0;
    lockHandle = 0;

    lockHandle = g->handle.lock;
    if( !lockHandle )  {
        result = EINVAL;
        goto exit;
    }
    error = lk_lock( lockHandle );
    if( error )  {
        result = error;
        goto exit;
    }

    metaHandle = g->handle.meta;
    if( !metaHandle )  {
        result = EINVAL;
        goto exit;
    }

    metaSpace = &(g->metaSpace);
    error     = ds_read( metaHandle, metaSpace );
    if( error )  {
        result = error;
        goto exit;
    }

    /*
     * After we've read the metadata DS we perform a few checks before
     * heading off to pull the fileData DS into the local file.
     *
     * First, there's a test to detect a mismatch between the role (Reader
     * versus Writer) we were launched in versus the role this node is
     * currently marked as playing.  We exit immediately if mismatch is
     * detected since those roles can't coexist peacefully on one node.
     *
     * Then we compare the snapshot view number with the last one we
     * remember seeing and don't bother any further if they're the same.
     *
     * Finally we acquire a local snapshot and verify that our snapshot
     * differs from the one in the metadata.
     *
     * XXX_MIKE - probably need a way to override this after a crash...
     */
    meta = (metadata *)(metaSpace->data);
    if( !(g->writeDS)  ==  (meta->writer == g->thisNode) )  {   /* Mismatch? */
        exit( 0 );          /* ASSUME: locks & dataspaces cleaned up on exit */
    }

    if( g->metaView == meta->view )  {
        goto exit;           /* We've seen this snapshot, so we're done here */
    }
    g->metaView = meta->view;               /* Remember latest snapshot view */

    error = snapshotFileState( g, 0 );
    if( error )  {
        result = error;
        goto exit;
    }

    if( md5hashCompare( &(g->snap.hash), &(meta->current.hash) ) )  {
        error = phase5meta( g );      /* Try to update file from fileData DS */
        if( error )  {
            result = error;
            goto exit;
        }
    }

exit:
    lk_unlock( lockHandle );                  /* XXX_MIKE - blind unlock OK? */
    return( result );
}


/*
 * ----------------------------------------------------------------------------
 * The metadata DS and lock are open and we got a FAM event notification, so
 * we open the fileData dataspace (protected by the lock) and push the local
 * file data into it, then update the metadata dataspace and drop the lock.
 *
 * ASSUME: this event associated with the file we're interested in...
 */
int
phase4fam(
    global         *g )
{
    netg_ds_handle *dataHandle;
    dataspace_t     dataSpace;
    int             error;
    FAMEvent       *event;
    void           *fileData;
    netg_lk_handle *lockHandle;
    int             result;
static
    int             eventCount = 0;


    event      = &(g->fam.event);
    dataHandle = 0;
    fileData   = 0;
    lockHandle = 0;
    result     = 0;

    ++eventCount;
    error = FAMNextEvent( &(g->fam.connection), &(g->fam.event) );
    if( error < 0 )  {
        clulog( LOG_CRIT, "(%s:%d)FAMNextEvent() error:%d\n",
              __FUNCTION__, __LINE__, error );
        result = error;
        goto exit;
    }
    if( g->verbose )  {
        clulog( LOG_CRIT, "(%s:%d)%s eventCount:%d\n",
            __FUNCTION__, __LINE__, eventTypeString(event->code), eventCount );
    }

    switch( event->code )  {
    case FAMExists:                            /* Legit, but we ignore these */
    case FAMEndExist:                          /* Legit, but we ignore these */
    case FAMStartExecuting:                    /* Legit, but we ignore these */
    case FAMStopExecuting:                     /* Legit, but we ignore these */
    case FAMCreated:             /* Only for files in monitored directories? */
    case FAMDeleted:        /* We don't propagate deletion of mirrored files */
        return( 0 );                        /* Silently ignore all the above */
    default:
    case FAMMoved:        /* per the FAM man page, this one can NEVER happen */
        clulog( LOG_CRIT, "(%s:%d)Unexpected event code:%d\n", event->code );
        return( event->code );
    case FAMChanged:                    /* Some fstat'able attribute changed */
        break;                                              /* Deal with it. */
    }

    /*
     * FAM seems to have reported an event of interest, so
     * we'll push the file contents into the filedata DS.
     */
    lockHandle = g->handle.lock;
    if( !lockHandle )  {
        clulog( LOG_CRIT, "(%s:%d)NULL lock handle\n" );
        result = EINVAL;
        goto exit;
    }
    error = lk_lock( lockHandle );
    if( error )  {
        clulog( LOG_CRIT, "(%s:%d)lk_lock(%s) error:%d\n",
              __FUNCTION__, __LINE__, g->DStag.L, error );
        result = error;
        goto exit;
    }

    dataHandle = ds_open( g->DStag.D, 0, &error);       /* Not DS_PERSISTENT */
    if( !dataHandle  ||  error )  {
        clulog( LOG_CRIT, "(%s:%d)ds_open(%s) error:%d\n",
              __FUNCTION__, __LINE__, g->DStag.D, error );
        result = error;
        goto exit;
    }

    /*
     * We could theoretically just blindly write the fileData DS
     * without first reading it in but for now this approach is
     * easier than fiddling with the dataspace_t to get it properly
     * initialized such that ds_write() would be happy with it.  XXX_MIKE
     */
    ds_descriptor_init( &dataSpace );
    error = ds_read( dataHandle, &dataSpace );
    if( error  &&  (error != DS_READ_NO_STATE) )  {
        clulog( LOG_CRIT, "(%s:%d)ds_read(%s) error:%d\n",
              __FUNCTION__, __LINE__, g->DStag.D, error );
        result = error;
        goto exit;
    }

    error = snapshotFileState( g, &fileData );   /* and please retain buffer */
    if( error )  {
        clulog( LOG_CRIT, "(%s:%d)snapshotFileState(%s) error:%d\n",
              __FUNCTION__, __LINE__, g->path.specified, error );
        result = error;
        goto exit;
    }

    if( dataSpace.data )  {
        free( dataSpace.data );          /* Blindly toss current DS contents */
    }
    dataSpace.data    = fileData;        /* Prepare to push file into the DS */
    dataSpace.db_size = dataSpace.buf_size = g->snap.stat.st_size;

    error = ds_write( dataHandle, &dataSpace );                     /* Push. */
    if( error )  {        /* XXX_MIKE - could this ever be DS_READ_NO_STATE? */
        clulog( LOG_CRIT, "(%s:%d)ds_write(%s) error:%d\n",
              __FUNCTION__, __LINE__, g->DStag.D, error );
        result = error;
        goto exit;
    }

    /*
     * OK - the file data have been transferred from the file
     * to the dataspace - now we need to update the metadata.
     * XXX_MIKE - need to guarantee that metadata always
     *            correctly describe the file-data in the DS.
     */
    result = pushMetadataEntry( g );         /* We're still holding the lock */

exit:
    if( fileData )  {
        free( fileData );
    }
    ds_close(  dataHandle );
    lk_unlock( lockHandle );                  /* XXX_MIKE - blind unlock OK? */
    return( result );
}


/*
 * ----------------------------------------------------------------------------
 * metadata DS and lock are open.
 *
 * Here we setup in preparation for monitoring various events.
 * Part of that prep is readying the FAM stuff if appropriate,
 * and also tearing it down on exit.
 */
int
phase3(
    global *g )
{
    int     error;
    int     fdMax;
    fd_set  readActive;                              /* Modified by select() */
    fd_set  readStatic;
    int     result;


    g->fam.connection.fd = -1;

    /*
     * It's now safe to register for events since we don't have
     * immediate plans to generate further ds_write() activity...
     */
    result = 0;
    error  = ds_register_for_events( g->handle.meta );
    if( error )  {
        clulog( LOG_CRIT, "(%s:%d)ds_register_for_events() error:%d\n",
              __FUNCTION__, __LINE__, error );
        result = error;
        goto exit;
    }
    g->fd.meta = ds_handle_to_fd( g->handle.meta );

    FD_ZERO(              &readStatic );
    FD_SET( g->fd.meta,   &readStatic );
    FD_SET( g->fd.member, &readStatic );
    fdMax = MAX( g->fd.meta, g->fd.member );

    if( g->writeDS )  {
        error = FAMOpen( &(g->fam.connection) );
        if( error < 0 )  {
            clulog( LOG_CRIT, "(%s:%d)FAMOpen() error:%d\n",
                  __FUNCTION__, __LINE__, error );
            result = error;
            goto exit;
        }
        FD_SET(      g->fam.connection.fd, &readStatic );
        fdMax = MAX( g->fam.connection.fd, fdMax );

        error = FAMMonitorFile( &(g->fam.connection),
                                  g->path.specified,
                                &(g->fam.request),    0 );
        if( error < 0 )  {
            clulog( LOG_CRIT, "(%s:%d)FAMMonitorFile() error:%d\n",
                  __FUNCTION__, __LINE__, error );
            result = error;
            goto exit;
        }
    }

    fdMax += 1;

    /*
     * The main event loop...
     */
    while( !result )  {
        readActive = readStatic;            /* Refresh from static snapshot. */
        error      = select( fdMax, &readActive, NULL, NULL, NULL );
        if( error < 0 )  {
            if( errno != EINTR )  {
                clulog( LOG_CRIT, "(%s:%d)select() errno:%d\n",
                      __FUNCTION__, __LINE__, errno );
                result = errno;                            /* Terminate loop */
            }
            continue;
        }

        /*
         * Membership event?  Unless we detect some unwanted or
         * unknown condition we just keep running...
         */
        if( FD_ISSET( g->fd.member, &readActive ) )  {
            error = mb_read_event( g->handle.member, &(g->memberState)  );
            if( error )  {
                if( error != NO_EVENT )  {         /* XXX_MIKE - is this OK? */
                    clulog( LOG_CRIT, "(%s:%d)mb_read_event() error:%d\n",
                          __FUNCTION__, __LINE__, error );
                    result = error;                       /* Terminates loop */
                }
                continue;
            }

            if( !mb_member( g->thisNode, &(g->memberState) ) )  {
                result = NO_QUORUM;                       /* Terminates loop */
                continue;
            }
        }

        /*
         * Metadata DS event?
         */
        if( FD_ISSET( g->fd.meta, &readActive ) )  {
            error = ds_read_event( g->handle.meta, &(g->metaEvent) );
            if( error )  {
                clulog( LOG_CRIT, "(%s:%d)ds_read_event() error:%d\n",
                      __FUNCTION__, __LINE__, error );
                result = error;                           /* Terminates loop */
                continue;
            }

            /*
             * After RTFSC I conclude that the possible
             * values of ds_event_t.ds_event_type are
             * DS_WRITE, NO_QUORUM and UNKNOWN_EVENT.
             */
            switch( g->metaEvent.ds_event_type )  {
            case DS_WRITE:
                error = phase4meta( g );    /* Somebody touched the metadata */
                if( error )  {
                    clulog( LOG_CRIT, "(%s:%d)phase4meta() error:%d\n",
                          __FUNCTION__, __LINE__, error );
                    result = error;
                    continue;              /* Nonzero result terminates loop */
                }
                break;                   /* Metadata event handled - proceed */
            case NO_QUORUM:
            case UNKNOWN_EVENT:                    /* What could cause this? */
            default:                  /* XXX_MIKE - could this ever be zero? */
                result = g->metaEvent.ds_event_type;
                continue;                  /* Nonzero result terminates loop */
            }
        }

        /*
         * FAM event?
         */
        if( g->writeDS )  {
            while( !result  &&  FAMPending( &(g->fam.connection) )  )  {
                error = phase4fam( g );
                if( error < 0 )  {
                    result = error;                       /* Terminates loop */
                    continue;
                }
            }
        }
    }

exit:
    if( g->fam.connection.fd >= 0 )  {
        FAMClose( &(g->fam.connection) );
        g->fam.connection.fd = -1;
    }
    return( result );
}


/*
 * ----------------------------------------------------------------------------
 * Called when we determine that we have quorum.
 *
 * Find the metadata DS (possibly first creating it) and sign up for events.
 * We'll need to open the associated lock, as well, but even though we'll
 * briefly lock it here we'll leave it unlocked after we're done with our
 * setup stuff...
 */
int
phase2(
    global         *g )
{
    int             error;
    netg_lk_handle *lockHandle;
    metadata       *meta;
    netg_ds_handle *metaHandle;
    dataspace_t    *metaSpace;
    int             result;
    int             shouldUpdate;


    lockHandle   = 0;
    metaHandle   = 0;
    result       = 0;
    shouldUpdate = 0;

    /*
     * lk_open() currently ignores the 2nd arg ("flags")
     */
    lockHandle = lk_open( g->DStag.L, 0, &error );
    if( !lockHandle  ||  error )  {
        clulog( LOG_CRIT, "(%s:%d)lk_open(%s) failed - error:%d\n",
              __FUNCTION__, __LINE__, g->DStag.L, error );
        result = error;
        goto exit;
    }
    error = lk_lock( lockHandle );
    if( error )  {
        clulog( LOG_CRIT, "(%s:%d)lk_lock(%s) failed - error:%d\n",
              __FUNCTION__, __LINE__, g->DStag.L, error );
        result = error;
        goto exit;
    }

    /*
     * We have the lock - open the metadata DS (not DS_PERSISTENT)
     */
    metaHandle = ds_open( g->DStag.M, 0, &error);
    if( !metaHandle  ||  error )  {
        clulog( LOG_CRIT, "(%s:%d)ds_open(%s) failed - error:%d\n",
              __FUNCTION__, __LINE__, g->DStag.M, error );
        result = error;
        goto exit;
    }

    metaSpace = &(g->metaSpace);
    ds_descriptor_init( metaSpace );
    error     = ds_read( metaHandle, metaSpace );
    if( error )  {
        if( error != DS_READ_NO_STATE )  { /* Just 1st reference to this DS? */
            clulog( LOG_CRIT, "(%s:%d)ds_read(%s) failed - error:%d\n",
                  __FUNCTION__, __LINE__, g->DStag.M, error );
            result = error;                     /* Nope - some other problem */
            goto exit;
        }
        shouldUpdate = 1;   /* Remember to push newly created metadata to DS */
    }

    /*
     * We've found the DS with the metadata for the file in question, though
     * (if this is the first reference) we may have "found" it by creating it,
     * in which case it'll at least be uninitialized and probably zero length.
     * We need to ensure that there are enough snap[] entries that our node is
     * included, reallocating a new (larger) metadata region if necessary.
     *
     * NOTE: dataspace_t.buf_size:totalBufferSize ...db_size:bytesPresent
     */
    meta  = (metadata *)(metaSpace->data);                  /* Possibly NULL */
    error = extendMetadataMem( &meta, (g->thisNode + 1) );
    if( error  ||  !meta )  {
        result = error;
        goto exit;            /* XXX_MIKE - Help! need better error checking */
    }

    /*
     * Since we just operated on our local metadata pointer
     * we might need to update the region pointer in the DS
     * descriptor since we may have resized/reallocated...
     */
    if( meta->size != metaSpace->buf_size)  {             /* Metadata grown? */
        shouldUpdate       = 1;
        meta->path         = g->path;                      /* structure-copy */
        metaSpace->data    = (void *)meta;
        metaSpace->db_size = metaSpace->buf_size = meta->size;
    }

    /*
     * If we're only here as part of a service-relocate we evict the local
     * Writer (if any) by marking the metadata as having no Writer.
     */
    if( g->resigning )  {
        if( meta->writer == g->thisNode )  {
            meta->writer = ~0;
            shouldUpdate =  1;                  /* Remember metadata changed */
        }
    } else  {
        /*
         * If we've been designated as the Writer node we stamp our mark on
         * the metadata ASAP since multiple Writers can't coexist peacefully
         * in the cluster, and neither can a Reader coexist with a Writer on
         * the same node.  This should cause all nodes monitoring the DS to
         * see an event and if there's a Reader on our node it should cause
         * him to exit immediately.  It should NOT cause any file update
         * activity since we haven't changed the snapshot view number.
         */
        if( g->writeDS  &&  (meta->writer != g->thisNode)  )  {
            meta->writer = g->thisNode;
            shouldUpdate = 1;                   /* Remember metadata changed */
        }
    }

    if( shouldUpdate )  {
        /*
         * This update will be noticed by all parties monitoring the
         * corresponding DS events but, unless the snapshot view was
         * changed in the metadata, resultant activity should be limited.
         */
        error = ds_write( metaHandle, metaSpace );
        if( error )  {
            result = error;
            goto exit;
        }
    }

    g->metaView = meta->view;   /* We'll regard this view as the current one */
    error = lk_unlock( lockHandle );
    if( error )  {
        result = error;
        goto exit;
    }

    /*
     * OK - we have quorum, the metadata handle and the lock handle
     */
    g->handle.meta = metaHandle;
    g->handle.lock = lockHandle;
    if( !g->resigning )  {
        result = phase3( g );        /* Go wait for metadata and file events */
    }

exit:
    ds_close( g->handle.meta );                           /* OK even if NULL */
    g->handle.meta = 0;
    lk_close( g->handle.lock );                           /* OK even if NULL */
    g->handle.lock = 0;
    return( result );
}


/*
 * ----------------------------------------------------------------------------
 * Learn our node ID, wait for quorum, proceed to next phase.
 */
int
phase1(
    global *g )
{
    int     error;
    int     fdMax;
    fd_set  readActive;                              /* Modified by select() */
    fd_set  readStatic;
    int     result;


    result = 0;

    /*
     * NetGuard (or at least quorumd) must be running for
     * this next operation to succeed...
     */
    g->thisNode = mb_get_node_id( &error );
    if( error )  {
        clulog( LOG_CRIT, "(%s:%d)mb_get_node_id() failed - no quorumd?\n",
              __FUNCTION__, __LINE__ );
        result = error;
        goto exit;
    }

    /*
     * DaveW says the act of registering for membership events
     * guarantees that there will be an event pending when you first
     * go to look for one, though I think he meant that would be the
     * case only if there was already quorum when you registered.
     */
    mb_unregister_for_events(         g->handle.member  );  /* Ignore errors */
    error = mb_register_for_events( &(g->handle.member) );
    if( error  ||  !(g->handle.member)  )  {
        clulog( LOG_CRIT, "(%s:%d)mb_register_for_events() returned %d\n",
              __FUNCTION__, __LINE__, error );
        result = error;
        goto exit;
    }
    g->fd.member = mb_handle_to_fd( g->handle.member );

    FD_ZERO(              &readStatic );
    FD_SET( g->fd.member, &readStatic );
    fdMax = g->fd.member + 1;

    /*
     * Loop waiting for quorum
     */
    while( 1 )  {
        /*
         * NULL timeout means select() blocks until I/O or signal...
         */
        readActive = readStatic;            /* Refresh from static snapshot. */
        error      = select( fdMax, &readActive, NULL, NULL, NULL );

        if( error <= 0 )  {
            if( (errno == EINTR ) )  {
                continue;
            }
            result = error;
            goto exit;
        }

        if( !FD_ISSET( g->fd.member, &readActive ) )  {
            continue;                  /* XXX_MIKE - Could this ever happen? */
        }

        error = mb_read_event( g->handle.member, &(g->memberState)  );
        if( error )  {
            if( error == NO_EVENT )  {   /* XXX_MIKE - can this ever happen? */
                continue;          /* XXX_MIKE - is this the right response? */
            }
            result = error;
            goto exit;
        }

        /*
         * IDIOSYNCRASY: mb_member() will only admit that the specified node
         *               is a member of the cluster if we also have quorum...
         */
        if( mb_member( g->thisNode, &(g->memberState) ) )  {
            break;
        }
    }

    /*
     * OK - we have quorum...
     */
    result = phase2( g );         /* ...acquire necessary locks & dataspaces */

exit:
    mb_unregister_for_events( g->handle.member );                 /* Blindly */
    g->handle.member = 0;
    return( result );
}


/*
 * ----------------------------------------------------------------------------
 */
int
main(
    int    argc,
    char **argv  )
{
    int    arg;
    global g;
    int    result;
    int    runAsDaemon;


    if( argc < 2 )  {
        printf( "usage: %s [-v] [-D] [-w] [-R] [-L localName] -f fileName\n",
                        argv[0] );
        exit( 1 );
    }

    runAsDaemon = 1;                      /* Can be overridden for debugging */
    memset( &g, 0, sizeof(g) );
    g.metaSpace.view_no = DS_INVALID_VIEW_NO;

    while( (arg = getopt( argc, argv, "Df:L:Rvw" )) != -1 )  {
        switch( arg )  {
        case 'R':
            g.resigning = 1;
            break;
        case 'D':
            runAsDaemon = 0;
            break;
        case 'f':
            strncpy( g.path.specified, optarg, MAXPATHLEN );
            break;
        case 'L':         /* If local filename differs from "canonical" name */
            strncpy( g.path.canonical, optarg, MAXPATHLEN ); /* NOT DONE YET */
            break;
        case 'v':
            g.verbose = 1;                    /* Default is TERSE - override */
            break;
        case 'w':
            g.writeDS = 1;                  /* Default is READING - override */
            break;
        default:
            main( 0, argv );
            break;
        }
    }

    if( !g.path.specified[0] )  {
        fprintf( stderr, "Must specify filename.\n" );
        return( main( 0, argv )  );
    }

    if( runAsDaemon )  {
        void daemon_init_no_check( char *prog );
        daemon_init_no_check( argv[0] );
    }

    /*
     * The name of the dataspaces we'll be using will be the ASCII string
     * representing the MD5 hash of the specified pathname.  However,
     * since NetGuard has a 31 character name limit we need to clip it to
     * that length.  We also force the last byte of the metadata space
     * name string to be 'M' while the name of the dataspace containing
     * the actual file data ends in 'D' and the lock's name ends in 'L'
     */
    md5asciiHashStringForString( g.path.specified, g.DStag.D );
    strcpy( g.DStag.L, g.DStag.D );
    strcpy( g.DStag.M, g.DStag.D );
    g.DStag.D[ 30 ] = 'D';  g.DStag.D[ 31 ] = 0;
    g.DStag.L[ 30 ] = 'L';  g.DStag.L[ 31 ] = 0;
    g.DStag.M[ 30 ] = 'M';  g.DStag.M[ 31 ] = 0;


    setupConfig(); /* XXX_MIKE - we don't actually use any config stuff, yet */
    setup_signals();        /* XXX_MIKE - we don't actually use signals, yet */
    logging_init( "clufmirror" ); /* XXX_MIKE - obtain log-level from config */

    if( g.verbose )  {
        clulog( LOG_CRIT, "(%s:%s:%d)START pid:%d file:%s MD5:%s\n",
                                argv[0], __FUNCTION__, __LINE__,
                                getpid(), g.path.specified, g.DStag.M );
    }
    result = phase1( &g );            /* Start by waiting for quorum, etc... */
    if( g.verbose )  {
        clulog( LOG_CRIT, "(%s:%s:%d)EXIT result:%d\n",
             argv[0], __FUNCTION__, __LINE__, result );
    }

    return( result );
}

