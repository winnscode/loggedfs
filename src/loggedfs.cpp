/*****************************************************************************
 * Author:   Remi Flament <remipouak at gmail dot com>
 *****************************************************************************
 * Copyright (c) 2005 - 2022, Remi Flament and contributors
 *
 * Licensed to the Apache Software Foundation (ASF) under one
 * or more contributor license agreements.  See the NOTICE file
 * distributed with this work for additional information
 * regarding copyright ownership.  The ASF licenses this file
 * to you under the Apache License, Version 2.0 (the
 * "License"); you may not use this file except in compliance
 * with the License.  You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0

 * Unless required by applicable law or agreed to in writing,
 * software distributed under the License is distributed on an
 * "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
 * KIND, either express or implied.  See the License for the
 * specific language governing permissions and limitations
 * under the License.
 *
 */

#ifdef linux
/* For pread()/pwrite() */
#define _X_SOURCE 500
#endif

#include <fuse.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>
#include <fcntl.h>
#include <dirent.h>
#include <errno.h>
#include <sys/statfs.h>

#ifdef HAVE_SETXATTR
#include <sys/xattr.h>
#endif

#include "easylogging++.h"
#include <stdarg.h>
#include <getopt.h>
#include <sys/time.h>
#include <pwd.h>
#include <grp.h>
#include "Config.h"
#include <stdexcept>
#include <iostream>


#include <stdio.h>
#include <sstream>
#include <cassert>
#include <functional>
#include "leveldb/db.h"



INITIALIZE_EASYLOGGINGPP

#define STR(X) #X
#define rAssert(cond)                                     \
    do                                                    \
    {                                                     \
        if ((cond) == false)                              \
        {                                                 \
            LOG(ERROR) << "Assert failed: " << STR(cond); \
            throw std::runtime_error(STR(cond));          \
        }                                                 \
    } while (false)

#define PUSHARG(ARG)                      \
    rAssert(out->fuseArgc < MaxFuseArgs); \
    out->fuseArgv[out->fuseArgc++] = ARG

using namespace std;
static Config config;
static int savefd;
static el::base::DispatchAction dispatchAction = el::base::DispatchAction::NormalLog;
static const char *loggerId = "default";
static const char *additionalInfoFormat = " {%s} [ pid = %d %s uid = %d ]";
static el::Logger *defaultLogger;


static leveldb::DB* db;
static leveldb::Status s;
static string magic;
static bool debugmode = false;

const int MaxFuseArgs = 32;
struct LoggedFS_Args
{
    char *mountPoint; // where the users read files
    char *configFilename;
    bool isDaemon; // true == spawn in background, log to syslog except if log file parameter is set
    bool logToSyslog;
    const char *fuseArgv[MaxFuseArgs];
    int fuseArgc;
};

static LoggedFS_Args *loggedfsArgs = new LoggedFS_Args;

static bool isAbsolutePath(const char *fileName)
{
    if (fileName && fileName[0] != '\0' && fileName[0] == '/')
        return true;
    else
        return false;
}

static char *getAbsolutePath(const char *path)
{
    char *realPath = new char[strlen(path) + strlen(loggedfsArgs->mountPoint) + 1];

    strcpy(realPath, loggedfsArgs->mountPoint);
    if (realPath[strlen(realPath) - 1] == '/')
        realPath[strlen(realPath) - 1] = '\0';
    strcat(realPath, path);
    return realPath;
}

static char *getRelativePath(const char *path)
{
    if (path[0] == '/')
    {
        if (strlen(path) == 1)
        {
            return strdup(".");
        }
        const char *substr = &path[1];
        return strdup(substr);
    }

    return strdup(path);
}


// 文件名的转换
// map方式随便写写的，216+16+16，可自定义，但转换后应该不大于255Byte
string __map_name(string rawname)
{
        string n_str2;
        std::hash<std::string> h;
        size_t n = h(rawname);
        stringstream ioss;
        ioss << hex << n;
        ioss >> n_str2;

        string name2 = rawname.substr(0,216);
        return name2 + magic + n_str2;
}


// 文件名转换的核心逻辑：
// 使用了bool作为返回值，之后可以重构为直接返回空串，或者其它形式
bool map_name(string rawname, string &realname)
{
        realname = "";
        if (rawname.size() < 256) {
                return false;
        }

        string tmp = __map_name(rawname);
        string v;

        // case1： 映射已经存在，直接返回结果
        s = db->Get(leveldb::ReadOptions(), tmp, &v);

        if (s.ok() && v == rawname) {
                realname = tmp;
                return true;
        }

        // case2： 映射不存在，创建并返回
        if (s.IsNotFound()) {
                s = db->Put(leveldb::WriteOptions(), tmp, rawname);
                if (s.ok()) {
                        realname = tmp;
                        return true;
                }
        }

        // case3：发生了冲突：realname作为key被其它rawname占用了，返回false，外层可以返回一个合适的错误值，表明该文件名不可用
        // TODO： 更完整的冲突处理？
        // 另外，现在是只要进入一次，rawname到realname的map关系就确定下来了，且这个map关系是该fuse全局的
        return false;
}




// 将rawpath映射到realpath
// 因为loggedfs的path处理是c，而leveldb的读写又是string，所以拼凑的时候也是混着用的。
// realpath是要直接传递给local-fs的，走libc、vfs、fs的路径，所以要预先完整地做映射，
// 所以需要在fuse里做路径解析，按"/"分割，并对其中的longname进行map。
// 当前代码很乱，建议重写，现在可能有内存泄露风险或者逻辑bug之类的。
char *map_path(const char *path, bool *ok)
{
    size_t len = strlen(path);
    // 不管是否成功，orig作为遍历需要的临时字符串，会在函数内free，而dest需要调用者释放
    char *orig = (char *)malloc(len+1);
    char *dest = (char *)malloc(len+1);

    // 原则上保持和orig path一样的格式，包括结尾的“/”
    int need_tail = 0;

    char *token;
    char *seq;

    strcpy(orig, path);

    if (orig[len-1] == '/' && len != 1)
        need_tail = 1;

    // 因为后面都是用strcat修改dest，所以先将其构造为一个长度为0的字符串
    // NOTE: 这是我临时了解c库的字符串处理而写的，使用方式很有可能有问题
    dest[0] = '\0';

    if (orig[0] == '/') {
        strcat(dest, "/");
        seq = orig + 1;
    } else
        seq = orig;

    // 在orig上，用“/”做分割，一段一段处理
    // strtok，我也不知道还有没有更好的方式……
    token = strtok(seq, "/");
    int first = 1;

    while (token != NULL) {
        // first时，不用加“/”
        // 如果真的是以“/”开头，前面已经手动处理了
        if (first)
            first = 0;
        else
            strcat(dest, "/");

        if (strlen(token) < 256) {
            // 长度小于255时，不进入map路径
            strcat(dest, token);
        } else {
            string src_str = token;
            string map_str = "";
            if (map_name(src_str, map_str)) {
                strcat(dest, map_str.c_str());
            } else {
                free(orig);
                *ok = 0;
                return dest;
            }
        }
        token = strtok(NULL, "/");
    }

    if (need_tail)
        strcat(dest, "/");

    free(orig);
    *ok = 1;
    return dest;
}


// 反向映射，从realname到rawname
// 当不符合map规则，或者没有在数据库找到时，直接返回realname （注意！所以没有失败）
string __map_reverse(string realname)
{
        if (realname.size() != 248) {
                return realname;
        }

        // 现在的magic是临时生成的，可以固定写死
        string tmp = realname.substr(216,16);
        if (tmp != magic) {
                cout << "tmp: " << tmp << endl;
                cout << "magic: " << magic << endl;
                return realname;
        }

        string v;
        s = db->Get(leveldb::ReadOptions(), realname, &v);

        // TODO：添加完整的访问错误逻辑处理
        if (s.IsNotFound())
                return realname;

        return v;
}


// 做了char *的封装，没有考虑效率，需要优化
char *map_reverse(const char *realname)
{
    string real = realname;
    string raw = __map_reverse(real);

    return strdup(raw.c_str());
}



// 核心是数据库的初始化
// 目前是将db文件放在挂载点目录，后续可以：
// 1 用.xxx.db隐藏
// 2 进行额外的保护，比如防止删除、手动修改之类的
bool map_init()
{
        std::hash<std::string> h;
        size_t n2  = h("deepin mapfs!");
        stringstream ioss;
        ioss << hex << n2;
        ioss >> magic;

        cout << "magic: " << magic << endl;

        // leveldb的部分可以参考网上的文档，我也是临时看，瞎用的……
        leveldb::Options options;
        options.create_if_missing = true;
        s = leveldb::DB::Open(options, "./testdb", &db);
        if (!s.ok()) {
                if (debugmode)
                    cerr << s.ToString() << endl;
                else
                    // ELPP_WRITE_LOG(el::base::Writer, el::Level::Info, dispatchAction, "default") << "map init failed." << endl;
                    defaultLogger->info("Map init failed");

                return false;
        }
        return true;
}




/*
 * Returns the name of the process which accessed the file system.
 */
static char *getcallername()
{
    char filename[100];
    sprintf(filename, "/proc/%d/cmdline", fuse_get_context()->pid);
    FILE *proc;
    char cmdline[256] = "";

    if ((proc = fopen(filename, "rt")) == NULL)
        return NULL;
    else
    {
        fread(cmdline, sizeof(cmdline), 1, proc);
        fclose(proc);
    }

    return strdup(cmdline);
}

static void loggedfs_log(const char *path, const char *action, const int returncode, const char *format, ...)
{
    const char *retname;

    if (returncode >= 0)
        retname = "SUCCESS";
    else
        retname = "FAILURE";

    if (config.shouldLog(path, fuse_get_context()->uid, action, retname))
    {
        va_list args;
        char *buf = NULL;
        char *additionalInfo = NULL;

        char *caller_name = getcallername();
        asprintf(&additionalInfo, additionalInfoFormat, retname, fuse_get_context()->pid, config.isPrintProcessNameEnabled() ? caller_name : "", fuse_get_context()->uid);

        va_start(args, format);
        vasprintf(&buf, format, args);
        va_end(args);

        if (returncode >= 0)
        {
            ELPP_WRITE_LOG(el::base::Writer, el::Level::Info, dispatchAction, "default") << buf << additionalInfo;
        }
        else
        {
            ELPP_WRITE_LOG(el::base::Writer, el::Level::Error, dispatchAction, "default") << buf << additionalInfo;
        }

        free(buf);
        free(additionalInfo);
        free(caller_name);
    }
}

static void *loggedFS_init(struct fuse_conn_info *info)
{
    fchdir(savefd);
    close(savefd);
    return NULL;
}

static int loggedFS_getattr(const char *orig_path, struct stat *stbuf)
{
    int res;

    char *aPath = getAbsolutePath(orig_path);
    char *path = getRelativePath(orig_path);
    res = lstat(path, stbuf);
    loggedfs_log(aPath, "getattr", res, "getattr %s", aPath);
    delete[] aPath;
    free(path);
    if (res == -1)
        return -errno;

    return 0;
}

static int loggedFS_access(const char *orig_path, int mask)
{
    int res;

    char *aPath = getAbsolutePath(orig_path);
    char *path = getRelativePath(orig_path);
    res = access(path, mask);
    loggedfs_log(aPath, "access", res, "access %s", aPath);
    delete[] aPath;
    free(path);
    if (res == -1)
        return -errno;

    return 0;
}

static int loggedFS_readlink(const char *orig_path, char *buf, size_t size)
{
    int res;

    char *aPath = getAbsolutePath(orig_path);
    char *path = getRelativePath(orig_path);
    res = readlink(path, buf, size - 1);
    loggedfs_log(aPath, "readlink", res, "readlink %s", aPath);
    delete[] aPath;
    free(path);
    if (res == -1)
        return -errno;

    buf[res] = '\0';

    return 0;
}

static int loggedFS_readdir(const char *orig_path, void *buf, fuse_fill_dir_t filler,
                            off_t offset, struct fuse_file_info *fi)
{
    DIR *dp;
    struct dirent *de;
    int res;

    (void)offset;
    (void)fi;

    char *aPath = getAbsolutePath(orig_path);
    char *path = getRelativePath(orig_path);

    dp = opendir(path);
    if (dp == NULL)
    {
        res = -errno;
        loggedfs_log(aPath, "readdir", -1, "readdir %s", aPath);
        delete[] aPath;
        free(path);
        return res;
    }

    while ((de = readdir(dp)) != NULL)
    {
        struct stat st;
        memset(&st, 0, sizeof(st));
        st.st_ino = de->d_ino;
        st.st_mode = de->d_type << 12;
        if (filler(buf, de->d_name, &st, 0))
            break;
    }

    closedir(dp);
    loggedfs_log(aPath, "readdir", 0, "readdir %s", aPath);
    delete[] aPath;
    free(path);

    return 0;
}

static int loggedFS_mknod(const char *orig_path, mode_t mode, dev_t rdev)
{
    int res;
    char *aPath = getAbsolutePath(orig_path);
    char *path = getRelativePath(orig_path);

    if (S_ISREG(mode))
    {
        res = open(path, O_CREAT | O_EXCL | O_WRONLY, mode);
        loggedfs_log(aPath, "mknod", res, "mknod %s %o S_IFREG (normal file creation)", aPath, mode);
        if (res >= 0)
            res = close(res);
    }
    else if (S_ISFIFO(mode))
    {
        res = mkfifo(path, mode);
        loggedfs_log(aPath, "mkfifo", res, "mkfifo %s %o S_IFFIFO (fifo creation)", aPath, mode);
    }
    else
    {
        res = mknod(path, mode, rdev);
        if (S_ISCHR(mode))
        {
            loggedfs_log(aPath, "mknod", res, "mknod %s %o (character device creation)", aPath, mode);
        }
        /*else if (S_IFBLK(mode))
		{
		loggedfs_log(aPath,"mknod",res,"mknod %s %o (block device creation)",aPath, mode);
		}*/
        else
            loggedfs_log(aPath, "mknod", res, "mknod %s %o", aPath, mode);
    }

    delete[] aPath;

    if (res == -1)
    {
        free(path);
        return -errno;
    }
    else
        lchown(path, fuse_get_context()->uid, fuse_get_context()->gid);

    free(path);

    return 0;
}


static int loggedFS_mkdir(const char *orig_path, mode_t mode)
{
    int res;
    char *aPath = getAbsolutePath(orig_path);
    char *path = getRelativePath(orig_path);
    res = mkdir(path, mode);
    loggedfs_log(path, "mkdir", res, "mkdir %s %o", aPath, mode);
    delete[] aPath;

    if (res == -1)
    {
        free(path);
        return -errno;
    }
    else
        lchown(path, fuse_get_context()->uid, fuse_get_context()->gid);

    free(path);
    return 0;
}

static int loggedFS_unlink(const char *orig_path)
{
    int res;
    char *aPath = getAbsolutePath(orig_path);
    char *path = getRelativePath(orig_path);
    res = unlink(path);
    loggedfs_log(aPath, "unlink", res, "unlink %s", aPath);
    delete[] aPath;
    free(path);

    if (res == -1)
        return -errno;

    return 0;
}

static int loggedFS_rmdir(const char *orig_path)
{
    int res;
    char *aPath = getAbsolutePath(orig_path);
    char *path = getRelativePath(orig_path);
    res = rmdir(path);
    loggedfs_log(aPath, "rmdir", res, "rmdir %s", aPath);
    delete[] aPath;
    free(path);
    if (res == -1)
        return -errno;
    return 0;
}

static int loggedFS_symlink(const char *from, const char *orig_to)
{
    int res;

    char *aTo = getAbsolutePath(orig_to);
    char *to = getRelativePath(orig_to);

    res = symlink(from, to);

    loggedfs_log(aTo, "symlink", res, "symlink from %s to %s", aTo, from);
    delete[] aTo;

    if (res == -1)
    {
        free(to);
        return -errno;
    }
    else
        lchown(to, fuse_get_context()->uid, fuse_get_context()->gid);

    free(to);
    return 0;
}

static int loggedFS_rename(const char *orig_from, const char *orig_to)
{
    int res;
    char *aFrom = getAbsolutePath(orig_from);
    char *aTo = getAbsolutePath(orig_to);
    char *from = getRelativePath(orig_from);
    char *to = getRelativePath(orig_to);
    res = rename(from, to);
    loggedfs_log(aFrom, "rename", res, "rename %s to %s", aFrom, aTo);
    delete[] aFrom;
    delete[] aTo;
    free(from);
    free(to);

    if (res == -1)
        return -errno;

    return 0;
}

static int loggedFS_link(const char *orig_from, const char *orig_to)
{
    int res;

    char *aFrom = getAbsolutePath(orig_from);
    char *aTo = getAbsolutePath(orig_to);
    char *from = getRelativePath(orig_from);
    char *to = getRelativePath(orig_to);

    res = link(from, to);
    loggedfs_log(aTo, "link", res, "hard link from %s to %s", aTo, aFrom);
    delete[] aFrom;
    delete[] aTo;
    free(from);

    if (res == -1)
    {
        delete[] to;
        return -errno;
    }
    else
        lchown(to, fuse_get_context()->uid, fuse_get_context()->gid);

    free(to);

    return 0;
}

static int loggedFS_chmod(const char *orig_path, mode_t mode)
{
    int res;
    char *aPath = getAbsolutePath(orig_path);
    char *path = getRelativePath(orig_path);
    res = chmod(path, mode);
    loggedfs_log(aPath, "chmod", res, "chmod %s to %o", aPath, mode);
    delete[] aPath;
    free(path);

    if (res == -1)
        return -errno;

    return 0;
}

static char *getusername(uid_t uid)
{
    struct passwd *p = getpwuid(uid);
    if (p != NULL)
        return p->pw_name;
    return NULL;
}

static char *getgroupname(gid_t gid)
{
    struct group *g = getgrgid(gid);
    if (g != NULL)
        return g->gr_name;
    return NULL;
}

static int loggedFS_chown(const char *orig_path, uid_t uid, gid_t gid)
{
    int res;
    char *aPath = getAbsolutePath(orig_path);
    char *path = getRelativePath(orig_path);
    res = lchown(path, uid, gid);

    char *username = getusername(uid);
    char *groupname = getgroupname(gid);

    if (username != NULL && groupname != NULL)
        loggedfs_log(aPath, "chown", res, "chown %s to %d:%d %s:%s", aPath, uid, gid, username, groupname);
    else
        loggedfs_log(aPath, "chown", res, "chown %s to %d:%d", aPath, uid, gid);
    delete[] aPath;
    free(path);

    if (res == -1)
        return -errno;

    return 0;
}

static int loggedFS_truncate(const char *orig_path, off_t size)
{
    int res;

    char *aPath = getAbsolutePath(orig_path);
    char *path = getRelativePath(orig_path);
    res = truncate(path, size);
    loggedfs_log(aPath, "truncate", res, "truncate %s to %d bytes", aPath, size);
    delete[] aPath;
    free(path);

    if (res == -1)
        return -errno;

    return 0;
}

#if (FUSE_USE_VERSION == 25)
static int loggedFS_utime(const char *orig_path, struct utimbuf *buf)
{
    int res;
    char *aPath = getAbsolutePath(orig_path);
    char *path = getRelativePath(orig_path);
    res = utime(path, buf);
    loggedfs_log(aPath, "utime", res, "utime %s", aPath);
    delete[] aPath;
    free(path);

    if (res == -1)
        return -errno;

    return 0;
}

#else

static int loggedFS_utimens(const char *orig_path, const struct timespec ts[2])
{
    int res;

    char *aPath = getAbsolutePath(orig_path);
    char *path = getRelativePath(orig_path);

    res = utimensat(AT_FDCWD, path, ts, AT_SYMLINK_NOFOLLOW);

    loggedfs_log(aPath, "utimens", res, "utimens %s", aPath);
    delete[] aPath;
    free(path);

    if (res == -1)
        return -errno;

    return 0;
}

#endif

static int loggedFS_open(const char *orig_path, struct fuse_file_info *fi)
{
    int res;
    char *aPath = getAbsolutePath(orig_path);
    char *path = getRelativePath(orig_path);
    res = open(path, fi->flags);

    // what type of open ? read, write, or read-write ?
    if (fi->flags & O_RDONLY)
    {
        loggedfs_log(aPath, "open-readonly", res, "open readonly %s", aPath);
    }
    else if (fi->flags & O_WRONLY)
    {
        loggedfs_log(aPath, "open-writeonly", res, "open writeonly %s", aPath);
    }
    else if (fi->flags & O_RDWR)
    {
        loggedfs_log(aPath, "open-readwrite", res, "open readwrite %s", aPath);
    }
    else
        loggedfs_log(aPath, "open", res, "open %s", aPath);

    delete[] aPath;
    free(path);

    if (res == -1)
        return -errno;

    fi->fh = res;
    return 0;
}


static int loggedFS_read(const char *orig_path, char *buf, size_t size,
    off_t offset, struct fuse_file_info *fi)
{
    char *aPath = getAbsolutePath(orig_path);
    int res;

    loggedfs_log(aPath, "read", 0, "read %d bytes from %s at offset %d", size, aPath, offset);
    res = pread(fi->fh, buf, size, offset);
    if (res == -1)
    {
        res = -errno;
        loggedfs_log(aPath, "read", -1, "read %d bytes from %s at offset %d", size, aPath, offset);
    }
    else
    {
        loggedfs_log(aPath, "read", 0, "%d bytes read from %s at offset %d", res, aPath, offset);
    }
    delete[] aPath;
    return res;
}



static int loggedFS_write(const char *orig_path, const char *buf, size_t size,
                          off_t offset, struct fuse_file_info *fi)
{
    int fd;
    int res;
    char *aPath = getAbsolutePath(orig_path);
    char *path = getRelativePath(orig_path);
    (void)fi;

    fd = open(path, O_WRONLY);
    if (fd == -1)
    {
        res = -errno;
        loggedfs_log(aPath, "write", -1, "write %d bytes to %s at offset %d", size, aPath, offset);
        delete[] aPath;
        free(path);
        return res;
    }
    else
    {
        loggedfs_log(aPath, "write", 0, "write %d bytes to %s at offset %d", size, aPath, offset);
    }

    res = pwrite(fd, buf, size, offset);

    if (res == -1)
        res = -errno;
    else
        loggedfs_log(aPath, "write", 0, "%d bytes written to %s at offset %d", res, aPath, offset);

    close(fd);
    delete[] aPath;
    free(path);

    return res;
}



static int loggedFS_statfs(const char *orig_path, struct statvfs *stbuf)
{
    int res;
    char *aPath = getAbsolutePath(orig_path);
    char *path = getRelativePath(orig_path);
    res = statvfs(path, stbuf);
    loggedfs_log(aPath, "statfs", res, "statfs %s", aPath);
    delete[] aPath;
    free(path);
    if (res == -1)
        return -errno;

    return 0;
}

static int loggedFS_release(const char *orig_path, struct fuse_file_info *fi)
{
    char *aPath = getAbsolutePath(orig_path);
    (void)orig_path;

    loggedfs_log(aPath, "release", 0, "release %s", aPath);
    delete[] aPath;

    close(fi->fh);
    return 0;
}

static int loggedFS_fsync(const char *orig_path, int isdatasync,
                          struct fuse_file_info *fi)
{
    char *aPath = getAbsolutePath(orig_path);
    (void)orig_path;
    (void)isdatasync;
    (void)fi;
    loggedfs_log(aPath, "fsync", 0, "fsync %s", aPath);
    delete[] aPath;
    return 0;
}

#ifdef HAVE_SETXATTR
/* xattr operations are optional and can safely be left unimplemented */
static int loggedFS_setxattr(const char *orig_path, const char *name, const char *value,
                             size_t size, int flags)
{
    int res = lsetxattr(orig_path, name, value, size, flags);
    if (res == -1)
        return -errno;
    return 0;
}

static int loggedFS_getxattr(const char *orig_path, const char *name, char *value,
                             size_t size)
{
    int res = lgetxattr(orig_path, name, value, size);
    if (res == -1)
        return -errno;
    return res;
}

static int loggedFS_listxattr(const char *orig_path, char *list, size_t size)
{
    int res = llistxattr(orig_path, list, size);
    if (res == -1)
        return -errno;
    return res;
}

static int loggedFS_removexattr(const char *orig_path, const char *name)
{
    int res = lremovexattr(orig_path, name);
    if (res == -1)
        return -errno;
    return 0;
}
#endif /* HAVE_SETXATTR */




// 通用模式是：加一层wrapper，预先做path的map
// 大部分操作都是这样： 将用户传入的orig-path，转换为real-path，其它逻辑都不需要动
// 我随手写了一部分，没有写全：比如access，rename，unlink之类的就还没写。
// 可以考虑用宏来重构……
// readdir()不同，它是读出目录中的real-name，转换为raw-name，并上报给fuse-driver
static int loggedFS_getattr_2(const char *orig_path, struct stat *stbuf)
{
    bool ok;
    int ret;
    char *path = map_path(orig_path, &ok);

    ret = 0;

    // TODO：错误处理需要更加规范
    if (!ok)
        ret = -EINVAL;
    else
        ret = loggedFS_getattr(path, stbuf);

out:
    // 记得free
    free(path);
    return ret;
}





// readdir而言，两件事都要做：
// 1. 将目录的orig-path，转换为real-path，往下传递
// 2. 将下层返回的目录内文件的realname，根据需要反向映射为rawname，并填充dirent
static int loggedFS_readdir_2(const char *orig_path, void *buf, fuse_fill_dir_t filler,
                            off_t offset, struct fuse_file_info *fi)
{
    bool ok;
    DIR *dp;
    struct dirent *de;
    int res;
    char *aPath;
    char *path;
    char *real_path;

    (void)offset;
    (void)fi;



    res = 0;
    real_path = map_path(orig_path, &ok);

    if (!ok) {
        res = -EINVAL;
        goto out2;
    }


    aPath = getAbsolutePath(real_path);
    path = getRelativePath(real_path);



    dp = opendir(path);
    if (dp == NULL)
    {
        res = -errno;
        loggedfs_log(aPath, "readdir", -1, "readdir %s", aPath);
        goto out1;
    }

    while ((de = readdir(dp)) != NULL)
    {
        struct stat st;
        memset(&st, 0, sizeof(st));
        st.st_ino = de->d_ino;
        st.st_mode = de->d_type << 12;

        // 执行反向映射，注意free （不会失败）
        char *r_name = map_reverse(de->d_name);

        if (filler(buf, r_name, &st, 0)) {
            free(r_name);
            break;
        } else {
            free(r_name);
        }

    }

    closedir(dp);
    loggedfs_log(aPath, "readdir", 0, "readdir %s", aPath);

    // 资源释放，按照内核的习惯用的goto，可以自行调整
out1:
    delete[] aPath;
    free(path);

out2:
    free(real_path);
    return res;
}


static int loggedFS_mknod_2(const char *orig_path, mode_t mode, dev_t rdev)
{
    bool ok;
    int ret;
    char *path = map_path(orig_path, &ok);

    ret = 0;
    if (!ok)
        ret = -EINVAL;
    else
        ret = loggedFS_mknod(path, mode, rdev);

out:
    free(path);
    return ret;
}


static int loggedFS_mkdir_2(const char *orig_path, mode_t mode)
{
    bool ok;
    int ret;
    char *path = map_path(orig_path, &ok);

    ret = 0;
    if (!ok)
        ret = -EINVAL;
    else
        ret = loggedFS_mkdir(path, mode);

out:
    free(path);
    return ret;
}



static int loggedFS_utimens_2(const char *orig_path,
        const struct timespec ts[2])
{
    bool ok;
    int ret;
    char *path = map_path(orig_path, &ok);

    ret = 0;
    if (!ok)
        ret = -EINVAL;
    else
        ret = loggedFS_utimens(path, ts);

out:
    free(path);
    return ret;
}



static int loggedFS_open_2(const char *orig_path, struct fuse_file_info *fi)
{
    bool ok;
    int ret;
    char *path = map_path(orig_path, &ok);

    ret = 0;
    if (!ok)
        ret = -EINVAL;
    else
        ret = loggedFS_open(path, fi);

out:
    free(path);
    return ret;
}



static int loggedFS_read_2(const char *orig_path, char *buf, size_t size,
    off_t offset, struct fuse_file_info *fi)
{
    bool ok;
    int ret;
    char *path = map_path(orig_path, &ok);

    ret = 0;
    if (!ok)
        ret = -EINVAL;
    else
        ret = loggedFS_read(path, buf, size, offset, fi);

out:
    free(path);
    return ret;
}



static int loggedFS_write_2(const char *orig_path, const char *buf, size_t size,
                          off_t offset, struct fuse_file_info *fi)
{
    bool ok;
    int ret;
    char *path = map_path(orig_path, &ok);

    ret = 0;
    if (!ok)
        ret = -EINVAL;
    else
        ret = loggedFS_write(path, buf, size, offset, fi);

out:
    free(path);
    return ret;
}


static void usage(char *name)
{
    fprintf(stderr, "Usage:\n");
    fprintf(stderr, "%s [-h] | [-l log-file] [-c config-file] [-f] [-p] [-e] /directory-mountpoint\n", name);
    fprintf(stderr, "Type 'man loggedfs' for more details\n");
    return;
}

static bool processArgs(int argc, char *argv[], LoggedFS_Args *out)
{
    // set defaults
    out->isDaemon = true;
    out->logToSyslog = true;

    out->fuseArgc = 0;
    out->configFilename = NULL;

    // pass executable name through
    out->fuseArgv[0] = argv[0];
    ++out->fuseArgc;

    // leave a space for mount point, as FUSE expects the mount point before
    // any flags
    out->fuseArgv[1] = NULL;
    ++out->fuseArgc;
    opterr = 0;

    int res;

    bool got_p = false;

    // We need the "nonempty" option to mount the directory in recent FUSE's
    // because it's non empty and contains the files that will be logged.
    //
    // We need "use_ino" so the files will use their original inode numbers,
    // instead of all getting 0xFFFFFFFF . For example, this is required for
    // logging the ~/.kde/share/config directory, in which hard links for lock
    // files are verified by their inode equivalency.

#define COMMON_OPTS "nonempty,use_ino,attr_timeout=0,entry_timeout=0,negative_timeout=0"

    // Delete "nonempty" in fuse3
// #define COMMON_OPTS "use_ino,attr_timeout=0,entry_timeout=0,negative_timeout=0"

    while ((res = getopt(argc, argv, "hpfec:l:")) != -1)
    {
        switch (res)
        {
        case 'h':
            usage(argv[0]);
            return false;
        case 'f':
            out->isDaemon = false;
            out->logToSyslog = false;
            // this option was added in fuse 2.x
            PUSHARG("-f");
            defaultLogger->info("LoggedFS not running as a daemon");
            break;
        case 'p':
            PUSHARG("-o");
            PUSHARG("allow_other,default_permissions," COMMON_OPTS);
            got_p = true;
            defaultLogger->info("LoggedFS running as a public filesystem");
            break;
        // case 'e':
        //     PUSHARG("-o");
        //     PUSHARG("nonempty");
        //     defaultLogger->info("Using existing directory");
        //     break;
        case 'c':
            out->configFilename = optarg;
            defaultLogger->info("Configuration file : %v", optarg);
            break;
        case 'l':
        {
            defaultLogger->info("LoggedFS log file : %v, no syslog logs", optarg);
            out->logToSyslog = false;
            el::Configurations defaultConf;
            defaultConf.setToDefault();
            defaultConf.setGlobally(el::ConfigurationType::ToFile, std::string("true"));
            defaultConf.setGlobally(el::ConfigurationType::ToStandardOutput, std::string("false"));
            defaultConf.setGlobally(el::ConfigurationType::Filename, std::string(optarg));
            el::Loggers::reconfigureLogger("default", defaultConf);
            defaultLogger = el::Loggers::getLogger("default");
            break;
        }
        default:
            break;
        }
    }

    if (!got_p)
    {
        PUSHARG("-o");
        PUSHARG(COMMON_OPTS);
    }
#undef COMMON_OPTS

    if (optind + 1 <= argc)
    {
        out->mountPoint = argv[optind++];
        out->fuseArgv[1] = out->mountPoint;
    }
    else
    {
        fprintf(stderr, "Missing mountpoint\n");
        usage(argv[0]);
        return false;
    }

    // If there are still extra unparsed arguments, pass them onto FUSE..
    if (optind < argc)
    {
        rAssert(out->fuseArgc < MaxFuseArgs);

        while (optind < argc)
        {
            rAssert(out->fuseArgc < MaxFuseArgs);
            out->fuseArgv[out->fuseArgc++] = argv[optind];
            ++optind;
        }
    }

    if (!isAbsolutePath(out->mountPoint))
    {
        fprintf(stderr, "You must use absolute paths "
                        "(beginning with '/') for %s\n",
                out->mountPoint);
        return false;
    }
    return true;
}

int main(int argc, char *argv[])
{
    el::Configurations defaultConf;
    defaultConf.setToDefault();
    defaultConf.setGlobally(el::ConfigurationType::ToFile, std::string("false"));
    el::Loggers::reconfigureLogger("default", defaultConf);
    defaultLogger = el::Loggers::getLogger("default");

    char *input = new char[2048]; // 2ko MAX input for configuration

    umask(0);
    fuse_operations loggedFS_oper;
    // in case this code is compiled against a newer FUSE library and new
    // members have been added to fuse_operations, make sure they get set to
    // 0..
    memset(&loggedFS_oper, 0, sizeof(fuse_operations));
    loggedFS_oper.init = loggedFS_init;
    loggedFS_oper.getattr = loggedFS_getattr_2;
    loggedFS_oper.access = loggedFS_access;
    loggedFS_oper.readlink = loggedFS_readlink;
    loggedFS_oper.readdir = loggedFS_readdir_2;
    loggedFS_oper.mknod = loggedFS_mknod_2;
    loggedFS_oper.mkdir = loggedFS_mkdir_2;
    loggedFS_oper.symlink = loggedFS_symlink;
    loggedFS_oper.unlink = loggedFS_unlink;
    loggedFS_oper.rmdir = loggedFS_rmdir;
    loggedFS_oper.rename = loggedFS_rename;
    loggedFS_oper.link = loggedFS_link;
    loggedFS_oper.chmod = loggedFS_chmod;
    loggedFS_oper.chown = loggedFS_chown;
    loggedFS_oper.truncate = loggedFS_truncate;
#if (FUSE_USE_VERSION == 25)
    loggedFS_oper.utime = loggedFS_utime;
#else
    loggedFS_oper.utimens = loggedFS_utimens_2;
    loggedFS_oper.flag_utime_omit_ok = 1;
#endif
    loggedFS_oper.open = loggedFS_open_2;
    loggedFS_oper.read = loggedFS_read_2;
    loggedFS_oper.write = loggedFS_write_2;
    loggedFS_oper.statfs = loggedFS_statfs;
    loggedFS_oper.release = loggedFS_release;
    loggedFS_oper.fsync = loggedFS_fsync;
#ifdef HAVE_SETXATTR
    loggedFS_oper.setxattr = loggedFS_setxattr;
    loggedFS_oper.getxattr = loggedFS_getxattr;
    loggedFS_oper.listxattr = loggedFS_listxattr;
    loggedFS_oper.removexattr = loggedFS_removexattr;
#endif

    for (int i = 0; i < MaxFuseArgs; ++i)
        loggedfsArgs->fuseArgv[i] = NULL; // libfuse expects null args..


    if (processArgs(argc, argv, loggedfsArgs))
    {

        if (loggedfsArgs->logToSyslog)
        {
            dispatchAction = el::base::DispatchAction::SysLog;
            loggerId = "syslog";
        }

        defaultLogger->info("LoggedFS starting at %v.", loggedfsArgs->mountPoint);

        if (loggedfsArgs->configFilename != NULL)
        {

            if (strcmp(loggedfsArgs->configFilename, "-") == 0)
            {
                defaultLogger->info("Using stdin configuration");
                memset(input, 0, 2048);
                char *ptr = input;

                int size = 0;
                do
                {
                    size = fread(ptr, 1, 1, stdin);
                    ptr++;
                } while (!feof(stdin) && size > 0);
                config.loadFromXmlBuffer(input);
            }
            else
            {
                defaultLogger->info("Using configuration file %v.", loggedfsArgs->configFilename);
                config.loadFromXmlFile(loggedfsArgs->configFilename);
            }
        }
        delete[] input;
        defaultLogger->info("chdir to %v", loggedfsArgs->mountPoint);
        chdir(loggedfsArgs->mountPoint);
        savefd = open(".", 0);



    if (!map_init())
        return -1;





#if (FUSE_USE_VERSION == 25)
        fuse_main(loggedfsArgs->fuseArgc,
                  const_cast<char **>(loggedfsArgs->fuseArgv), &loggedFS_oper);
#else
        fuse_main(loggedfsArgs->fuseArgc,
                  const_cast<char **>(loggedfsArgs->fuseArgv), &loggedFS_oper, NULL);
#endif

        defaultLogger->info("LoggedFS closing.");
    }
}
