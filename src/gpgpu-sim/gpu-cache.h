// Copyright (c) 2009-2011, Tor M. Aamodt, Tayler Hetherington
// The University of British Columbia
// All rights reserved.
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are met:
//
// Redistributions of source code must retain the above copyright notice, this
// list of conditions and the following disclaimer.
// Redistributions in binary form must reproduce the above copyright notice, this
// list of conditions and the following disclaimer in the documentation and/or
// other materials provided with the distribution.
// Neither the name of The University of British Columbia nor the names of its
// contributors may be used to endorse or promote products derived from this
// software without specific prior written permission.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
// ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
// WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
// DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
// FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
// DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
// SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
// CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
// OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
// OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

#ifndef GPU_CACHE_H
#define GPU_CACHE_H

#include <stdio.h>
#include <stdlib.h>
#include "gpu-misc.h"
#include "mem_fetch.h"
#include "../abstract_hardware_model.h"
#include "../tr1_hash_map.h"

#include "addrdec.h"

enum cache_block_state {
    INVALID,
    RESERVED,
    VALID,
    MODIFIED
};

enum cache_request_status {
    HIT = 0,
    HIT_RESERVED,
    MISS,
    RESERVATION_FAIL,
    PREFETCH_HIT, //added by gh
    PREFETCH_MISS,
    NUM_CACHE_REQUEST_STATUS
};

enum cache_event {
    WRITE_BACK_REQUEST_SENT,
    READ_REQUEST_SENT,
    WRITE_REQUEST_SENT
};

const char * cache_request_status_str(enum cache_request_status status); 

struct cache_block_t {
    cache_block_t()
    {
        m_tag=0;
        m_block_addr=0;
        m_alloc_time=0;
        m_fill_time=0;
        m_last_access_time=0;
        m_status=INVALID;
        //added by gh
        m_prefetched=false;
        m_accessed=false;
    }
    void allocate( new_addr_type tag, new_addr_type block_addr, unsigned time )
    {
        m_tag=tag;
        m_block_addr=block_addr;
        m_alloc_time=time;
        m_last_access_time=time;
        m_fill_time=0;
        m_status=RESERVED;

        //added by gh
        m_prefetched=false;
        m_accessed=false;
    }
    void fill( unsigned time )
    {
        assert( m_status == RESERVED );
        m_status=VALID;
        m_fill_time=time;
    }

    new_addr_type    m_tag;
    new_addr_type    m_block_addr;
    unsigned         m_alloc_time;
    unsigned         m_last_access_time;
    unsigned         m_fill_time;
    cache_block_state    m_status;

    //bits for prefetching,added by gh
    bool    m_prefetched;
    bool    m_accessed;
};

enum replacement_policy_t {
    LRU,
    FIFO
};

enum write_policy_t {
    READ_ONLY,
    WRITE_BACK,
    WRITE_THROUGH,
    WRITE_EVICT,
    LOCAL_WB_GLOBAL_WT
};

enum allocation_policy_t {
    ON_MISS,
    ON_FILL
};


enum write_allocate_policy_t {
	NO_WRITE_ALLOCATE,
	WRITE_ALLOCATE
};

enum mshr_config_t {
    TEX_FIFO,
    ASSOC // normal cache 
};

enum set_index_function{
    FERMI_HASH_SET_FUNCTION = 0,
    LINEAR_SET_FUNCTION,
    CUSTOM_SET_FUNCTION
};

class cache_config {
public:
    cache_config() 
    { 
        m_valid = false; 
        m_disabled = false;
        m_config_string = NULL; // set by option parser
        m_config_stringPrefL1 = NULL;
        m_config_stringPrefShared = NULL;
        m_data_port_width = 0;
        m_set_index_function = LINEAR_SET_FUNCTION;
    }
    void init(char * config, FuncCache status)
    {
    	cache_status= status;
        assert( config );
        char rp, wp, ap, mshr_type, wap, sif;


        int ntok = sscanf(config,"%u:%u:%u,%c:%c:%c:%c:%c,%c:%u:%u,%u:%u,%u",
                          &m_nset, &m_line_sz, &m_assoc, &rp, &wp, &ap, &wap,
                          &sif,&mshr_type,&m_mshr_entries,&m_mshr_max_merge,
                          &m_miss_queue_size, &m_result_fifo_entries,
                          &m_data_port_width);

        if ( ntok < 11 ) {
            if ( !strcmp(config,"none") ) {
                m_disabled = true;
                return;
            }
            exit_parse_error();
        }
        switch (rp) {
        case 'L': m_replacement_policy = LRU; break;
        case 'F': m_replacement_policy = FIFO; break;
        default: exit_parse_error();
        }
        switch (wp) {
        case 'R': m_write_policy = READ_ONLY; break;
        case 'B': m_write_policy = WRITE_BACK; break;
        case 'T': m_write_policy = WRITE_THROUGH; break;
        case 'E': m_write_policy = WRITE_EVICT; break;
        case 'L': m_write_policy = LOCAL_WB_GLOBAL_WT; break;
        default: exit_parse_error();
        }
        switch (ap) {
        case 'm': m_alloc_policy = ON_MISS; break;
        case 'f': m_alloc_policy = ON_FILL; break;
        default: exit_parse_error();
        }
        switch (mshr_type) {
        case 'F': m_mshr_type = TEX_FIFO; assert(ntok==13); break;
        case 'A': m_mshr_type = ASSOC; break;
        default: exit_parse_error();
        }
        m_line_sz_log2 = LOGB2(m_line_sz);
        m_nset_log2 = LOGB2(m_nset);
        m_valid = true;

        switch(wap){
        case 'W': m_write_alloc_policy = WRITE_ALLOCATE; break;
        case 'N': m_write_alloc_policy = NO_WRITE_ALLOCATE; break;
        default: exit_parse_error();
        }

        // detect invalid configuration 
        if (m_alloc_policy == ON_FILL and m_write_policy == WRITE_BACK) {
            // A writeback cache with allocate-on-fill policy will inevitably lead to deadlock:  
            // The deadlock happens when an incoming cache-fill evicts a dirty
            // line, generating a writeback request.  If the memory subsystem
            // is congested, the interconnection network may not have
            // sufficient buffer for the writeback request.  This stalls the
            // incoming cache-fill.  The stall may propagate through the memory
            // subsystem back to the output port of the same core, creating a
            // deadlock where the wrtieback request and the incoming cache-fill
            // are stalling each other.  
            assert(0 && "Invalid cache configuration: Writeback cache cannot allocate new line on fill. "); 
        }

        // default: port to data array width and granularity = line size 
        if (m_data_port_width == 0) {
            m_data_port_width = m_line_sz; 
        }
        assert(m_line_sz % m_data_port_width == 0); 

        switch(sif){
        case 'H': m_set_index_function = FERMI_HASH_SET_FUNCTION; break;
        case 'C': m_set_index_function = CUSTOM_SET_FUNCTION; break;
        case 'L': m_set_index_function = LINEAR_SET_FUNCTION; break;
        default: exit_parse_error();
        }
    }
    bool disabled() const { return m_disabled;}
    unsigned get_line_sz() const
    {
        assert( m_valid );
        return m_line_sz;
    }
    unsigned get_num_lines() const
    {
        assert( m_valid );
        return m_nset * m_assoc;
    }

    void print( FILE *fp ) const
    {
        fprintf( fp, "Size = %d B (%d Set x %d-way x %d byte line)\n", 
                 m_line_sz * m_nset * m_assoc,
                 m_nset, m_assoc, m_line_sz );
    }

    virtual unsigned set_index( new_addr_type addr ) const
    {
        if(m_set_index_function != LINEAR_SET_FUNCTION){
            printf("\nGPGPU-Sim cache configuration error: Hashing or "
                    "custom set index function selected in configuration "
                    "file for a cache that has not overloaded the set_index "
                    "function\n");
            abort();
        }
        return(addr >> m_line_sz_log2) & (m_nset-1);
    }

    new_addr_type tag( new_addr_type addr ) const
    {
        // For generality, the tag includes both index and tag. This allows for more complex set index
        // calculations that can result in different indexes mapping to the same set, thus the full
        // tag + index is required to check for hit/miss. Tag is now identical to the block address.

        //return addr >> (m_line_sz_log2+m_nset_log2);
        return addr & ~(m_line_sz-1);
    }
    new_addr_type block_addr( new_addr_type addr ) const
    {
        return addr & ~(m_line_sz-1);
    }
    FuncCache get_cache_status() {return cache_status;}
    char *m_config_string;
    char *m_config_stringPrefL1;
    char *m_config_stringPrefShared;
    FuncCache cache_status;

protected:
    void exit_parse_error()
    {
        printf("GPGPU-Sim uArch: cache configuration parsing error (%s)\n", m_config_string );
        abort();
    }

    bool m_valid;
    bool m_disabled;
    unsigned m_line_sz;
    unsigned m_line_sz_log2;
    unsigned m_nset;
    unsigned m_nset_log2;
    unsigned m_assoc;

    enum replacement_policy_t m_replacement_policy; // 'L' = LRU, 'F' = FIFO
    enum write_policy_t m_write_policy;             // 'T' = write through, 'B' = write back, 'R' = read only
    enum allocation_policy_t m_alloc_policy;        // 'm' = allocate on miss, 'f' = allocate on fill
    enum mshr_config_t m_mshr_type;

    write_allocate_policy_t m_write_alloc_policy;	// 'W' = Write allocate, 'N' = No write allocate

    union {
        unsigned m_mshr_entries;
        unsigned m_fragment_fifo_entries;
    };
    union {
        unsigned m_mshr_max_merge;
        unsigned m_request_fifo_entries;
    };
    union {
        unsigned m_miss_queue_size;
        unsigned m_rob_entries;
    };
    unsigned m_result_fifo_entries;
    unsigned m_data_port_width; //< number of byte the cache can access per cycle 
    enum set_index_function m_set_index_function; // Hash, linear, or custom set index function

    friend class tag_array;
    friend class baseline_cache;
    friend class read_only_cache;
    friend class tex_cache;
    friend class data_cache;
    friend class l1_cache;
    friend class l2_cache;
};

class l1d_cache_config : public cache_config{
public:
	l1d_cache_config() : cache_config(){}
	virtual unsigned set_index(new_addr_type addr) const;
};

class l2_cache_config : public cache_config {
public:
	l2_cache_config() : cache_config(){}
	void init(linear_to_raw_address_translation *address_mapping);
	virtual unsigned set_index(new_addr_type addr) const;

private:
	linear_to_raw_address_translation *m_address_mapping;
};

class tag_array {
public:
    // Use this constructor
    tag_array(cache_config &config, int core_id, int type_id );
    ~tag_array();

    enum cache_request_status probe( new_addr_type addr, unsigned &idx ) const;
    enum cache_request_status access( new_addr_type addr, unsigned time, unsigned &idx );
    enum cache_request_status access( new_addr_type addr, unsigned time, unsigned &idx, bool &wb, cache_block_t &evicted );

    void fill( new_addr_type addr, unsigned time );
    void fill( unsigned idx, unsigned time );
    //added by gh
    void fill( new_addr_type addr, unsigned time , bool is_prefetched);
    void fill( unsigned idx, unsigned time, bool is_prefetched );   

    unsigned size() const { return m_config.get_num_lines();}
    cache_block_t &get_block(unsigned idx) { return m_lines[idx];}

    void flush(); // flash invalidate all entries
    void new_window();

    void print( FILE *stream, unsigned &total_access, unsigned &total_misses ) const;
    float windowed_miss_rate( ) const;
    void get_stats(unsigned &total_access, unsigned &total_misses, unsigned &total_hit_res, unsigned &total_res_fail) const;

	void update_cache_parameters(cache_config &config);
protected:
    // This constructor is intended for use only from derived classes that wish to
    // avoid unnecessary memory allocation that takes place in the
    // other tag_array constructor
    tag_array( cache_config &config,
               int core_id,
               int type_id,
               cache_block_t* new_lines );
    void init( int core_id, int type_id );

protected:

    cache_config &m_config;

    cache_block_t *m_lines; /* nbanks x nset x assoc lines in total */

    unsigned m_access;
    unsigned m_miss;
    unsigned m_pending_hit; // number of cache miss that hit a line that is allocated but not filled
    unsigned m_res_fail;

    // performance counters for calculating the amount of misses within a time window
    unsigned m_prev_snapshot_access;
    unsigned m_prev_snapshot_miss;
    unsigned m_prev_snapshot_pending_hit;

    int m_core_id; // which shader core is using this
    int m_type_id; // what kind of cache is this (normal, texture, constant)
};

class mshr_table {
public:
    mshr_table( unsigned num_entries, unsigned max_merged )
    : m_num_entries(num_entries),
    m_max_merged(max_merged)
#if (tr1_hash_map_ismap == 0)
    ,m_data(2*num_entries)
#endif
    {
    }

    /// Checks if there is a pending request to the lower memory level already
    bool probe( new_addr_type block_addr ) const;
    /// Checks if there is space for tracking a new memory access
    bool full( new_addr_type block_addr ) const;
    /// Add or merge this access
    void add( new_addr_type block_addr, mem_fetch *mf );
    /// Returns true if cannot accept new fill responses
    bool busy() const {return false;}
    /// Accept a new cache fill response: mark entry ready for processing
    void mark_ready( new_addr_type block_addr, bool &has_atomic );
    /// Returns true if ready accesses exist
    bool access_ready() const {return !m_current_response.empty();}
    /// Returns next ready access
    mem_fetch *next_access();
    void display( FILE *fp ) const;

    void check_mshr_parameters( unsigned num_entries, unsigned max_merged )
    {
    	assert(m_num_entries==num_entries && "Change of MSHR parameters between kernels is not allowed");
    	assert(m_max_merged==max_merged && "Change of MSHR parameters between kernels is not allowed");
    }

private:

    // finite sized, fully associative table, with a finite maximum number of merged requests
    const unsigned m_num_entries;
    const unsigned m_max_merged;

    struct mshr_entry {
        std::list<mem_fetch*> m_list;
        bool m_has_atomic; 
        mshr_entry() : m_has_atomic(false) { }
    }; 
    typedef tr1_hash_map<new_addr_type,mshr_entry> table;
    table m_data;

    // it may take several cycles to process the merged requests
    bool m_current_response_ready;
    std::list<new_addr_type> m_current_response;
};


/***************************************************************** Caches *****************************************************************/
///
/// Simple struct to maintain cache accesses, misses, pending hits, and reservation fails.
///
struct cache_sub_stats{
    unsigned accesses;
    unsigned misses;
    unsigned pending_hits;
    unsigned res_fails;
    //added by gh
    unsigned prefetch_access;
    unsigned prefetch_misses;
    unsigned num_prefetched;
    unsigned num_unused_prefetched;

    unsigned long long port_available_cycles; 
    unsigned long long data_port_busy_cycles; 
    unsigned long long fill_port_busy_cycles; 

    cache_sub_stats(){
        clear();
    }
    void clear(){
        accesses = 0;
        misses = 0;
        pending_hits = 0;
        res_fails = 0;
        port_available_cycles = 0; 
        data_port_busy_cycles = 0; 
        fill_port_busy_cycles = 0; 
        //added by gh
        prefetch_access = 0;
        prefetch_misses = 0;
        num_prefetched = 0;
        num_unused_prefetched=0;
    }
    cache_sub_stats &operator+=(const cache_sub_stats &css){
        ///
        /// Overloading += operator to easily accumulate stats
        ///
        accesses += css.accesses;
        misses += css.misses;
        pending_hits += css.pending_hits;
        res_fails += css.res_fails;
        //added by gh
        prefetch_access += css.prefetch_access;
        prefetch_misses += css.prefetch_misses;
        num_prefetched += css.num_prefetched;
        num_unused_prefetched += css.num_unused_prefetched;

        port_available_cycles += css.port_available_cycles; 
        data_port_busy_cycles += css.data_port_busy_cycles; 
        fill_port_busy_cycles += css.fill_port_busy_cycles; 
        return *this;
    }

    cache_sub_stats operator+(const cache_sub_stats &cs){
        ///
        /// Overloading + operator to easily accumulate stats
        ///
        cache_sub_stats ret;
        ret.accesses = accesses + cs.accesses;
        ret.misses = misses + cs.misses;
        ret.pending_hits = pending_hits + cs.pending_hits;
        ret.res_fails = res_fails + cs.res_fails;
        //added by gh
        ret.prefetch_access = prefetch_access + cs.prefetch_access;
        ret.prefetch_misses = prefetch_misses + cs.prefetch_misses;
        ret.num_prefetched = num_prefetched + cs.num_prefetched;
        ret.num_unused_prefetched = num_unused_prefetched + cs.num_unused_prefetched;

        ret.port_available_cycles = port_available_cycles + cs.port_available_cycles; 
        ret.data_port_busy_cycles = data_port_busy_cycles + cs.data_port_busy_cycles; 
        ret.fill_port_busy_cycles = fill_port_busy_cycles + cs.fill_port_busy_cycles; 
        return ret;
    }

    void print_port_stats(FILE *fout, const char *cache_name) const; 
};

///
/// Cache_stats
/// Used to record statistics for each cache.
/// Maintains a record of every 'mem_access_type' and its resulting
/// 'cache_request_status' : [mem_access_type][cache_request_status]
///
class cache_stats {
public:
    cache_stats();
    void clear();
    void inc_stats(int access_type, int access_outcome);
    enum cache_request_status select_stats_status(enum cache_request_status probe, enum cache_request_status access) const;
    unsigned &operator()(int access_type, int access_outcome);
    unsigned operator()(int access_type, int access_outcome) const;
    cache_stats operator+(const cache_stats &cs);
    cache_stats &operator+=(const cache_stats &cs);
    void print_stats(FILE *fout, const char *cache_name = "Cache_stats") const;

    unsigned get_stats(enum mem_access_type *access_type, unsigned num_access_type, enum cache_request_status *access_status, unsigned num_access_status)  const;
    void get_sub_stats(struct cache_sub_stats &css) const;

    void sample_cache_port_utility(bool data_port_busy, bool fill_port_busy); 
    //added by gh
    void inc_num_prefetched(){
        m_num_prefetched++;
    }
    void inc_num_unused_prefetched(){
        m_num_unused_prefetched++;
    }
private:
    bool check_valid(int type, int status) const;

    std::vector< std::vector<unsigned> > m_stats;
    //added by gh
    unsigned m_num_prefetched;
    unsigned m_num_unused_prefetched;

    unsigned long long m_cache_port_available_cycles; 
    unsigned long long m_cache_data_port_busy_cycles; 
    unsigned long long m_cache_fill_port_busy_cycles; 
};

class cache_t {
public:
    virtual ~cache_t() {}
    virtual enum cache_request_status access( new_addr_type addr, mem_fetch *mf, unsigned time, std::list<cache_event> &events ) =  0;

    // accessors for cache bandwidth availability 
    virtual bool data_port_free() const = 0; 
    virtual bool fill_port_free() const = 0; 
};

bool was_write_sent( const std::list<cache_event> &events );
bool was_read_sent( const std::list<cache_event> &events );

/// Baseline cache
/// Implements common functions for read_only_cache and data_cache
/// Each subclass implements its own 'access' function
class baseline_cache : public cache_t {
public:
    baseline_cache( const char *name, cache_config &config, int core_id, int type_id, mem_fetch_interface *memport,
                     enum mem_fetch_status status )
    : m_config(config), m_tag_array(new tag_array(config,core_id,type_id)), 
      m_mshrs(config.m_mshr_entries,config.m_mshr_max_merge), 
      m_bandwidth_management(config) 
    {
        init( name, config, memport, status );
    }

    void init( const char *name,
               const cache_config &config,
               mem_fetch_interface *memport,
               enum mem_fetch_status status )
    {
        m_name = name;
        assert(config.m_mshr_type == ASSOC);
        m_memport=memport;
        m_miss_queue_status = status;
    }

    virtual ~baseline_cache()
    {
        delete m_tag_array;
    }

	void update_cache_parameters(cache_config &config)
	{
		m_config=config;
		m_tag_array->update_cache_parameters(config);
		m_mshrs.check_mshr_parameters(config.m_mshr_entries,config.m_mshr_max_merge);
	}

    virtual enum cache_request_status access( new_addr_type addr, mem_fetch *mf, unsigned time, std::list<cache_event> &events ) =  0;
    /// Sends next request to lower level of memory
    void cycle();
    /// Interface for response from lower memory level (model bandwidth restictions in caller)
    void fill( mem_fetch *mf, unsigned time );
    /// Checks if mf is waiting to be filled by lower memory level
    bool waiting_for_fill( mem_fetch *mf );
    /// Are any (accepted) accesses that had to wait for memory now ready? (does not include accesses that "HIT")
    bool access_ready() const {return m_mshrs.access_ready();}
    /// Pop next ready access (does not include accesses that "HIT")
    mem_fetch *next_access(){return m_mshrs.next_access();}
    // flash invalidate all entries in cache
    void flush(){m_tag_array->flush();}
    void print(FILE *fp, unsigned &accesses, unsigned &misses) const;
    void display_state( FILE *fp ) const;

    // Stat collection
    const cache_stats &get_stats() const {
        return m_stats;
    }
    unsigned get_stats(enum mem_access_type *access_type, unsigned num_access_type, enum cache_request_status *access_status, unsigned num_access_status)  const{
        return m_stats.get_stats(access_type, num_access_type, access_status, num_access_status);
    }
    void get_sub_stats(struct cache_sub_stats &css) const {
        m_stats.get_sub_stats(css);
    }

    // accessors for cache bandwidth availability 
    bool data_port_free() const { return m_bandwidth_management.data_port_free(); } 
    bool fill_port_free() const { return m_bandwidth_management.fill_port_free(); } 

protected:
    // Constructor that can be used by derived classes with custom tag arrays
    baseline_cache( const char *name,
                    cache_config &config,
                    int core_id,
                    int type_id,
                    mem_fetch_interface *memport,
                    enum mem_fetch_status status,
                    tag_array* new_tag_array )
    : m_config(config),
      m_tag_array( new_tag_array ),
      m_mshrs(config.m_mshr_entries,config.m_mshr_max_merge), 
      m_bandwidth_management(config) 
    {
        init( name, config, memport, status );
    }

protected:
    std::string m_name;
    cache_config &m_config;
    tag_array*  m_tag_array;
    mshr_table m_mshrs;
    std::list<mem_fetch*> m_miss_queue;
    enum mem_fetch_status m_miss_queue_status;
    mem_fetch_interface *m_memport;

    struct extra_mf_fields {
        extra_mf_fields()  { m_valid = false;}
        extra_mf_fields( new_addr_type a, unsigned i, unsigned d ) 
        {
            m_valid = true;
            m_block_addr = a;
            m_cache_index = i;
            m_data_size = d;
        }
        bool m_valid;
        new_addr_type m_block_addr;
        unsigned m_cache_index;
        unsigned m_data_size;
    };

    typedef std::map<mem_fetch*,extra_mf_fields> extra_mf_fields_lookup;

    extra_mf_fields_lookup m_extra_mf_fields;

    cache_stats m_stats;

    /// Checks whether this request can be handled on this cycle. num_miss equals max # of misses to be handled on this cycle
    bool miss_queue_full(unsigned num_miss){
    	  return ( (m_miss_queue.size()+num_miss) >= m_config.m_miss_queue_size );
    }
    /// Read miss handler without writeback
    void send_read_request(new_addr_type addr, new_addr_type block_addr, unsigned cache_index, mem_fetch *mf,
    		unsigned time, bool &do_miss, std::list<cache_event> &events, bool read_only, bool wa);
    /// Read miss handler. Check MSHR hit or MSHR available
    void send_read_request(new_addr_type addr, new_addr_type block_addr, unsigned cache_index, mem_fetch *mf,
    		unsigned time, bool &do_miss, bool &wb, cache_block_t &evicted, std::list<cache_event> &events, bool read_only, bool wa);

    /// Sub-class containing all metadata for port bandwidth management 
    class bandwidth_management 
    {
    public: 
        bandwidth_management(cache_config &config); 

        /// use the data port based on the outcome and events generated by the mem_fetch request 
        void use_data_port(mem_fetch *mf, enum cache_request_status outcome, const std::list<cache_event> &events); 

        /// use the fill port 
        void use_fill_port(mem_fetch *mf); 

        /// called every cache cycle to free up the ports 
        void replenish_port_bandwidth(); 

        /// query for data port availability 
        bool data_port_free() const; 
        /// query for fill port availability 
        bool fill_port_free() const; 
    protected: 
        const cache_config &m_config; 

        int m_data_port_occupied_cycles; //< Number of cycle that the data port remains used 
        int m_fill_port_occupied_cycles; //< Number of cycle that the fill port remains used 
    }; 

    bandwidth_management m_bandwidth_management; 
};

/// Read only cache
class read_only_cache : public baseline_cache {
public:
    read_only_cache( const char *name, cache_config &config, int core_id, int type_id, mem_fetch_interface *memport, enum mem_fetch_status status )
    : baseline_cache(name,config,core_id,type_id,memport,status){}

    /// Access cache for read_only_cache: returns RESERVATION_FAIL if request could not be accepted (for any reason)
    virtual enum cache_request_status access( new_addr_type addr, mem_fetch *mf, unsigned time, std::list<cache_event> &events );

    virtual ~read_only_cache(){}

protected:
    read_only_cache( const char *name, cache_config &config, int core_id, int type_id, mem_fetch_interface *memport, enum mem_fetch_status status, tag_array* new_tag_array )
    : baseline_cache(name,config,core_id,type_id,memport,status, new_tag_array){}
};

/// Data cache - Implements common functions for L1 and L2 data cache
class data_cache : public baseline_cache {
public:
    data_cache( const char *name, cache_config &config,
    			int core_id, int type_id, mem_fetch_interface *memport,
                mem_fetch_allocator *mfcreator, enum mem_fetch_status status,
                mem_access_type wr_alloc_type, mem_access_type wrbk_type )
    			: baseline_cache(name,config,core_id,type_id,memport,status)
    {
        init( mfcreator );
        m_wr_alloc_type = wr_alloc_type;
        m_wrbk_type = wrbk_type;
    }

    virtual ~data_cache() {}

    virtual void init( mem_fetch_allocator *mfcreator )
    {
        m_memfetch_creator=mfcreator;

        // Set read hit function
        m_rd_hit = &data_cache::rd_hit_base;

        // Set read miss function
        m_rd_miss = &data_cache::rd_miss_base;

        // Set write hit function
        switch(m_config.m_write_policy){
        // READ_ONLY is now a separate cache class, config is deprecated
        case READ_ONLY:
            assert(0 && "Error: Writable Data_cache set as READ_ONLY\n");
            break; 
        case WRITE_BACK: m_wr_hit = &data_cache::wr_hit_wb; break;
        case WRITE_THROUGH: m_wr_hit = &data_cache::wr_hit_wt; break;
        case WRITE_EVICT: m_wr_hit = &data_cache::wr_hit_we; break;
        case LOCAL_WB_GLOBAL_WT:
            m_wr_hit = &data_cache::wr_hit_global_we_local_wb;
            break;
        default:
            assert(0 && "Error: Must set valid cache write policy\n");
            break; // Need to set a write hit function
        }

        // Set write miss function
        switch(m_config.m_write_alloc_policy){
        case WRITE_ALLOCATE: m_wr_miss = &data_cache::wr_miss_wa; break;
        case NO_WRITE_ALLOCATE: m_wr_miss = &data_cache::wr_miss_no_wa; break;
        default:
            assert(0 && "Error: Must set valid cache write miss policy\n");
            break; // Need to set a write miss function
        }
    }

    virtual enum cache_request_status access( new_addr_type addr,
                                              mem_fetch *mf,
                                              unsigned time,
                                              std::list<cache_event> &events );
protected:
    data_cache( const char *name,
                cache_config &config,
                int core_id,
                int type_id,
                mem_fetch_interface *memport,
                mem_fetch_allocator *mfcreator,
                enum mem_fetch_status status,
                tag_array* new_tag_array,
                mem_access_type wr_alloc_type,
                mem_access_type wrbk_type)
    : baseline_cache(name, config, core_id, type_id, memport,status, new_tag_array)
    {
        init( mfcreator );
        m_wr_alloc_type = wr_alloc_type;
        m_wrbk_type = wrbk_type;
    }

    mem_access_type m_wr_alloc_type; // Specifies type of write allocate request (e.g., L1 or L2)
    mem_access_type m_wrbk_type; // Specifies type of writeback request (e.g., L1 or L2)

    //! A general function that takes the result of a tag_array probe
    //  and performs the correspding functions based on the cache configuration
    //  The access fucntion calls this function
    enum cache_request_status
        process_tag_probe( bool wr,
                           enum cache_request_status status,
                           new_addr_type addr,
                           unsigned cache_index,
                           mem_fetch* mf,
                           unsigned time,
                           std::list<cache_event>& events );

protected:
    mem_fetch_allocator *m_memfetch_creator;

    // Functions for data cache access
    /// Sends write request to lower level memory (write or writeback)
    void send_write_request( mem_fetch *mf,
                             cache_event request,
                             unsigned time,
                             std::list<cache_event> &events);

    // Member Function pointers - Set by configuration options
    // to the functions below each grouping
    /******* Write-hit configs *******/
    enum cache_request_status
        (data_cache::*m_wr_hit)( new_addr_type addr,
                                 unsigned cache_index,
                                 mem_fetch *mf,
                                 unsigned time,
                                 std::list<cache_event> &events,
                                 enum cache_request_status status );
    /// Marks block as MODIFIED and updates block LRU
    enum cache_request_status
        wr_hit_wb( new_addr_type addr,
                   unsigned cache_index,
                   mem_fetch *mf,
                   unsigned time,
                   std::list<cache_event> &events,
                   enum cache_request_status status ); // write-back
    enum cache_request_status
        wr_hit_wt( new_addr_type addr,
                   unsigned cache_index,
                   mem_fetch *mf,
                   unsigned time,
                   std::list<cache_event> &events,
                   enum cache_request_status status ); // write-through

    /// Marks block as INVALID and sends write request to lower level memory
    enum cache_request_status
        wr_hit_we( new_addr_type addr,
                   unsigned cache_index,
                   mem_fetch *mf,
                   unsigned time,
                   std::list<cache_event> &events,
                   enum cache_request_status status ); // write-evict
    enum cache_request_status
        wr_hit_global_we_local_wb( new_addr_type addr,
                                   unsigned cache_index,
                                   mem_fetch *mf,
                                   unsigned time,
                                   std::list<cache_event> &events,
                                   enum cache_request_status status );
        // global write-evict, local write-back


    /******* Write-miss configs *******/
    enum cache_request_status
        (data_cache::*m_wr_miss)( new_addr_type addr,
                                  unsigned cache_index,
                                  mem_fetch *mf,
                                  unsigned time,
                                  std::list<cache_event> &events,
                                  enum cache_request_status status );
    /// Sends read request, and possible write-back request,
    //  to lower level memory for a write miss with write-allocate
    enum cache_request_status
        wr_miss_wa( new_addr_type addr,
                    unsigned cache_index,
                    mem_fetch *mf,
                    unsigned time,
                    std::list<cache_event> &events,
                    enum cache_request_status status ); // write-allocate
    enum cache_request_status
        wr_miss_no_wa( new_addr_type addr,
                       unsigned cache_index,
                       mem_fetch *mf,
                       unsigned time,
                       std::list<cache_event> &events,
                       enum cache_request_status status ); // no write-allocate

    // Currently no separate functions for reads
    /******* Read-hit configs *******/
    enum cache_request_status
        (data_cache::*m_rd_hit)( new_addr_type addr,
                                 unsigned cache_index,
                                 mem_fetch *mf,
                                 unsigned time,
                                 std::list<cache_event> &events,
                                 enum cache_request_status status );
    enum cache_request_status
        rd_hit_base( new_addr_type addr,
                     unsigned cache_index,
                     mem_fetch *mf,
                     unsigned time,
                     std::list<cache_event> &events,
                     enum cache_request_status status );

    /******* Read-miss configs *******/
    enum cache_request_status
        (data_cache::*m_rd_miss)( new_addr_type addr,
                                  unsigned cache_index,
                                  mem_fetch *mf,
                                  unsigned time,
                                  std::list<cache_event> &events,
                                  enum cache_request_status status );
    enum cache_request_status
        rd_miss_base( new_addr_type addr,
                      unsigned cache_index,
                      mem_fetch*mf,
                      unsigned time,
                      std::list<cache_event> &events,
                      enum cache_request_status status );

};

/// This is meant to model the first level data cache in Fermi.
/// It is write-evict (global) or write-back (local) at
/// the granularity of individual blocks
/// (the policy used in fermi according to the CUDA manual)
class l1_cache : public data_cache {
public:
    l1_cache(const char *name, cache_config &config,
            int core_id, int type_id, mem_fetch_interface *memport,
            mem_fetch_allocator *mfcreator, enum mem_fetch_status status )
            : data_cache(name,config,core_id,type_id,memport,mfcreator,status, L1_WR_ALLOC_R, L1_WRBK_ACC){}

    virtual ~l1_cache(){}

    virtual enum cache_request_status
        access( new_addr_type addr,
                mem_fetch *mf,
                unsigned time,
                std::list<cache_event> &events );

protected:
    l1_cache( const char *name,
              cache_config &config,
              int core_id,
              int type_id,
              mem_fetch_interface *memport,
              mem_fetch_allocator *mfcreator,
              enum mem_fetch_status status,
              tag_array* new_tag_array )
    : data_cache( name,
                  config,
                  core_id,type_id,memport,mfcreator,status, new_tag_array, L1_WR_ALLOC_R, L1_WRBK_ACC ){}

};

/// Models second level shared cache with global write-back
/// and write-allocate policies
class l2_cache : public data_cache {
public:
    l2_cache(const char *name,  cache_config &config,
            int core_id, int type_id, mem_fetch_interface *memport,
            mem_fetch_allocator *mfcreator, enum mem_fetch_status status )
            : data_cache(name,config,core_id,type_id,memport,mfcreator,status, L2_WR_ALLOC_R, L2_WRBK_ACC){}

    virtual ~l2_cache() {}

    virtual enum cache_request_status
        access( new_addr_type addr,
                mem_fetch *mf,
                unsigned time,
                std::list<cache_event> &events );
};

/*****************************************************************************/

// See the following paper to understand this cache model:
// 
// Igehy, et al., Prefetching in a Texture Cache Architecture, 
// Proceedings of the 1998 Eurographics/SIGGRAPH Workshop on Graphics Hardware
// http://www-graphics.stanford.edu/papers/texture_prefetch/
class tex_cache : public cache_t {
public:
    tex_cache( const char *name, cache_config &config, int core_id, int type_id, mem_fetch_interface *memport,
               enum mem_fetch_status request_status, 
               enum mem_fetch_status rob_status )
    : m_config(config), 
    m_tags(config,core_id,type_id), 
    m_fragment_fifo(config.m_fragment_fifo_entries), 
    m_request_fifo(config.m_request_fifo_entries),
    m_rob(config.m_rob_entries),
    m_result_fifo(config.m_result_fifo_entries)
    {
        m_name = name;
        assert(config.m_mshr_type == TEX_FIFO);
        assert(config.m_write_policy == READ_ONLY);
        assert(config.m_alloc_policy == ON_MISS);
        m_memport=memport;
        m_cache = new data_block[ config.get_num_lines() ];
        m_request_queue_status = request_status;
        m_rob_status = rob_status;
    }

    /// Access function for tex_cache
    /// return values: RESERVATION_FAIL if request could not be accepted
    /// otherwise returns HIT_RESERVED or MISS; NOTE: *never* returns HIT
    /// since unlike a normal CPU cache, a "HIT" in texture cache does not
    /// mean the data is ready (still need to get through fragment fifo)
    enum cache_request_status access( new_addr_type addr, mem_fetch *mf, unsigned time, std::list<cache_event> &events );
    void cycle();
    /// Place returning cache block into reorder buffer
    void fill( mem_fetch *mf, unsigned time );
    /// Are any (accepted) accesses that had to wait for memory now ready? (does not include accesses that "HIT")
    bool access_ready() const{return !m_result_fifo.empty();}
    /// Pop next ready access (includes both accesses that "HIT" and those that "MISS")
    mem_fetch *next_access(){return m_result_fifo.pop();}
    void display_state( FILE *fp ) const;

    // accessors for cache bandwidth availability - stubs for now 
    bool data_port_free() const { return true; }
    bool fill_port_free() const { return true; }

    // Stat collection
    const cache_stats &get_stats() const {
        return m_stats;
    }
    unsigned get_stats(enum mem_access_type *access_type, unsigned num_access_type, enum cache_request_status *access_status, unsigned num_access_status) const{
        return m_stats.get_stats(access_type, num_access_type, access_status, num_access_status);
    }

    void get_sub_stats(struct cache_sub_stats &css) const{
        m_stats.get_sub_stats(css);
    }
private:
    std::string m_name;
    const cache_config &m_config;

    struct fragment_entry {
        fragment_entry() {}
        fragment_entry( mem_fetch *mf, unsigned idx, bool m, unsigned d )
        {
            m_request=mf;
            m_cache_index=idx;
            m_miss=m;
            m_data_size=d;
        }
        mem_fetch *m_request;     // request information
        unsigned   m_cache_index; // where to look for data
        bool       m_miss;        // true if sent memory request
        unsigned   m_data_size;
    };

    struct rob_entry {
        rob_entry() { m_ready = false; m_time=0; m_request=NULL;}
        rob_entry( unsigned i, mem_fetch *mf, new_addr_type a ) 
        { 
            m_ready=false; 
            m_index=i;
            m_time=0;
            m_request=mf; 
            m_block_addr=a;
        }
        bool m_ready;
        unsigned m_time; // which cycle did this entry become ready?
        unsigned m_index; // where in cache should block be placed?
        mem_fetch *m_request;
        new_addr_type m_block_addr;
    };

    struct data_block {
        data_block() { m_valid = false;}
        bool m_valid;
        new_addr_type m_block_addr;
    };

    // TODO: replace fifo_pipeline with this?
    template<class T> class fifo {
    public:
        fifo( unsigned size ) 
        { 
            m_size=size; 
            m_num=0; 
            m_head=0; 
            m_tail=0; 
            m_data = new T[size];
        }
        bool full() const { return m_num == m_size;}
        bool empty() const { return m_num == 0;}
        unsigned size() const { return m_num;}
        unsigned capacity() const { return m_size;}
        unsigned push( const T &e ) 
        { 
            assert(!full()); 
            m_data[m_head] = e; 
            unsigned result = m_head;
            inc_head(); 
            return result;
        }
        T pop() 
        { 
            assert(!empty()); 
            T result = m_data[m_tail];
            inc_tail();
            return result;
        }
        const T &peek( unsigned index ) const 
        { 
            assert( index < m_size );
            return m_data[index]; 
        }
        T &peek( unsigned index ) 
        { 
            assert( index < m_size );
            return m_data[index]; 
        }
        T &peek() const
        { 
            return m_data[m_tail]; 
        }
        unsigned next_pop_index() const 
        {
            return m_tail;
        }
    private:
        void inc_head() { m_head = (m_head+1)%m_size; m_num++;}
        void inc_tail() { assert(m_num>0); m_tail = (m_tail+1)%m_size; m_num--;}

        unsigned   m_head; // next entry goes here
        unsigned   m_tail; // oldest entry found here
        unsigned   m_num;  // how many in fifo?
        unsigned   m_size; // maximum number of entries in fifo
        T         *m_data;
    };

    tag_array               m_tags;
    fifo<fragment_entry>    m_fragment_fifo;
    fifo<mem_fetch*>        m_request_fifo;
    fifo<rob_entry>         m_rob;
    data_block             *m_cache;
    fifo<mem_fetch*>        m_result_fifo; // next completed texture fetch

    mem_fetch_interface    *m_memport;
    enum mem_fetch_status   m_request_queue_status;
    enum mem_fetch_status   m_rob_status;

    struct extra_mf_fields {
        extra_mf_fields()  { m_valid = false;}
        extra_mf_fields( unsigned i ) 
        {
            m_valid = true;
            m_rob_index = i;
        }
        bool m_valid;
        unsigned m_rob_index;
    };

    cache_stats m_stats;

    typedef std::map<mem_fetch*,extra_mf_fields> extra_mf_fields_lookup;

    extra_mf_fields_lookup m_extra_mf_fields;
};
typedef  new_addr_type Bound_Reg;
typedef  unsigned long long EWMA_Time;
enum List_Type{
    NONE,
    WORK_LIST,
    VERTEX_LIST,
    EDGE_LIST,
    VISIT_LIST
};
struct EWMA_Unit{
    EWMA_Time work_time;
    EWMA_Time data_time;

    EWMA_Time gen_new_ewma_time(EWMA_Time new_time);
    //ratio reg;
};
enum Prefetch_Mode{
    VERTEX,
    LARGE_NODE
};
#define ADDRALIGN 0xffffff80;
#define MAX_LINE 8
#define ALIGN_32 0xffffffe0;
#define STEP 1
class Prefetch_Unit{
public:
    Prefetch_Unit(){init();m_stat_not_finished=0;m_stat_wl_load=0;}
    ~Prefetch_Unit(){}

    void init()
    {
        m_req_q.clear();
        m_max_queue_length=10000;
        // m_double_line=false;
        // m_worklist_head=m_worklist_tail=-1;
        // m_prefetched_vid=-1;
        // m_prefetched_el_head=m_prefetched_el_tail=-1;
        // m_el_tail_ready=m_el_head_ready=false;
        // m_cur_wl_idx=-1;
        // m_prefetched_wl_idx=-1;
        wid2cur_wl.clear();//<inst, current warp wl index>
        wid2next_wl.clear();//<current wl index, next wl index>
        wid2vid.clear(); //<next wl index, prefetched vid>
        wid2num_vl_prefetched.clear();//<prefetched vertexlist addr, issued num of prefetching>
        wid2num_el_prefetched.clear();
        wid2el_addr.clear();
        wid2el_idx.clear();

    }
    
    void reinit()
    {
        init();
    }

    void update_struct_bound(new_addr_type* struct_bound){
        for(unsigned i=0; i<10; i++)
            m_bound_regs[i] = struct_bound[i];
        printf("worklist range(0x%x ~ 0x%x).\n",m_bound_regs[0],m_bound_regs[1]);
    }

    void set_worklist_band(unsigned long long start, unsigned long long end)
    {
        m_worklist_head = start;
        m_worklist_tail = end;
    }

typedef std::map<new_addr_type, unsigned long long> addr2value;
typedef std::map<unsigned, std::map<new_addr_type, unsigned long long> > wid2map;
typedef std::map<unsigned, std::map<new_addr_type, unsigned long long> >::iterator it_wid;
typedef std::map<new_addr_type, unsigned long long>::iterator it_addr;
typedef std::map<unsigned, std::map<new_addr_type, std::vector<unsigned long long> > > wid2vector;
typedef std::map<unsigned, std::map<new_addr_type, std::vector<unsigned long long> > >::iterator it_wid_vec;
typedef std::map<new_addr_type, std::vector<unsigned long long> > addr2vec;
typedef std::map<new_addr_type, std::vector<unsigned long long> >::iterator it_addr_vec;
typedef std::map<unsigned, std::map<new_addr_type, unsigned> > wid2u;
typedef std::map<unsigned, std::map<new_addr_type, unsigned> >::iterator it_wid_u;
typedef std::map<new_addr_type, unsigned> addr2u;
typedef std::map<new_addr_type, unsigned>::iterator it_addr_u;

    unsigned get_stat_wl_load() {return m_stat_wl_load;}
    unsigned get_stat_not_finished() {return m_stat_not_finished;}

    void set_cur_wl_idx(new_addr_type addr, unsigned wid, new_addr_type marked_addr) {
        assert((addr-m_bound_regs[0])%8==0);
        unsigned long long cur_wl_idx = (addr-m_bound_regs[0])/8;
        printf("add wid2cur_wl mapping. addr:0x%x, current wl index:%llu\n",addr,cur_wl_idx);
        m_stat_wl_load++;
        if(m_req_q.find(wid)==m_req_q.end()){
            std::list<mem_access_t*> req;
            req.clear();
            m_req_q.insert(std::map<unsigned, std::list<mem_access_t*> >::value_type(wid,req));
        }
        if(is_prefetching(addr,wid)){
            m_stat_not_finished++;
            m_req_q[wid].clear();
        }
        it_wid it = wid2cur_wl.find(wid);
        if(it!=wid2cur_wl.end()){
            it_addr it2 = it->second.find(marked_addr);
            assert(it2==it->second.end());
            wid2cur_wl[wid][marked_addr] = cur_wl_idx;
        } else {
            addr2value tmp;
            tmp[marked_addr]=cur_wl_idx;
            wid2cur_wl.insert(std::map<unsigned long long, std::map<new_addr_type, unsigned long long> >::value_type(wid, tmp));
        }
    }

    bool is_full(){return m_req_q.size()==m_max_queue_length;}

    bool is_visit(new_addr_type addr){
        return addr>=m_bound_regs[6]&&addr<m_bound_regs[7];
    }

    void new_load_addr(new_addr_type addr, unsigned wid, new_addr_type marked_addr)
    {
        it_wid it = wid2cur_wl.find(wid);
        assert(it!=wid2cur_wl.end());
        it_addr it2 = it->second.find(marked_addr);

        // if(!is_full()){
        List_Type type = addr_filter(addr);
        if(type==WORK_LIST && it!=wid2cur_wl.end() && it2!=it->second.end()){
            unsigned long long cur_wl = it2->second;
            unsigned long long next_addr = m_bound_regs[0]+8*(cur_wl+STEP);
            // next_addr &= ADDRALIGN;

            if(next_addr>=m_bound_regs[0]&&next_addr<m_bound_regs[1])
            {
                next_addr &= ADDRALIGN;
                //it_wid it3 = wid2next_wl.find(wid);
                if(wid2next_wl.find(wid)==wid2next_wl.end()){
                    addr2value tmp;
                    tmp[marked_addr]=cur_wl+STEP;
                    wid2next_wl.insert(wid2map::value_type(wid, tmp));
                } else{
                    it_addr it3 = wid2next_wl[wid].find(marked_addr);
                    if(it3==wid2next_wl[wid].end()){
                        wid2next_wl[wid][marked_addr] = cur_wl+STEP;
                    } else {
                        printf("already has a mapping. wid(%u), marked_addr(0x%x), next_wl_index(%llu)\n",wid, marked_addr, wid2next_wl[wid][marked_addr]);
                        exit(1);
                    }
                }
                printf("current wl index:%llu, next_wl_index_addr:0x%x\n", cur_wl, next_addr);
                gen_prefetch_worklist(next_addr, wid, marked_addr);
            } 
            wid2cur_wl[wid].erase(it2);
            if(wid2cur_wl[wid].size()==0)
                wid2cur_wl.erase(it);
        } 
        // else if(type==EDGE_LIST){
        //     gen_prefetch_edgelist(addr, wid, marked_addr);
        // }
        
    }

    void prefetched_data(unsigned long long* pre_data, new_addr_type addr, unsigned wid, new_addr_type marked_addr){
        List_Type type = addr_filter(addr);
        new_addr_type el_head_addr, el_tail_addr;
        new_addr_type vid_addr, next_vid_addr, el_addr,prefetch_vl_addr;

        unsigned long long prefetched_next_wl_idx, prefetched_vid;
        unsigned long long m_prefetched_vid, el_idx;

        it_wid next_wl_it, vid_it;
        it_addr next_wl_it2, vid_it2;
        it_wid_vec el_idx_it;
        it_addr_vec el_idx_it2;
        it_wid_u num_prefetch_it;
        it_addr_u num_prefetch_it2;

        std::vector<unsigned long long> el_idx_vec;

        addr2value tmp2;
        addr2u tmp;
        addr2vec tmp1;


        switch(type){
            case WORK_LIST:
                next_wl_it = wid2next_wl.find(wid);
                assert(next_wl_it!=wid2next_wl.end());
                next_wl_it2 = next_wl_it->second.find(marked_addr);
                assert(next_wl_it2!=wid2next_wl[wid].end());
                prefetched_next_wl_idx = wid2next_wl[wid][marked_addr];

                next_wl_it->second.erase(next_wl_it2);
                if(wid2next_wl[wid].size()==0)
                    wid2next_wl.erase(next_wl_it);

                prefetched_vid = pre_data[prefetched_next_wl_idx%16];//假设worklist是128B对齐的并且每个item是8B,那么cacheline的offset就是模16

                vid_it = wid2vid.find(wid);
                if(vid_it==wid2vid.end()){
                    tmp2[marked_addr]=prefetched_vid;
                    wid2vid.insert(wid2map::value_type(wid, tmp2));
                } else{
                    vid_it2 = vid_it->second.find(marked_addr);
                    if(vid_it2==vid_it->second.end()){
                        vid_it->second[marked_addr] = prefetched_vid;
                    } else {
                        printf("already has a mapping. prefetched_wl_index(%llu), prefetched_vid(%llu)\n",prefetched_next_wl_idx,wid2vid[wid][marked_addr]);
                        exit(1);
                    }
                }
                
                el_head_addr = m_bound_regs[2] + prefetched_vid/16*128 + (prefetched_vid%16)*8;//计算需要访问vertex结构的地址，并128B对齐
                el_tail_addr = el_head_addr+8;
                el_head_addr &= ADDRALIGN;
                el_tail_addr &= ADDRALIGN;

                if(el_tail_addr == el_head_addr){
                    num_prefetch_it = wid2num_vl_prefetched.find(wid);
                    if(num_prefetch_it==wid2num_vl_prefetched.end()){
                        tmp[marked_addr]=1;
                        wid2num_vl_prefetched.insert(wid2u::value_type(wid, tmp));
                    } else{
                        num_prefetch_it2 = num_prefetch_it->second.find(marked_addr);
                        assert(num_prefetch_it2==num_prefetch_it->second.end());
                        num_prefetch_it->second[marked_addr]=1;
                    }
                    //assert(wid2num_vl_prefetched.find(wid)==wid2num_vl_prefetched.end());
                    // wid2num_vl_prefetched[wid]=1;
                   
                    // assert(inst2el_addr.find(inst)==inst2el_addr.end());
                    // inst2el_addr[inst].push_back(el_head_addr);
                    // inst2el_addr[inst].push_back(el_tail_addr);
                    gen_prefetch_vertexlist(el_head_addr,wid,marked_addr); 
                }
                else {
                    num_prefetch_it = wid2num_vl_prefetched.find(wid);
                    if(num_prefetch_it==wid2num_vl_prefetched.end()){
                        tmp[marked_addr]=2;
                        wid2num_vl_prefetched.insert(wid2u::value_type(wid, tmp));
                    } else{
                        num_prefetch_it2 = num_prefetch_it->second.find(marked_addr);
                        assert(num_prefetch_it2==num_prefetch_it->second.end());
                        num_prefetch_it->second[marked_addr]=2;
                    }
                    // assert(wid2num_vl_prefetched.find(wid)==wid2num_vl_prefetched.end());
                    // wid2num_vl_prefetched[wid]=2;
                    
                    // assert(inst2el_addr.find(inst)==inst2el_addr.end());
                    // inst2el_addr[inst].push_back(el_head_addr);
                    // inst2el_addr[inst].push_back(el_tail_addr);
                    
                    gen_prefetch_vertexlist(el_head_addr,wid,marked_addr);
                    gen_prefetch_vertexlist(el_tail_addr,wid,marked_addr);
                }
                break;
            case VERTEX_LIST:
                assert(wid2vid.find(wid)!=wid2vid.end());
                assert(wid2vid[wid].find(marked_addr)!=wid2vid[wid].end());
                m_prefetched_vid = wid2vid[wid][marked_addr];
                vid_addr = m_bound_regs[2] + (m_prefetched_vid/16)*128 + (m_prefetched_vid%16)*8;
                next_vid_addr = vid_addr+8;
                vid_addr &= ADDRALIGN;
                next_vid_addr &= ADDRALIGN;

                

                assert(wid2num_vl_prefetched.find(wid)!=wid2num_vl_prefetched.end());
                //assert(wid2el_idx.find(wid)==wid2el_idx.end()||wid2el_idx[wid].size()<2);
                // if(m_double_line){
                el_idx_vec.push_back(-1);
                el_idx_vec.push_back(-1);
                el_idx_it = wid2el_idx.find(wid);
                if(el_idx_it==wid2el_idx.end()){
                    tmp1[marked_addr] = el_idx_vec;
                    wid2el_idx.insert(wid2vector::value_type(wid,tmp1));
                } else{
                    el_idx_it2 = wid2el_idx[wid].find(marked_addr);
                    if(el_idx_it2==wid2el_idx[wid].end())
                        wid2el_idx[wid][marked_addr]=el_idx_vec;
                }

                if(wid2num_vl_prefetched[wid][marked_addr]==1){
                    assert(addr==vid_addr&&addr==next_vid_addr);
                    wid2el_idx[wid][marked_addr][0]=pre_data[m_prefetched_vid%16];
                    wid2el_idx[wid][marked_addr][1]=pre_data[(m_prefetched_vid+1)%16];
                } else {
                    assert(wid2num_vl_prefetched[wid][marked_addr]==2);
                    assert(vid_addr!=next_vid_addr);
                    if(addr==vid_addr)
                        wid2el_idx[wid][marked_addr][0]=pre_data[m_prefetched_vid%16];
                    else if(addr==next_vid_addr)
                        wid2el_idx[wid][marked_addr][1]=pre_data[(m_prefetched_vid+1)%16];
                }

                if(addr != vid_addr && addr != next_vid_addr) {
                    printf("no addr matched.vid_addr(0x%x), next_vid_addr(0x%x), addr(0x%x)\n",vid_addr,next_vid_addr,addr);
                    exit(1);
                }

                if(wid2el_idx[wid][marked_addr][0]!=-1&&wid2el_idx[wid][marked_addr][1]!=-1){
                    // el_idx = wid2el_idx[wid][0];
                    // // el_tail = inst2el_idx[inst][1];
                    // if(el_idx>wid2el_idx[wid][1]){
                    //     wid2el_idx[wid][0] = wid2el_idx[wid][1];
                    //     wid2el_idx[wid][1] = el_idx;
                    //     // gen_prefetch_edgelist_on_vertex(el_tail,el_head,inst);
                    // }
                    wid2num_vl_prefetched[wid].erase(wid2num_vl_prefetched[wid].find(marked_addr));
                    if(wid2num_vl_prefetched[wid].size()==0){
                        wid2num_vl_prefetched.erase(wid2num_vl_prefetched.find(wid));
                    }
                    vid_it = wid2vid.find(wid);
                    vid_it2 = vid_it->second.find(marked_addr);
                    vid_it->second.erase(vid_it2);
                    if(wid2vid[wid].size()==0)
                        wid2vid.erase(vid_it);
                    gen_prefetch_edgelist_on_vertex(wid2el_idx[wid][marked_addr][0],wid2el_idx[wid][marked_addr][1],wid,marked_addr);
                }
            break;
            case EDGE_LIST:
                el_addr = addr;
                assert(wid2el_idx.find(wid)!=wid2el_idx.end());
                assert(wid2el_idx[wid].find(marked_addr)!=wid2el_idx[wid].end());
                for(unsigned i=0; i<16; i++){
                    if(el_addr+i*8<m_bound_regs[6]+8*wid2el_idx[wid][marked_addr][1])
                    {
                        prefetch_vl_addr = m_bound_regs[6] + pre_data[i]*4;
                        gen_prefetch_visitedlist(prefetch_vl_addr,wid,marked_addr);
                    }
                }
                assert(wid2num_el_prefetched.find(wid)!=wid2num_el_prefetched.end());
                assert(wid2num_el_prefetched[wid].find(marked_addr)!=wid2num_el_prefetched[wid].end());
                wid2num_el_prefetched[wid][marked_addr]--;
                if(wid2num_el_prefetched[wid][marked_addr]==0)
                {
                    wid2el_idx[wid].erase(wid2el_idx[wid].find(marked_addr));
                    wid2num_el_prefetched[wid].erase(wid2num_el_prefetched[wid].find(marked_addr));
                    if(wid2el_idx[wid].size()==0)
                    {
                        el_idx_it = wid2el_idx.find(wid);
                        wid2el_idx.erase(el_idx_it);
                    }
                    if(wid2num_el_prefetched[wid].size()==0){
                        wid2num_el_prefetched.erase(wid2num_el_prefetched.find(wid));
                    }
                }
            break;
            default:    
            break;
        }
    }

    List_Type addr_filter(new_addr_type addr)
    {
        if((addr>=m_bound_regs[0]&&addr<m_bound_regs[1]))
            return WORK_LIST;
        else if(addr>=m_bound_regs[2] && addr < m_bound_regs[3])
            return VERTEX_LIST;
        else if(addr >= m_bound_regs[4] && addr < m_bound_regs[5])
            return EDGE_LIST;
        else if(addr >= m_bound_regs[6] && addr < m_bound_regs[7])
            return VISIT_LIST;
        else return NONE;
    }

    // void gen_prefetch_requests(new_addr_type addr, List_Type type, unsigned wid, new_addr_type marked_addr)//统一入口
    // {
    //     switch(type){
    //         case WORK_LIST: 
                //assert(addr%128==0);
                //printf("current worklist index:%llu\n",m_cur_wl_idx);
                // if(addr< m_bound_regs[1]){
                // gen_prefetch_worklist(addr,wid,marked_addr);
                    //m_prefetched_wl_idx = m_cur_wl_idx+1;
                // }
                // break;
            // case VERTEX_LIST: gen_prefetch_vertexlist(addr);break;
            // case EDGE_LIST:  if((addr-m_bound_regs[4])%(4*128)==0) gen_prefetch_edgelist(addr); break;
            // case VISIT_LIST:   gen_prefetch_visitedlist(addr);break;
    //         default: break;
    //     }
    // }

    void gen_prefetch_worklist(new_addr_type addr, unsigned wid, new_addr_type marked_addr)//generate worklist prefetch, push reqs into req_q
    {
        printf("generate worklist prefetch\n");
        assert(addr>=m_bound_regs[0]&&addr<m_bound_regs[1]);
        mem_access_t* access = new mem_access_t(GLOBAL_ACC_R, addr, 128, false, wid,marked_addr);
        m_req_q[wid].push_back(access);
    }
    void gen_prefetch_vertexlist(new_addr_type addr, unsigned wid, new_addr_type marked_addr)//generate vertexlist prefetch, push reqs into req_q
    {
        printf("generate vertexlist prefetch\n");
        assert(addr>=m_bound_regs[2]&&addr<m_bound_regs[3]);
        mem_access_t* access = new mem_access_t(GLOBAL_ACC_R, addr, 128, false, wid,marked_addr);
        m_req_q[wid].push_back(access);
    }
    void gen_prefetch_edgelist(new_addr_type addr, unsigned wid, new_addr_type marked_addr)//generate edgelist prefetch, push reqs into req_q
    {
        printf("generate edgelist prefetch\n");
        for(unsigned i=1;i<5;i++){
            new_addr_type next_addr = addr + 128*(4+i);
            if(next_addr>=m_bound_regs[5]||next_addr<m_bound_regs[4])
                break;
            mem_access_t* access = new mem_access_t(GLOBAL_ACC_R, next_addr, 128, false, wid,marked_addr);
            m_req_q[wid].push_back(access);
        }
    }
    void gen_prefetch_edgelist_on_vertex(unsigned long long start_offset, unsigned long long end_offset, unsigned wid, new_addr_type marked_addr)
    {
        printf("generate edgelist prefetch on vertex\n");

        unsigned long long length = 8*(end_offset-start_offset);
        if(length%128) length = length/128+1;
        else length /=128;

        unsigned max_lines = (length>MAX_LINE)?MAX_LINE:length;


        it_wid_u num_el_prefetch_it = wid2num_el_prefetched.find(wid);
        if(num_el_prefetch_it==wid2num_el_prefetched.end()){
            addr2u tmp;
            tmp[marked_addr]=max_lines;
            wid2num_el_prefetched.insert(wid2u::value_type(wid, tmp));
        } else{
            it_addr_u num_el_prefetch_it2 = wid2num_el_prefetched[wid].find(marked_addr);
            assert(num_el_prefetch_it2==wid2num_el_prefetched[wid].end());
            wid2num_el_prefetched[wid][marked_addr]=max_lines;
        }   
        
        for(unsigned i=0;i<max_lines;i++){
            new_addr_type next_addr = m_bound_regs[4] + start_offset*8 + 128*i;
            if(next_addr >= m_bound_regs[5] || next_addr < m_bound_regs[4])
                break;
            mem_access_t* access = new mem_access_t(GLOBAL_ACC_R, next_addr, 128, false, wid,marked_addr);
            m_req_q[wid].push_back(access);
        }
    }
    void gen_prefetch_visitedlist(new_addr_type addr, unsigned wid, new_addr_type marked_addr)//generate visited list prefetch, push reqs into req_q
    {
        printf("generate visitlist prefetch\n");
        assert(addr>=m_bound_regs[6]&&addr<m_bound_regs[7]);
        mem_access_t* access = new mem_access_t(GLOBAL_ACC_R, addr, 128, false,wid,marked_addr);
        m_req_q[wid].push_back(access);
    }

    bool is_prefetching(new_addr_type addr, unsigned wid)
    {
        if(req_in_queue(addr,wid)||waiting_for_data(addr,wid))
            return true;
        else return false;
    }

    bool req_in_queue(new_addr_type addr, unsigned wid)
    {
        if(addr==m_bound_regs[0])
            return false;
        new_addr_type marked_addr = addr-8;
        std::list<mem_access_t*>::iterator it = m_req_q[wid].begin();
        for(;it!=m_req_q.end();it++){
            if((*it)->get_marked_addr()==addr)
                return true;
        }
        return false;
    }

    bool waiting_for_data(new_addr_type addr, unsigned wid)
    {
        if(addr==m_bound_regs[0])
            return false;
        addr -= 8;
        if(wid2next_wl.find(wid)!=wid2next_wl.end()){
            if(wid2next_wl[wid].find(addr)!=wid2next_wl[wid].end())
                return true;
        }
         
        if(wid2vid.find(wid)!=wid2vid.end()){
            if(wid2vid[wid].find(addr)!=wid2vid[wid].end())
                return true;
        }
        
        if(wid2num_vl_prefetched.find(wid)!=wid2num_vl_prefetched.end()){
            if(wid2num_vl_prefetched[wid].find(addr)!=wid2num_vl_prefetched[wid].end())
                return true;
        }
            // return true;
        if(wid2num_el_prefetched.find(wid)!=wid2num_el_prefetched.end()){
            if(wid2num_el_prefetched[wid].find(addr)!=wid2num_el_prefetched[wid].end())
                return true;
        }
            // return true;
        if(wid2el_addr.find(wid)!=wid2el_addr.end()){
            if(wid2el_addr[wid].find(addr)!=wid2el_addr[wid].end())
                return true;
        }
            // return true;
        if(wid2el_idx.find(wid)!=wid2el_idx.end()){
            if(wid2el_idx[wid].find(wid)!=wid2el_idx[wid].end())
                return true;
        }
            // return true;
        return false;
    }

    mem_access_t* pop_from_top(unsigned wid) {return m_req_q[wid].front();}
    void del_req_from_top(unsigned wid) {
        m_req_q[wid].pop_front();
    }
    bool queue_empty(unsigned wid) {return m_req_q[wid].size()==0;}
    bool all_queue_empty() {
        std::map<unsigned , std::list<mem_access_t*> >::iterator iter = m_req_q.begin();
        for(;iter!=m_req_q.end();iter++){
            if(iter->size()!=0)
                return false;
        }
        return true;
    }
    Bound_Reg m_bound_regs[10];

    
private:
    //worklist, vertexlist, edgelist, visitedlist, out_worklist. (start, end)
    //EWMA_Unit m_ewma;
    std::map<unsigned, std::list<mem_access_t*> >m_req_q;//added by gh

    // std::list<mem_access_t*> m_prior_q;
    //Prefetch_Mode m_mode;
    unsigned m_max_queue_length;
    bool m_double_line;

    unsigned long long m_worklist_head, m_worklist_tail;//整个GPU共享work list的addr range

    wid2map wid2cur_wl;//<inst, current warp wl index>
    wid2map wid2next_wl;//<current wl index, next wl index>
    wid2map wid2vid; //<next wl index, prefetched vid>
    wid2u wid2num_vl_prefetched;//<prefetched vertexlist addr, issued num of prefetching>
    wid2u wid2num_el_prefetched;
    wid2vector wid2el_addr;
    wid2vector wid2el_idx;

    unsigned m_stat_wl_load;
    unsigned m_stat_not_finished;
};

#endif
