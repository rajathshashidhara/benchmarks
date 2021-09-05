/*
 * Copyright 2019 University of Washington, Max Planck Institute for
 * Software Systems, and The University of Texas at Austin
 *
 * Permission is hereby granted, free of charge, to any person obtaining
 * a copy of this software and associated documentation files (the
 * "Software"), to deal in the Software without restriction, including
 * without limitation the rights to use, copy, modify, merge, publish,
 * distribute, sublicense, and/or sell copies of the Software, and to
 * permit persons to whom the Software is furnished to do so, subject to
 * the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
 * IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
 * CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
 * TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
 * SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <assert.h>

#include <rte_config.h>
#include <rte_memcpy.h>
#include <rte_malloc.h>
#include <rte_lcore.h>
#include <rte_ether.h>
#include <rte_ethdev.h>
#include <rte_mempool.h>
#include <rte_mbuf.h>
#include <rte_random.h>
#include <rte_spinlock.h>
#include <rte_ip.h>
#include <rte_cycles.h>

#include <utils.h>
#include <packet_defs.h>

#define BUFFER_SIZE 2048
#define PERTHREAD_MBUFS 2048
#define RING_SIZE       (4 * PERTHREAD_MBUFS)
#define MBUF_SIZE (BUFFER_SIZE + sizeof(struct rte_mbuf) + RTE_PKTMBUF_HEADROOM)
#define RX_DESCRIPTORS 128
#define TX_DESCRIPTORS 128

#define BATCH_SIZE 32

struct queue {
  uint64_t mac;
  beui32_t ip;
};

static int network_init(unsigned num_rx, unsigned num_tx);
static int network_rx_thread_init(unsigned queue);
static int network_tx_thread_init(unsigned queue);
static struct rte_mempool *mempool_alloc(size_t count);

#define MAX_WORKERS 32
static const uint8_t port_id = 0;
static const uint8_t num_workers = 1;

static const struct rte_eth_conf port_conf = {
    .rxmode = {
      .mq_mode = ETH_MQ_RX_RSS,
    },
    .txmode = {
      .mq_mode = ETH_MQ_TX_NONE,
    },
    .rx_adv_conf = {
      .rss_conf = {
        .rss_hf = ETH_RSS_NONFRAG_IPV4_TCP,
      },
    }
  };

static struct rte_eth_dev_info eth_devinfo;
static struct rte_ether_addr eth_addr;
static size_t queues_num;
static struct queue *queues;

struct rte_mempool *pool[MAX_WORKERS];
struct rte_ring *rx_to_tx[MAX_WORKERS];

static uint64_t stat_rx = 0;
static uint64_t stat_tx = 0;
static uint64_t stat_tail_drops = 0;
static uint64_t stat_rnd_drops = 0;

static uint32_t rnd_drop_prob = 0;

static int network_init(unsigned num_rx, unsigned num_tx)
{
  int ret;
  unsigned count;

  /* make sure there is only one port */
  count = rte_eth_dev_count_avail();
  if (count == 0) {
    fprintf(stderr, "No ethernet devices\n");
    return -1;
  } else if (count > 1) {
    fprintf(stderr, "Multiple ethernet devices\n");
    return -1;
  }

  /* initialize port */
  ret = rte_eth_dev_configure(port_id, num_rx, num_tx, &port_conf);
  if (ret < 0) {
    fprintf(stderr, "rte_eth_dev_configure failed\n");
    return -1;
  }

  /* get mac address and device info */
  rte_eth_macaddr_get(port_id, &eth_addr);

  return 0;
}

static int network_rx_thread_init(unsigned queue)
{
  int ret;

  /* allocate pool */
  if ((pool[queue] = mempool_alloc(PERTHREAD_MBUFS)) == NULL) {
    fprintf(stderr, "mempool_alloc failed\n");
    return -1;
  }

  /* initialize queue */
  ret = rte_eth_rx_queue_setup(port_id, queue, RX_DESCRIPTORS,
          rte_socket_id(), &eth_devinfo.default_rxconf, pool[queue]);
  if (ret != 0) {
    return -1;
  }

  return 0;
}

static int network_tx_thread_init(unsigned queue)
{
  int ret;
  char ring_name[256];

  /* initialize queue */
  ret = rte_eth_tx_queue_setup(port_id, queue, TX_DESCRIPTORS,
          rte_socket_id(), &eth_devinfo.default_txconf);
  if (ret != 0) {
    fprintf(stderr, "network_tx_thread_init: rte_eth_tx_queue_setup failed\n");
    return -1;
  }

  snprintf(ring_name, 256, "rx_to_tx-%u", queue);
  rx_to_tx[queue] = rte_ring_create(ring_name, PERTHREAD_MBUFS, rte_socket_id(), RING_F_SP_ENQ | RING_F_SC_DEQ);
  if (rx_to_tx[queue] == NULL) {
    return -1;
  }

  return 0;
}

static struct rte_mempool *mempool_alloc(size_t bufs)
{
  static unsigned pool_id = 0;
  unsigned n;
  char name[32];
  n = __sync_fetch_and_add(&pool_id, 1);
  snprintf(name, 32, "mbuf_pool_%u\n", n);
  return rte_mempool_create(name, bufs, MBUF_SIZE, 32,
          sizeof(struct rte_pktmbuf_pool_private), rte_pktmbuf_pool_init, NULL,
          rte_pktmbuf_init, NULL, rte_socket_id(), 0);
}

static inline int is_local_ip(beui32_t bip)
{
  uint32_t i;
  uint32_t ip = f_beui32(bip);

  if ((ip & 0xff) != 254)
    return 0;

  for (i = 0; i < queues_num; i++) {
    if ((f_beui32(queues[i].ip) >> 8) == (ip >> 8))
      return 1;
  }

  return 0;
}

static inline unsigned handle_rx_arp(struct rte_mbuf *mb)
{
  struct pkt_arp *pa = rte_pktmbuf_mtod(mb, struct pkt_arp *);
  beui32_t sip;

  if (f_beui16(pa->arp.oper) != ARP_OPER_REQUEST ||
      f_beui16(pa->arp.htype) != ARP_HTYPE_ETHERNET ||
      f_beui16(pa->arp.ptype) != ARP_PTYPE_IPV4 ||
      pa->arp.hlen != 6 || pa->arp.plen != 4 ||
      !is_local_ip(pa->arp.tpa))
  {
    return 1;
  }

  fprintf(stderr, "handle_rx_arp: answering ARP for %x\n", f_beui32(pa->arp.tpa));
  memcpy(&pa->eth.dest, &pa->arp.sha, ETH_ADDR_LEN);
  memcpy(&pa->arp.tha, &pa->arp.sha, ETH_ADDR_LEN);
  memcpy(&pa->eth.src, &eth_addr, ETH_ADDR_LEN);
  memcpy(&pa->arp.sha, &eth_addr, ETH_ADDR_LEN);
  sip = pa->arp.spa;
  pa->arp.spa = pa->arp.tpa;
  pa->arp.tpa = sip;
  pa->arp.oper = t_beui16(ARP_OPER_REPLY);

  return 0;
}

static inline struct queue *find_queue(beui32_t dip)
{
  uint32_t i;
  for (i = 0; i < queues_num; i++) {
    if (queues[i].ip.x == dip.x)
      return &queues[i];
  }
  return NULL;
}

/** Relative timestamp, ignoring wrap-arounds */
static inline unsigned int loss_event_random()
{
  return (uint32_t) rte_rand();
}

static inline unsigned handle_rx_ip(struct rte_mbuf *mb)
{
  struct pkt_ip *pi = rte_pktmbuf_mtod(mb, struct pkt_ip *);
  struct queue *q;

  /* random drops, if enabled */
  if (rnd_drop_prob != 0) {
    if (loss_event_random() <= rnd_drop_prob) {
      stat_rnd_drops++;
      goto drop;
    }
  }

  if (memcmp(&pi->eth.dest, &eth_addr, ETH_ADDR_LEN) != 0 ||
      (q = find_queue(pi->ip.dest)) == NULL)
  {
    goto drop;
  }

  /* update macs */
  memcpy(&pi->eth.src, &eth_addr, ETH_ADDR_LEN);
  memcpy(&pi->eth.dest, &q->mac, ETH_ADDR_LEN);

  return 0;

drop:
  return 1;
}

static inline void pktmbuf_free_bulk(struct rte_mbuf *mbs[], unsigned int cnt)
{
  unsigned int i;
  for (i = 0; i < cnt; i++) {
    rte_pktmbuf_free(mbs[i]);
  }
}

static void process_packets(int queue)
{
  unsigned num, i, ret, cnt_fwd, cnt_drop;
  struct rte_mbuf *mbs[BATCH_SIZE], *mbs_fwd[BATCH_SIZE], *mbs_drop[BATCH_SIZE];
  struct eth_hdr *eh;

  num = rte_eth_rx_burst(port_id, queue, mbs, BATCH_SIZE);
  cnt_fwd = cnt_drop = 0;

  stat_rx += num;

  for (i = 0; i < num; i++) {
    eh = rte_pktmbuf_mtod(mbs[i], struct eth_hdr *);
    if (f_beui16(eh->type) == ETH_TYPE_IP) {
      ret = handle_rx_ip(mbs[i]);
    } else if (f_beui16(eh->type) == ETH_TYPE_ARP) {
      ret = handle_rx_arp(mbs[i]);
    } else {
      ret = 1;
    }

    if (ret) {
      mbs_drop[cnt_drop++] = mbs[i];
    }
    else {
      mbs_fwd[cnt_fwd++] = mbs[i];
    }
  }

  if (cnt_fwd) {

    ret = rte_eth_tx_burst(port_id, queue, mbs_fwd, cnt_fwd);
    for (i = ret; i < cnt_fwd; i++) {
      mbs_drop[cnt_drop++] = mbs_fwd[i];
      stat_tail_drops++;
    }
  }

  if (cnt_drop) {
    pktmbuf_free_bulk(mbs_drop, cnt_drop);
  }
}

static void receive_packets(int queue)
{
  unsigned num, i, ret, cnt_fwd, cnt_drop;
  struct rte_mbuf *mbs[BATCH_SIZE], *mbs_fwd[BATCH_SIZE], *mbs_drop[BATCH_SIZE];
  struct eth_hdr *eh;

  num = rte_eth_rx_burst(port_id, queue, mbs, BATCH_SIZE);
  cnt_fwd = cnt_drop = 0;

  stat_rx += num;

  for (i = 0; i < num; i++) {
    eh = rte_pktmbuf_mtod(mbs[i], struct eth_hdr *);
    if (f_beui16(eh->type) == ETH_TYPE_IP) {
      ret = handle_rx_ip(mbs[i]);
    } else if (f_beui16(eh->type) == ETH_TYPE_ARP) {
      ret = handle_rx_arp(mbs[i]);
    } else {
      ret = 1;
    }

    if (ret) {
      mbs_drop[cnt_drop++] = mbs[i];
    }
    else {
      mbs_fwd[cnt_fwd++] = mbs[i];
    }
  }

  if (cnt_fwd) {

    ret = rte_ring_sp_enqueue_burst(rx_to_tx[queue], mbs_fwd, cnt_fwd, NULL);
    for (i = ret; i < cnt_fwd; i++) {
      mbs_drop[cnt_drop++] = mbs_fwd[i];
      stat_tail_drops++;
    }
  }

  if (cnt_drop) {
    pktmbuf_free_bulk(mbs_drop, cnt_drop);
  }
}

static void transmit_packets(int queue)
{
  struct rte_mbuf *mbs[BATCH_SIZE], *mbs_free[BATCH_SIZE];
  size_t num = 0, drop, tx;

  num = rte_ring_sc_dequeue_burst(rx_to_tx[queue], mbs, BATCH_SIZE, NULL);

  if (num > 0) {
    tx = rte_eth_tx_burst(port_id, queue, mbs, num);

    stat_tx += tx;
    for (drop = 0; (tx + drop) < num; drop++) {
      mbs_free[drop] = mbs[tx + drop];
      stat_tail_drops++;
    }

    if (drop) {
      pktmbuf_free_bulk(mbs_free, drop);
    }
  }
}

#define RX_THREAD 1
#define TX_THREAD 2
static int run_thread(void *arg)
{
  int lcore_id, worker_id;
  lcore_id = rte_lcore_id();

  // lcore_id is 1-indexed
  lcore_id -= 1;
  assert(lcore_id >= 0 && lcore_id < (2 * num_workers));

  // RX thread
  worker_id = lcore_id / 2;
  if (lcore_id % 2 == 0) {
    while (1) {
      receive_packets(worker_id);
    }
  }
  else {
    while (1) {
      transmit_packets(worker_id);
    }
  }

  return 0;
}

static int worker_thread(void *arg)
{
  int lcore_id, worker_id;
  lcore_id = rte_lcore_id();

  // lcore_id is 1-indexed
  lcore_id -= 1;
  assert(lcore_id >= 0 && lcore_id < num_workers);

  worker_id = lcore_id;
  while (1)
  {
    process_packets(worker_id);
  }

  return 0;
}

static inline int parse_int32(const char *s, uint32_t *pi)
{
  char *end;
  *pi = strtoul(s, &end, 10);
  if (!*s || *end)
    return -1;
  return 0;
}

static inline int parse_double(const char *s, double *pd)
{
  char *end;
  *pd = strtod(s, &end);
  if (!*s || *end)
    return -1;
  return 0;
}

static int parse_queue(char *arg, struct queue *q)
{
  char *mac;
  uint32_t ip;

  /* separate parts by commas */
  if ((mac = strchr(arg, ',')) == NULL)
  {
    fprintf(stderr, "Not all 3 commas in argument found\n");
    return -1;
  }
  *mac = 0;
  mac++;

  /* parse IP */
  if (util_parse_ipv4(arg, &ip) != 0) {
    fprintf(stderr, "parsing IP failed (%s)\n", arg);
    return -1;
  }
  q->ip = t_beui32(ip);

  /* parse MAC */
  if (util_parse_mac(mac, &q->mac) != 0) {
    fprintf(stderr, "parsing IP failed (%s)\n", mac);
    return -1;
  }

  return 0;
}

static int parse_args(int argc, char *argv[], size_t *pqlen_total)
{
  static const char *opts = "d:";
  int c, done = 0;
  unsigned i;
  char *arg;
  double d;

  while (!done) {
    c = getopt(argc, argv, opts);
    switch (c) {
      case 'd':
        if (parse_double(optarg, &d) != 0) {
          fprintf(stderr, "parsing drop probability failed\n");
          return -1;
        }
        rnd_drop_prob = UINT32_MAX * d;
        break;
      case -1:
        done = 1;
        break;
      case '?':
        return -1;
      default:
        abort();
    }
  }

  /* allocate queues */
  queues_num = argc - optind;
  if ((queues = calloc(queues_num, sizeof(*queues))) == NULL) {
    fprintf(stderr, "calloc queues failed\n");
    return -1;
  }

  /* parse args */
  for (i = 0; i < queues_num; i++) {
    arg = argv[optind + i];
    if (parse_queue(arg, &queues[i]) != 0) {
      fprintf(stderr, "Parsing queue (%s) failed\n", arg);
      fprintf(stderr, "expect IP,MAC,LEN,RATE\n");
      return -1;
    }
  }

  return 0;
}

int main(int argc, char *argv[])
{
  int n;
  unsigned threads = num_workers, core, i;
  size_t qlen_total;
  struct rte_mempool *pool;

  assert(num_workers <= MAX_WORKERS);

  if ((n = rte_eal_init(argc, argv)) < 0) {
    return -1;
  }

  if (parse_args(argc - n, argv + n, &qlen_total) < 0) {
    return -1;
  }

  /* allocate pool */
  if ((pool = mempool_alloc(PERTHREAD_MBUFS)) == NULL) {
    fprintf(stderr, "mempool_alloc failed\n");
    return -1;
  }

  /* initialize networking */
  if (network_init(num_workers, num_workers) != 0) {
    fprintf(stderr, "network_init failed\n");
    return -1;
  }

  for (i = 0; i < num_workers; i++){
    network_rx_thread_init(i);
    network_tx_thread_init(i);
  }

  /* start device */
  if (rte_eth_dev_start(port_id) != 0) {
    fprintf(stderr, "rte_eth_dev_start failed\n");
    return -1;
  }

  /* start threads */
  i = 0;
  RTE_LCORE_FOREACH_SLAVE(core) {
    if (i++ < threads) {
      if (rte_eal_remote_launch(worker_thread, NULL, core) != 0) {
        return -1;
      }
    }
  }

  printf("router ready\n");
  fflush(stdout);

  while (1) {
    printf("rx=%"PRIu64" tx=%"PRIu64" tail_drops=%"PRIu64" rnd_drops=%"PRIu64"  ",
        stat_rx, stat_tx, stat_tail_drops, stat_rnd_drops);
    printf("\n");
    fflush(stdout);
    sleep(1);
  }

  return 0;
}
