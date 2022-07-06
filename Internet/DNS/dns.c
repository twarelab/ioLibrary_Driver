//*****************************************************************************
//
//! \file dns.c
//! \brief DNS APIs Implement file.
//! \details Send DNS query & Receive DNS reponse.  \n
//!          It depends on stdlib.h & string.h in ansi-c library
//! \version 1.1.0
//! \date 2013/11/18
//! \par  Revision history
//!       <2013/10/21> 1st Release
//!       <2013/12/20> V1.1.0
//!         1. Remove secondary DNS server in DNS_run
//!            If 1st DNS_run failed, call DNS_run with 2nd DNS again
//!         2. DNS_timerHandler -> DNS_time_handler
//!         3. Remove the unused define
//!         4. Integrated dns.h dns.c & dns_parse.h dns_parse.c into dns.h & dns.c
//!       <2013/12/20> V1.1.0
//!
//! \author Eric Jung & MidnightCow
//! \copyright
//!
//! Copyright (c)  2013, WIZnet Co., LTD.
//! All rights reserved.
//!
//! Redistribution and use in source and binary forms, with or without
//! modification, are permitted provided that the following conditions
//! are met:
//!
//!     * Redistributions of source code must retain the above copyright
//! notice, this list of conditions and the following disclaimer.
//!     * Redistributions in binary form must reproduce the above copyright
//! notice, this list of conditions and the following disclaimer in the
//! documentation and/or other materials provided with the distribution.
//!     * Neither the name of the <ORGANIZATION> nor the names of its
//! contributors may be used to endorse or promote products derived
//! from this software without specific prior written permission.
//!
//! THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
//! AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
//! IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
//! ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE
//! LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
//! CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
//! SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
//! INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
//! CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
//! ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF
//! THE POSSIBILITY OF SUCH DAMAGE.
//
//*****************************************************************************

#include <string.h>
#include <stdlib.h>

#include "socket.h"
#include "dns.h"

#ifdef _DNS_DEBUG_
   #include <stdio.h>
#endif

#define	INITRTT		2000L	/* Initial smoothed response time */
#define	MAXCNAME	   (MAX_DOMAIN_NAME + (MAX_DOMAIN_NAME>>1))	   /* Maximum amount of cname recursion */

#define	TYPE_A		1	   /* Host address */
#define	TYPE_NS		2	   /* Name server */
#define	TYPE_MD		3	   /* Mail destination (obsolete) */
#define	TYPE_MF		4	   /* Mail forwarder (obsolete) */
#define	TYPE_CNAME	5	   /* Canonical name */
#define	TYPE_SOA	   6	   /* Start of Authority */
#define	TYPE_MB		7	   /* Mailbox name (experimental) */
#define	TYPE_MG		8	   /* Mail group member (experimental) */
#define	TYPE_MR		9	   /* Mail rename name (experimental) */
#define	TYPE_NULL	10	   /* Null (experimental) */
#define	TYPE_WKS	   11	   /* Well-known sockets */
#define	TYPE_PTR	   12	   /* Pointer record */
#define	TYPE_HINFO	13	   /* Host information */
#define	TYPE_MINFO	14	   /* Mailbox information (experimental)*/
#define	TYPE_MX		15	   /* Mail exchanger */
#define	TYPE_TXT	   16	   /* Text strings */
#define	TYPE_ANY	   255	/* Matches any type */

#define	CLASS_IN	   1	   /* The ARPA Internet */

/* Round trip timing parameters */
#define	AGAIN	      8     /* Average RTT gain = 1/8 */
#define	LAGAIN      3     /* Log2(AGAIN) */
#define	DGAIN       4     /* Mean deviation gain = 1/4 */
#define	LDGAIN      2     /* log2(DGAIN) */

/* Header for all domain messages */
struct dhdr
{
	uint16_t id;   /* Identification */
	uint8_t	qr;      /* Query/Response */
#define	QUERY    0
#define	RESPONSE 1
	uint8_t	opcode;
#define	IQUERY   1
	uint8_t	aa;      /* Authoratative answer */
	uint8_t	tc;      /* Truncation */
	uint8_t	rd;      /* Recursion desired */
	uint8_t	ra;      /* Recursion available */
	uint8_t	rcode;   /* Response code */
#define	NO_ERROR       0
#define	FORMAT_ERROR   1
#define	SERVER_FAIL    2
#define	NAME_ERROR     3
#define	NOT_IMPL       4
#define	REFUSED        5
	uint16_t qdcount;	/* Question count */
	uint16_t ancount;	/* Answer count */
	uint16_t nscount;	/* Authority (name server) count */
	uint16_t arcount;	/* Additional record count */
};


uint8_t* pDNSMSG;       // DNS message buffer
uint8_t  DNS_SOCKET;    // SOCKET number for DNS
uint16_t DNS_MSGID;     // DNS message ID

uint32_t dns_1s_tick;   // for timout of DNS processing
static uint8_t retry_count;

typedef enum {
	DNS_STATE_IDLE 			= 0,
	DNS_STATE_SOCK_CREATE	= 1,
	DNS_STATE_SEND_REQUEST	= 2,
	DNS_STATE_REPLY_RCVD	= 3,
	DNS_STATE_FAILED 		= 4,
	DNS_STATE_FINISHED		= 5
};

static uint8_t dnsState = DNS_STATE_IDLE;



/* converts uint16_t from network buffer to a host byte order integer. */
uint16_t get16(uint8_t * s)
{
	uint16_t i;
	i = *s++ << 8;
	i = i + *s;
	return i;
}

/* copies uint16_t to the network buffer with network byte order. */
uint8_t * put16(uint8_t * s, uint16_t i)
{
	*s++ = i >> 8;
	*s++ = i;
	return s;
}


/*
 *              CONVERT A DOMAIN NAME TO THE HUMAN-READABLE FORM
 *
 * Description : This function converts a compressed domain name to the human-readable form
 * Arguments   : msg        - is a pointer to the reply message
 *               compressed - is a pointer to the domain name in reply message.
 *               buf        - is a pointer to the buffer for the human-readable form name.
 *               len        - is the MAX. size of buffer.
 * Returns     : the length of compressed message
 */
int parse_name(uint8_t * msg, uint8_t * compressed, char * buf, int16_t len)
{
	uint16_t slen;		/* Length of current segment */
	uint8_t * cp;
	int clen = 0;		/* Total length of compressed name */
	int indirect = 0;	/* Set if indirection encountered */
	int nseg = 0;		/* Total number of segments in name */

	cp = compressed;

	for (;;)
	{
		slen = *cp++;	/* Length of this segment */

		if (!indirect) clen++;

		if ((slen & 0xc0) == 0xc0)
		{
			if (!indirect)
				clen++;
			indirect = 1;
			/* Follow indirection */
			cp = &msg[((slen & 0x3f)<<8) + *cp];
			slen = *cp++;
		}

		if (slen == 0)	/* zero length == all done */
			break;

		len -= slen + 1;

		if (len < 0) return -1;

		if (!indirect) clen += slen;

		while (slen-- != 0) *buf++ = (char)*cp++;
		*buf++ = '.';
		nseg++;
	}

	if (nseg == 0)
	{
		/* Root name; represent as single dot */
		*buf++ = '.';
		len--;
	}

	*buf++ = '\0';
	len--;

	return clen;	/* Length of compressed message */
}

/*
 *              PARSE QUESTION SECTION
 *
 * Description : This function parses the qeustion record of the reply message.
 * Arguments   : msg - is a pointer to the reply message
 *               cp  - is a pointer to the qeustion record.
 * Returns     : a pointer the to next record.
 */
uint8_t * dns_question(uint8_t * msg, uint8_t * cp)
{
	int len;
	char name[MAXCNAME];

	len = parse_name(msg, cp, name, MAXCNAME);
#ifdef _DNS_DEBUG_
	printf("dns_question, name: %s\r\n", name);
#endif
	if (len == -1) return 0;

	cp += len;
	cp += 2;		/* type */
	cp += 2;		/* class */

	return cp;
}


/*
 *              PARSE ANSER SECTION
 *
 * Description : This function parses the answer record of the reply message.
 * Arguments   : msg - is a pointer to the reply message
 *               cp  - is a pointer to the answer record.
 * Returns     : a pointer the to next record.
 */
uint8_t * dns_answer(uint8_t * msg, uint8_t * cp, uint8_t * ip_from_dns)
{
	int len, type;
	char name[MAXCNAME];

	len = parse_name(msg, cp, name, MAXCNAME);
#ifdef _DNS_DEUBG_
	printf("dns_answer, name: %s\r\n", name);
#endif
	if (len == -1) return 0;

	cp += len;
	type = get16(cp);
	cp += 2;		/* type */
	cp += 2;		/* class */
	cp += 4;		/* ttl */
	cp += 2;		/* len */


	switch (type)
	{
	case TYPE_A:
#ifdef _DNS_DEBUG_
		printf("Type A\r\n");
#endif
		/* Just read the address directly into the structure */
		ip_from_dns[0] = *cp++;
		ip_from_dns[1] = *cp++;
		ip_from_dns[2] = *cp++;
		ip_from_dns[3] = *cp++;
		break;
	case TYPE_CNAME:
	case TYPE_MB:
	case TYPE_MG:
	case TYPE_MR:
	case TYPE_NS:
	case TYPE_PTR:
#ifdef _DNS_DEBUG_
		printf("Type %d\r\n", type);
#endif
		/* These types all consist of a single domain name */
		/* convert it to ascii format */
		len = parse_name(msg, cp, name, MAXCNAME);
		if (len == -1) return 0;

		cp += len;
		break;
	case TYPE_HINFO:
#ifdef _DNS_DEUBG_
		printf("TYPE_HINFO\r\n");
#endif
		len = *cp++;
		cp += len;

		len = *cp++;
		cp += len;
		break;
	case TYPE_MX:
#ifdef _DNS_DEBUG_
		printf("TYPE_MX\r\n");
#endif
		cp += 2;
		/* Get domain name of exchanger */
		len = parse_name(msg, cp, name, MAXCNAME);
		if (len == -1) return 0;

		cp += len;
		break;
	case TYPE_SOA:
#ifdef _DNS_DEBUG_
		printf("TYPE_SOA\r\n");
#endif
		/* Get domain name of name server */
		len = parse_name(msg, cp, name, MAXCNAME);
		if (len == -1) return 0;

		cp += len;

		/* Get domain name of responsible person */
		len = parse_name(msg, cp, name, MAXCNAME);
		if (len == -1) return 0;

		cp += len;

		cp += 4;
		cp += 4;
		cp += 4;
		cp += 4;
		cp += 4;
		break;
	case TYPE_TXT:
#ifdef _DNS_DEBUG_
		printf("TYPE_TXT\r\n");
#endif
		/* Just stash */
		break;
	default:
		/* Ignore */
		break;
	}

	return cp;
}

/*
 *              PARSE THE DNS REPLY
 *
 * Description : This function parses the reply message from DNS server.
 * Arguments   : dhdr - is a pointer to the header for DNS message
 *               buf  - is a pointer to the reply message.
 *               len  - is the size of reply message.
 * Returns     : -1 - Domain name lenght is too big
 *                0 - Fail (Timout or parse error)
 *                1 - Success,
 */
int8_t parseDNSMSG(struct dhdr * pdhdr, uint8_t * pbuf, uint8_t * ip_from_dns)
{
	uint16_t tmp;
	uint16_t i;
	uint8_t * msg;
	uint8_t * cp;

	msg = pbuf;
	memset(pdhdr, 0, sizeof(*pdhdr));

	pdhdr->id = get16(&msg[0]);
#ifdef _DNS_DEBUG_
	printf("ID: %d\r\n", pdhdr->id);
#endif
	tmp = get16(&msg[2]);
	if (tmp & 0x8000) pdhdr->qr = 1;
#ifdef _DNS_DEBUG_
	printf("QR: %d\r\n", pdhdr->qr);
#endif

	pdhdr->opcode = (tmp >> 11) & 0xf;
#ifdef _DNS_DEBUG_
	printf("OPCODE: %d\r\n", pdhdr->opcode);
#endif

	if (tmp & 0x0400) pdhdr->aa = 1;
	if (tmp & 0x0200) pdhdr->tc = 1;
	if (tmp & 0x0100) pdhdr->rd = 1;
	if (tmp & 0x0080) pdhdr->ra = 1;
#ifdef _DNS_DEBUG_
	printf("pdhdr->aa: %d\r\n", pdhdr->aa);
	printf("pdhdr->tc: %d\r\n", pdhdr->tc);
	printf("pdhdr->rd: %d\r\n", pdhdr->rd);
	printf("pdhdr->ra: %d\r\n", pdhdr->ra);
#endif
	pdhdr->rcode = tmp & 0xf;
	pdhdr->qdcount = get16(&msg[4]);
	pdhdr->ancount = get16(&msg[6]);
	pdhdr->nscount = get16(&msg[8]);
	pdhdr->arcount = get16(&msg[10]);
#ifdef _DNS_DEBUG_
	printf("pdhdr->rcode: %d\r\n", pdhdr->rcode);
	printf("pdhdr->qdcount: %d\r\n", pdhdr->qdcount);
	printf("pdhdr->ancount: %d\r\n", pdhdr->ancount);
	printf("pdhdr->nscount: %d\r\n", pdhdr->nscount);
	printf("pdhdr->arcount: %d\r\n", pdhdr->arcount);
#endif

	/* Now parse the variable length sections */
	cp = &msg[12];

	/* Question section */
	for (i = 0; i < pdhdr->qdcount; i++)
	{
		cp = dns_question(msg, cp);
   #ifdef _DNS_DEBUG_
      printf("MAX_DOMAIN_NAME is too small, it should be redfine in dns.h");
   #endif
		if(!cp) return -1;
	}

	/* Answer section */
	for (i = 0; i < pdhdr->ancount; i++)
	{
		cp = dns_answer(msg, cp, ip_from_dns);
   #ifdef _DNS_DEBUG_
      printf("MAX_DOMAIN_NAME is too small, it should be redfine in dns.h");
   #endif
		if(!cp) return -1;
	}

	/* Name server (authority) section */
	for (i = 0; i < pdhdr->nscount; i++)
	{
		;
	}

	/* Additional section */
	for (i = 0; i < pdhdr->arcount; i++)
	{
		;
	}

	if(pdhdr->rcode == 0) return 1;		// No error
	else return 0;
}


/*
 *              MAKE DNS QUERY MESSAGE
 *
 * Description : This function makes DNS query message.
 * Arguments   : op   - Recursion desired
 *               name - is a pointer to the domain name.
 *               buf  - is a pointer to the buffer for DNS message.
 *               len  - is the MAX. size of buffer.
 * Returns     : the pointer to the DNS message.
 */
int16_t dns_makequery(uint16_t op, char * name, uint8_t * buf, uint16_t len)
{
	uint8_t *cp;
	char *cp1;
	char sname[MAXCNAME];
	char *dname;
	uint16_t p;
	uint16_t dlen;

	cp = buf;

	DNS_MSGID++;
	cp = put16(cp, DNS_MSGID);
	p = (op << 11) | 0x0100;			/* Recursion desired */
	cp = put16(cp, p);
	cp = put16(cp, 1);
	cp = put16(cp, 0);
	cp = put16(cp, 0);
	cp = put16(cp, 0);

	strcpy(sname, name);
	dname = sname;
	dlen = strlen(dname);
	for (;;)
	{
		/* Look for next dot */
		cp1 = strchr(dname, '.');

		if (cp1 != NULL) len = cp1 - dname;	/* More to come */
		else len = dlen;			/* Last component */

		*cp++ = len;				/* Write length of component */
		if (len == 0) break;

		/* Copy component up to (but not including) dot */
		strncpy((char *)cp, dname, len);
		cp += len;
		if (cp1 == NULL)
		{
			*cp++ = 0;			/* Last one; write null and finish */
			break;
		}
		dname += len+1;
		dlen -= len+1;
	}

	cp = put16(cp, 0x0001);				/* type */
	cp = put16(cp, 0x0001);				/* class */

	return ((int16_t)((uint32_t)(cp) - (uint32_t)(buf)));
}

/*
 *              CHECK DNS TIMEOUT
 *
 * Description : This function check the DNS timeout
 * Arguments   : None.
 * Returns     : -1 - timeout occurred, 0 - timer over, but no timeout, 1 - no timer over, no timeout occur
 * Note        : timeout : retry count and timer both over.
 */

int8_t check_DNS_timeout(void)
{

	if(dns_1s_tick >= DNS_WAIT_TIME)
	{
//		printf("dns_1s_tick: %d in check_DNS_timeout\r\n", dns_1s_tick);
		dns_1s_tick = 0;
		if(retry_count >= MAX_DNS_RETRY) {
			retry_count = 0;
			return -1; // timeout occurred
		}
		retry_count++;
		return 0; // timer over, but no timeout
	}

	return 1; // no timer over, no timeout occur
}



/* DNS CLIENT INIT */
void DNS_init(uint8_t s, uint8_t * buf)
{
	DNS_SOCKET = s; // SOCK_DNS
	pDNSMSG = buf; // User's shared buffer
	DNS_MSGID = DNS_MSG_ID;
	dnsState = DNS_STATE_IDLE;
#ifdef _DNS_DEBUG_
    printf("> DNS_init. dnsState will be changed to DNS_STATE_IDLE\r\n");
#endif
}

/* DNS CLIENT RUN */

int8_t DNS_run(uint8_t * dns_ip, uint8_t * name, uint8_t * ip_from_dns)
{
	int8_t ret;
	struct dhdr dhp;
	uint8_t ip[4];
	static uint16_t len;
	uint16_t port;
	int8_t ret_check_timeout;
	int i;

	ret = -2;

	switch(dnsState)
	{
	case DNS_STATE_IDLE:
		retry_count = 0;
		dns_1s_tick = 0;
		// socket create
		socket(DNS_SOCKET, Sn_MR_UDP, 0, SF_IO_NONBLOCK);
		len = dns_makequery(0, (char *)name, pDNSMSG, MAX_DNS_BUF_SIZE);
//		printf("dns_makequery len: %d\r\n", len);
		dnsState = DNS_STATE_SOCK_CREATE;
		#ifdef _DNS_DEBUG_
			printf("> dnsState will be changed to DNS_STATE_SOCK_CREATE in DNS_run\r\n");
		#endif
		break;
	case DNS_STATE_SOCK_CREATE:
		sendto(DNS_SOCKET, pDNSMSG, len, dns_ip, IPPORT_DOMAIN);
		#ifdef _DNS_DEBUG_
			printf("> DNS Query was sent to %d.%d.%d.%d\r\n", dns_ip[0], dns_ip[1], dns_ip[2], dns_ip[3]);
		#endif
		dnsState = DNS_STATE_SEND_REQUEST;
		#ifdef _DNS_DEBUG_
			printf("> dnsState will be changed to DNS_STATE_SEND_REQUEST in DNS_run\r\n");
		#endif
		break;
	case DNS_STATE_SEND_REQUEST:
		if ((len = getSn_RX_RSR(DNS_SOCKET)) > 0)
		{
			if (len > MAX_DNS_BUF_SIZE) len = MAX_DNS_BUF_SIZE;
			len = recvfrom(DNS_SOCKET, pDNSMSG, len, ip, &port);
		  #ifdef _DNS_DEBUG_
			  printf("> Receive DNS message from %d.%d.%d.%d(%d). len = %d\r\n", ip[0], ip[1], ip[2], ip[3],port,len);
		  #endif
         ret = parseDNSMSG(&dhp, pDNSMSG, ip_from_dns);
//         printf("parseDNSMSG ret: %d\r\n", ret);
		}

		//Timeout Check
		ret_check_timeout = check_DNS_timeout();
		if (ret_check_timeout < 0)
		{

			#ifdef _DNS_DEBUG_
				printf("> DNS Server is not responding : %d.%d.%d.%d\r\n", dns_ip[0], dns_ip[1], dns_ip[2], dns_ip[3]);
			#endif
			dnsState = DNS_STATE_FAILED;

			#ifdef _DNS_DEBUG_
				printf("> dnsState will be changed to DNS_STATE_FAILED in DNS_run\r\n");
			#endif
		}
		else if (ret_check_timeout == 0)
		{

			#ifdef _DNS_DEBUG_
				printf("> DNS Timeout. dns_1s_tick: %d\r\n", dns_1s_tick);
			#endif
			dnsState = DNS_STATE_SOCK_CREATE;

			#ifdef _DNS_DEBUG_
				printf("> dnsState will be changed to DNS_STATE_SOCK_CREATE in DNS_run\r\n");
			#endif
		}
		break;
	case DNS_STATE_REPLY_RCVD:
		close(DNS_SOCKET);
		dnsState = DNS_STATE_FINISHED;
		#ifdef _DNS_DEBUG_
			printf("> dnsState will be changed to DNS_STATE_FINISED in DNS_run\r\n");
		#endif
		break;
	case DNS_STATE_FAILED:
		close(DNS_SOCKET); //test by james
		dnsState = DNS_STATE_IDLE;
		break;
	default:
		break;
	}

	return ret;
}

//int8_t DNS_run(uint8_t * dns_ip, uint8_t * name, uint8_t * ip_from_dns)
//{
//	int8_t ret;
//	struct dhdr dhp;
//	uint8_t ip[4];
//	uint16_t len, port;
//	int8_t ret_check_timeout;
//	int i;
//
//	retry_count = 0;
//	dns_1s_tick = 0;
//
//   // Socket open
//   socket(DNS_SOCKET, Sn_MR_UDP, 0, 0x01);
//
//#ifdef _DNS_DEBUG_
//	printf("> DNS Query to DNS Server : %d.%d.%d.%d\r\n", dns_ip[0], dns_ip[1], dns_ip[2], dns_ip[3]);
//#endif
//
//	len = dns_makequery(0, (char *)name, pDNSMSG, MAX_DNS_BUF_SIZE);
//	sendto(DNS_SOCKET, pDNSMSG, len, dns_ip, IPPORT_DOMAIN);
//#ifdef _DNS_DEBUG_
//	printf("> DNS Query was sent to %d.%d.%d.%d\r\n", dns_ip[0], dns_ip[1], dns_ip[2], dns_ip[3]);
//#endif
//
//	while (1)
//	{
//		if ((len = getSn_RX_RSR(DNS_SOCKET)) > 0)
//		{
//			if (len > MAX_DNS_BUF_SIZE) len = MAX_DNS_BUF_SIZE;
//			len = recvfrom(DNS_SOCKET, pDNSMSG, len, ip, &port);
//      #ifdef _DNS_DEBUG_
//	      printf("> Receive DNS message from %d.%d.%d.%d(%d). len = %d\r\n", ip[0], ip[1], ip[2], ip[3],port,len);
////	      printf("Received DNS message:\r\n");
////	      for(i=0; i<len; i++)
////	    	  printf("%02X ", pDNSMSG[i]);
////	      printf("\r\n");
//      #endif
//         ret = parseDNSMSG(&dhp, pDNSMSG, ip_from_dns);
//         printf("parseDNSMSG ret: %d\r\n", ret);
//			break;
//		}
//		// Check Timeout
//		ret_check_timeout = check_DNS_timeout();
//		if (ret_check_timeout < 0) {
//
//#ifdef _DNS_DEBUG_
//			printf("> DNS Server is not responding : %d.%d.%d.%d\r\n", dns_ip[0], dns_ip[1], dns_ip[2], dns_ip[3]);
//#endif
//			close(DNS_SOCKET); //test by james
//			return 0; // timeout occurred
//		}
//		else if (ret_check_timeout == 0) {
//
//#ifdef _DNS_DEBUG_
//			printf("> DNS Timeout\r\n");
//#endif
//			sendto(DNS_SOCKET, pDNSMSG, len, dns_ip, IPPORT_DOMAIN);
//		}
//	}
//	close(DNS_SOCKET);
//	// Return value
//	// 0 > :  failed / 1 - success
//	return ret;
//}


/* DNS TIMER HANDLER */
void DNS_time_handler(void)
{
	dns_1s_tick++;
}
