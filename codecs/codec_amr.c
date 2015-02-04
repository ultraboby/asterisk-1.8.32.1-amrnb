/*
 * Asterisk -- An open source telephony toolkit.
 *
 * The AMR code is from 3GPP TS 26.104.  Copyright information for that package is available
 * in the amr directory.
 *
 * Copyright (C) 2007, 2010 Digital Solutions
 * Paul Bagyenda <bagyenda@dsmagic.com>
 * 
 *
 * See http://www.asterisk.org for more information about
 * the Asterisk project. Please do not directly contact
 * any of the maintainers of this project for assistance;
 * the project provides a web site, mailing lists and IRC
 * channels for your use.
 *
 * This program is free software, distributed under the terms of
 * the GNU General Public License Version 2. See the LICENSE file
 * at the top of the source tree.
 */

/*! \file
 *
 * \brief Translate between signed linear and Adaptive Multi-Rate (AMR) Narrow Band (RFC 3267 format).
 *
 * \ingroup codecs
 */

/*** MODULEINFO
	
 ***/

#include "asterisk.h"

ASTERISK_FILE_VERSION(__FILE__, "$Revision$")

#include <fcntl.h>
#include <stdlib.h>
#include <unistd.h>
#include <netinet/in.h>
#include <string.h>
#include <stdio.h>
#include <assert.h>

#include "asterisk/lock.h"
#include "asterisk/translate.h"
#include "asterisk/config.h"
#include "asterisk/options.h"
#include "asterisk/module.h"
#include "asterisk/logger.h"
#include "asterisk/channel.h"
#include "asterisk/utils.h"

#include "amr/typedef.h"
#include "amr/interf_enc.h"
#include "amr/interf_dec.h"


/* Sample frame data */
#include "amr_slin_ex.h"
#include "asterisk/slin.h"

#define SAMPLES_PER_SEC_NB   8000 /* 8kHz speech gives us 8000 samples per second */
#define BUFFER_SAMPLES	     8000 /* maximum number of samples we will process at a go. */
#define AMR_SAMPLES	     160
#define AMR_MAX_FRAME_LEN    32
#define AMR_MAX_FRAMES_NB (BUFFER_SAMPLES*1000)/(SAMPLES_PER_SEC_NB*20) /* each frame is 20ms, hence max frames = samples/samples_per_sec*/

static int dtx = 0;
static enum Mode enc_mode = MR122; 

/* whether we are parsing/encoding using octet-aligned mode -- XXX not very clean 
 * Note: We don't handle crc or inter-leaving for now
 */
static int octet_aligned = 0;

/* Size of (octet-aligned) speech block for each mode */
/* static short block_size[16]={12, 13, 15, 17, 19, 20, 26, 31, 5}; */

/* Taken from Table 2, of 3GPP TS 26.101, v5.0.0 */
static int num_bits[16] = {95, 103, 118, 134,148,159,204,244};

/* Mapping of encoding mode to AMR codec mode */
static const short modeConv[]={475, 515, 59, 67, 74, 795, 102, 122};

struct amr_translator_pvt {	/* both amr2lin and lin2amr */
	int *destate;  /* decoder state */
	int *enstate;  /* encoder state. */
	enum Mode enc_mode;                /* Currrently requested mode */
	int16_t buf[BUFFER_SAMPLES];	/* lin2amr, temporary storage */
#if 0
	unsigned char pheader[AMR_MAX_FRAMES_NB + 1]; /* lin2amr temporary storage for Pay load header + Table of Contents */
#endif
	unsigned char speech_bits[AMR_MAX_FRAMES_NB*AMR_MAX_FRAME_LEN + 1]; /* storage for packed bits. */
};


/* Pack bits into dst, advance ptr */
static int pack_bits(unsigned char **dst, int d_offset, unsigned char *src,  unsigned sbits)
{
     unsigned char *p = *dst;
     unsigned s_offset, x,y,sbytes = (sbits+7)/8; /* Number of bytes. */
     unsigned char *end_ptr = src + sbytes;
     
     assert(d_offset >= 0 && d_offset < 8);
#if 0     
     ast_verbose("pack_bits: off=%d,sbits=%d\n",d_offset,sbits);
#endif

   /* Fill first dst byte, then we proceed */    
     x = d_offset + 1;  
     /* *p &= (1<<x) - 1; Clear top bits. */
     
     *p = (*p  & (~0 << x)) |  (*src >> (8 - x)); /* Clear bits, then set */
     if (d_offset == 7) 
	  src++;           
     /* Now fill whole dst bytes in each pass */
     s_offset = (d_offset == 7) ? 7 : 7 - x;
     y = s_offset + 1;
     while (src < end_ptr) {
	  p++; /* Go to next; Only do so here, because we need to go to next only if octet is used up. */	  
	  *p = (*src & ((1<<y) - 1)) << (8 - y); 
	  if (s_offset < 7) /* Need part of next byte. Redundant check? I think so */
	       *p |= (src[1] >> y) & ((1<<(8 - s_offset)) - 1);	  
	  src++;
     }
     
     if (*dst == p && (sbits % 8 ) == 0)
	     p++; /* Terrible kludge, but... */

     *dst = p;
     
     /* Compute new d_offset */
     if (sbits > x) {
	  sbits = (sbits - x) % 8; /* We'd have filled in first byte, and X full bytes */
	  
	  /* We now have a remainder set of bits, which are fewer than 8, time to fill them in and calculate */
	  d_offset = 7 - sbits;
     } else {
	  d_offset  -= sbits; /* We stayed in same byte, or just filled it: Subtract # of bits added */
	  if (d_offset < 0)
	       d_offset = 7;
     }
     return d_offset;
}

/* unpack bits from src, advance src */
static int unpack_bits(unsigned char **src, int s_offset, unsigned char *dst, unsigned sbits)
{
     
     unsigned char *q = *src;;

     assert(s_offset >= 0 && s_offset <= 7);
     while (sbits > 0) {	
	  int bits = sbits >= 8 ? 8 : sbits;
	  unsigned mask = ~((1<<(8-bits)) - 1);	  
	  int x = s_offset + 1;

	  *dst = (*q << (8 - x));  /* Set */
	  if (x - bits < 0)  /* Get bit off next byte */
	       *dst |= (q[1] >> x) /*  & ((1 << (8-s_offset)) - 1) */;	  /* right shift of unsigned left pads with zeros*/
	  
	  *dst &= mask; /* Clear all other bits */

	  s_offset -= bits;
	  if (s_offset < 0) { /* This means we got a bit off next byte or all of current byte, so move. */
	       q++;
	       s_offset  += 8;
	  } 
	  dst++;
	  sbits -= bits;
     }

     *src = q;

     return s_offset;
}

static int amr_new(struct ast_trans_pvt *pvt)
{
	struct amr_translator_pvt *tmp = pvt->pvt;
	
	tmp->enstate = Encoder_Interface_init(dtx);
	tmp->destate = Decoder_Interface_init();
	tmp->enc_mode = enc_mode;
	return 0;
}

static struct ast_frame *amrtolin_sample(void)
{
	static struct ast_frame f = {0};
	f.frametype = AST_FRAME_VOICE;
	f.subclass.codec = AST_FORMAT_AMRNB;
	f.datalen = sizeof(amr_slin_ex);
	/* All frames are 20 ms long */
	f.samples = AMR_SAMPLES;
	f.len = 20;
	f.mallocd = 0;
	f.offset = 0;
	f.src = __PRETTY_FUNCTION__;
	f.data.ptr = amr_slin_ex;
	return &f;
}

/*! \brief decode and store in outbuf. */
static int amrtolin_framein(struct ast_trans_pvt *pvt, struct ast_frame *f)
{
	struct amr_translator_pvt *tmp = pvt->pvt;
	int x = 0, more_frames = 1, nframes = 0;
	int16_t *dst = pvt->outbuf.i16;
	unsigned char *src = f->data.ptr, cmr, buffer[AMR_MAX_FRAME_LEN+1];
	struct { 
		unsigned char ft;
		unsigned char q;
	} toc[AMR_MAX_FRAMES_NB];
	
	unsigned char *end_ptr = src + f->datalen;
	int pos; /* position in current byte in the bit stream. */
	
	int xoctet_aligned = octet_aligned;
	
	/* Massive kludge, but we need it to stay alive. Here goes: */
	if (f->data.ptr == amr_slin_ex)
		xoctet_aligned = 1;
	
	pos = unpack_bits(&src, 7, &cmr,  xoctet_aligned ? 8 : 4);
	cmr >>= 4;     /* So we get correct one */

	/* Get the table of contents first... */
	while (src < end_ptr && more_frames) {
		unsigned char ch;
		/* get table of contents. */
		pos = unpack_bits(&src, pos, &ch, xoctet_aligned ? 8 : 6); 
		
		more_frames = (ch>>7);	     
		toc[nframes].ft = (ch >> 3) & 0x0F; /* Kill Q bit */
		toc[nframes].q  = (ch >> 2) & 0x01; 
#if 0
		ast_verbose("amrtolin_framein: cmr=%02hhx, toc.ft=%02hhx,toc.q=%d more=%d, datalen=%d\n",
			    cmr, toc[nframes].ft, toc[nframes].q, more_frames, f->datalen); 
#endif     
		nframes++;
	}
	
	/* Now get the speech bits, and decode as we go. */
	for (x = 0; x<nframes; x++) {
		unsigned char ft = toc[x].ft, q = toc[x].q;
	     int bits = xoctet_aligned ? (num_bits[ft]+7)&~7 : num_bits[ft];
	     
	     if (ft == 14 || ft == 15) /* No data */
		     goto loop; 

	     if (pvt->samples + AMR_SAMPLES > BUFFER_SAMPLES) {	
		  ast_log(LOG_WARNING, "Out of buffer space\n");
		  return -1;
	     }
#if 0
	     memset(buffer, 0, sizeof buffer); /* clear it. */
#endif
	     /* for octet-aligned mode, the speech frames are octet aligned as well */
	     pos = unpack_bits(&src, pos, &buffer[1], bits);
	     buffer[0] = (ft<<3) | (q<<2);
	     Decoder_Interface_Decode(tmp->destate,buffer, dst + pvt->samples,0);
	     
	     pvt->samples += AMR_SAMPLES;
	     pvt->datalen += 2 * AMR_SAMPLES;

	loop:
	     (void)0;
#if 0
	     ast_verbose("amr2lin: %d/%d Decode ft=%u, num_bits=%d\n", x,nframes, ft, bits); 
#endif
	}

	/* Honour the requested codec? */
	if (cmr < tmp->enc_mode)
	     tmp->enc_mode = cmr;
	
	return 0;
}

/*! \brief store samples into working buffer for later decode */
static int lintoamr_framein(struct ast_trans_pvt *pvt, struct ast_frame *f)
{
	struct amr_translator_pvt *tmp = pvt->pvt;

	/* XXX We should look at how old the rest of our stream is, and if it
	   is too old, then we should overwrite it entirely, otherwise we can
	   get artifacts of earlier talk that do not belong */

	/* ast_verbose("lintoamr_framein: %d samples\n", f->samples);*/

	if (pvt->samples + f->samples > BUFFER_SAMPLES) {
		ast_log(LOG_WARNING, "Out of buffer space\n");
		return -1;
	}
	memcpy(tmp->buf + pvt->samples, f->data.ptr, f->datalen);
	pvt->samples += f->samples;
#if 0
	ast_verbose("lintoamr_framein: %d/%d samples\n", f->samples, pvt->samples);
#endif
	return 0;
}

/*! \brief encode and produce a frame */
static struct ast_frame *lintoamr_frameout(struct ast_trans_pvt *pvt)
{
	struct amr_translator_pvt *tmp = pvt->pvt;
	int datalen = 0, samples = 0, npad, h_offset, d_offset;
	int pbits = 0, sbits = 0; /* header and body bit count */
	unsigned char buffer[AMR_MAX_FRAME_LEN+1], cmr = tmp->enc_mode, toc_entry, *phdr, *pdata;
	const unsigned char xzero = 0;

	/* We can't work on anything less than a frame in size */
	if (pvt->samples < AMR_SAMPLES)
		return NULL;

#if 0
	ast_verbose("lintoamr_frameout: %d samples\n", pvt->samples);
#endif

	/* First, put the CMR into the header. */
	cmr <<= 4; /* Put in higher order nibble. */
	phdr = pvt->outbuf.uc;	
	pdata = tmp->speech_bits;
	d_offset = h_offset = 7;
	h_offset = pack_bits(&phdr, h_offset, &cmr, octet_aligned ? 8 : 4);
	pbits += octet_aligned ? 8 : 4;
#if 0
	memset(tmp->speech_bits, 0, sizeof tmp->speech_bits);
	memset(buffer, 0, sizeof buffer);
#endif
	while (pvt->samples >= AMR_SAMPLES) {	     
		unsigned int mode, bits, q;
		/* Encode a frame of data */
		Encoder_Interface_Encode(tmp->enstate, tmp->enc_mode, 
							  tmp->buf + samples, 
							  buffer, 0);

		
		samples += AMR_SAMPLES;
		pvt->samples -= AMR_SAMPLES;
		
		mode = (buffer[0]>>3)&0x0F; 
		q = (buffer[0]>>2)&0x01;
		
		toc_entry = (mode<<3) | (q<<2);

		bits = octet_aligned ? (num_bits[mode]+7)&~7 : num_bits[mode];
		
		/* Set the F bit */
		if (pvt->samples >= AMR_SAMPLES) /* then we have another frame to  pack, so... */
			toc_entry |= (1<<7);
		h_offset = pack_bits(&phdr, h_offset, 
				     &toc_entry, octet_aligned ? 8 : 6); /* put in the table of contents element. */
		pbits += octet_aligned ? 8 : 6;
		

		/* Pack the bits of the speech. */
		d_offset = pack_bits(&pdata, d_offset, &buffer[1], bits);
		sbits += bits;	
#if 0
		ast_verbose("lin2amr[1]: mode=%d,q=%d,enc_mode=%d,byte_count=%d,bits=%d,more=%d\n",
			    mode, q, tmp->enc_mode,byte_count,bits, 
			    toc_entry & (1<<7) ? 1 : 0); 	
#endif
	}
	
        /* CMR+TOC  is already in outbuf. So: Add speech bits */
	
	h_offset = pack_bits(&phdr, h_offset, tmp->speech_bits, sbits);
	npad = (8 - ((sbits + pbits) & 7))&0x7; /* Number of padding bits */

	if (octet_aligned && npad != 0)
		ast_log(LOG_ERROR,"Padding bits cannot be > 0 in octet aligned mode!\n");
	
	pack_bits(&phdr, h_offset, (void *)&xzero, npad); /* zero out the rest of the padding bits. */
	datalen = (sbits + pbits + npad + 7)/8; /* Round up to nearest octet. */
	
#if 0
	ast_verbose("lin2amr: toc_bit_count=%d,body_bit_count=%d, npad=%d,p[0]=0X%02hhX,p[1]=0X%02hhX,data_len=%d\n", 
		    pbits, sbits, npad, (unsigned)pvt->outbuf.uc[0], (unsigned)pvt->outbuf.uc[1], datalen); 
#endif
	/* Move the data at the end of the buffer to the front */
	if (pvt->samples)
		memmove(tmp->buf, tmp->buf + samples, pvt->samples * 2);
	
	return ast_trans_frameout(pvt, datalen, samples);
}

static void amr_destroy_stuff(struct ast_trans_pvt *pvt)
{
	struct amr_translator_pvt *tmp = pvt->pvt;
	Encoder_Interface_exit(tmp->enstate);
	Decoder_Interface_exit(tmp->destate);
}

static struct ast_translator amrtolin = {
	.name = "amrtolin", 
	.srcfmt = AST_FORMAT_AMRNB,
	.dstfmt = AST_FORMAT_SLINEAR,
	.newpvt = amr_new,
	.framein = amrtolin_framein,
	.destroy = amr_destroy_stuff,
	.sample = amrtolin_sample,
	.buffer_samples = BUFFER_SAMPLES,
	.buf_size = BUFFER_SAMPLES * 2,
	.desc_size = sizeof (struct amr_translator_pvt )
};

static struct ast_translator lintoamr = {
	.name = "lintoamr", 
	.srcfmt = AST_FORMAT_SLINEAR,
	.dstfmt = AST_FORMAT_AMRNB,
	.newpvt = amr_new,
	.framein = lintoamr_framein,
	.frameout = lintoamr_frameout,
	.destroy = amr_destroy_stuff,
	.sample = slin16_sample,
	.desc_size = sizeof (struct amr_translator_pvt ),
	.buf_size = (BUFFER_SAMPLES * AMR_MAX_FRAME_LEN + AMR_SAMPLES - 1)/AMR_SAMPLES,
};


static int parse_config(int reload)
{    
	struct ast_variable *var;
	struct ast_flags config_flags = { reload ? CONFIG_FLAG_FILEUNCHANGED : 0 };
	struct ast_config *cfg = ast_config_load("codecs.conf", config_flags);

	if (cfg == CONFIG_STATUS_FILEMISSING || cfg == CONFIG_STATUS_FILEUNCHANGED || cfg == CONFIG_STATUS_FILEINVALID)
		return 0;
	for (var = ast_variable_browse(cfg, "amr"); var; var = var->next) {
	     if (!strcasecmp(var->name, "octet-aligned")) {
		  octet_aligned = atoi(var->value);
		  if (option_verbose > 2)
			  ast_verbose(VERBOSE_PREFIX_3 "codec_amr: octet-align mode set to %d\n", octet_aligned);
	     } else if (!strcasecmp(var->name, "dtx")) {
		  dtx = atoi(var->value);
		  if (option_verbose > 2)
		       ast_verbose(VERBOSE_PREFIX_3 "codec_amr: set dtx mode to %d\n", dtx);
	     } else if (!strcasecmp(var->name, "mode")) {
		  int mode_tmp = strtol(var->value + 2, NULL, 10);
		  int req_mode;
		  for (req_mode = 0; req_mode < 8; req_mode++)
		       if (mode_tmp == modeConv[req_mode])
			    break;
		  if (req_mode == 8) {
		       ast_log(LOG_ERROR, "Error, unknown mode %s. Must be one of MR475, MR515, MR59, MR67, MR74, MR795, MR102, MR122\n",
			       var->value);
		  } else {
		       enc_mode = req_mode;
		       if (option_verbose > 2)
			    ast_verbose(VERBOSE_PREFIX_3 "codec_amr: AMR mode set to MR%d\n", mode_tmp);
		  }
	       }
	}
	ast_config_destroy(cfg);
	ast_verbose("codec_amr: enc_mode = %d, dtx = %d\n", enc_mode, dtx);

	return 0;
}

/*! \brief standard module glue */
static int reload(void)
{
	if (parse_config(1))
		return AST_MODULE_LOAD_DECLINE;
	return AST_MODULE_LOAD_SUCCESS;
}

static int unload_module(void)
{
	int res;

	res = ast_unregister_translator(&lintoamr);
	if (!res)
		res = ast_unregister_translator(&amrtolin);

	return res;
}

static int load_module(void)
{
	int res;

	if (parse_config(0))
		return AST_MODULE_LOAD_DECLINE;

	res = ast_register_translator(&amrtolin);
	if (!res) 
		res=ast_register_translator(&lintoamr);
	else
		ast_unregister_translator(&amrtolin);

	if (res)
		return AST_MODULE_LOAD_FAILURE;
	return AST_MODULE_LOAD_SUCCESS;
}

AST_MODULE_INFO(ASTERISK_GPL_KEY, AST_MODFLAG_DEFAULT, "AMR Coder/Decoder",
		.load = load_module,
		.unload = unload_module,
		.reload = reload,
	       );
