
// glob :: Vamp : language support
// --------------------------------------------------------------------------------------------------------
   Define('Vamp')
   ({
   // func :: init
   // -----------------------------------------------------------------------------------------------------
      Init:function()
      {
         Path.Read.mimeCast.Join(Vamp.decode.extn);

         // this.opkv = {}.Join(this.expr).Join(this.mopr).Join(this.dlim).Join(this.quot).Join(this.omit);
         // this.opkn = Keys(this.opkv);
         // this.opql = Keys(this.quot);
         // this.opil = Keys(this.omit);
      },
   // -----------------------------------------------------------------------------------------------------





   // func :: minify : remove comments & extra white-space
   // -----------------------------------------------------------------------------------------------------
      minify:function(vt)
      {
      // dbug & vars
      // --------------------------------------------------------------------------------------------------
         if (!isText(vt))
         { throw 'expecting typeOf: TEXT'; }

         var md,ol,ql,ob,qb,qp,qr,vs,zi,rt,mo;

         md = '!# minified\n';   // mini done
         ol = Vamp.decode.omit;  // omit list
         ql = Vamp.decode.quot;  // quot list
         ob = Keys(ol);          // omit begn
         qb = Keys(ql);          // quot begn
         qp = '‷‴';              // quot pair (triple prime)
         qr = '';                // quot CRLF
         vt = vt.trim();         // vamp text
         rt = '';                // resl text

         if
         (
            (vt.length < 1) || (vt.substr(0,md.length) == md) ||
            (!vt.Has(',',':','(') && !vt.Has(ob) && !vt.Has(qb) && !vt.Has('\n'))
         )
         { return vt.split(md).join(''); } // nothing to do

         vt = ('\n'+(vt.split('\r\n').join('\n'))+'\n'); // fix new-lines for comments & line-numbers
         vs = vt.length;
         zi = (vs -1);

         mo = Vamp.decode.swap;

         var ci,c1,c2,c3,cl;     // char-pairs & char-list
         var ox,qx      ;        // omit-contxt & quot-contxt
         var os,qs,qt,pc,nc,tv,bt,dc,co;

         bt = '';
         dc = this.decode;
         co = Keys({}.Join(dc.expr).Join(dc.dlim).Join(dc.mopr)).Join(Vals(dc.mopr[':']));
      // --------------------------------------------------------------------------------------------------




      // each :: char : walk through each char to avoid quot-&-omit issues -- jump ahead on omit -or- quot
      // --------------------------------------------------------------------------------------------------
         for (ci=0; ci<vs; ci++)
         {
         // char pairs
         // -----------------------------------------------------------------------------------------------
            c1 = vt[ci];                              // 1 char
            c2 = (((ci+1) < vs) ? c1+vt[ci+1] : '');  // 2 chars
            c3 = (((ci+2) < vs) ? c2+vt[ci+2] : '');  // 3 chars
            cl = [c3,c2,c1];                          // char list
         // -----------------------------------------------------------------------------------------------



         // omit :: comment
         // -----------------------------------------------------------------------------------------------
            ox = cl.Find(ob);

            if (ox)
            {
               ox = ol[ox[1]];
               ox = vt.Find(ox, ci+2);
               os = ox[1].length;
               ci = (ox[0]+ci+os+1);

               continue;
            }
         // -----------------------------------------------------------------------------------------------



         // quot :: strings
         // -----------------------------------------------------------------------------------------------
            qx = cl.Find(qb);

            if (qx)
            {
               qs = ql[qx[1]];
               tv = ('⋖'+(qs.length<2 ? '□' : '□□')+'⋗');
               vt = vt.split('\\'+qs+'\\').join(tv);
               qx = vt.Find(qs,ci+1); qx[0]+=ci;
               vt = vt.split(tv).join('\\'+qs+'\\');
               qs = qx[1].length;
               qt = vt.substr(ci+qs, ((qx[0]+1) - (ci+qs)));
               ci = (qx[0] + qs);

               if ((qx[1] == '|]') && qt.Has('\n'))
               {
                  qs = qt.split('\n');
                  tv = (qs.length -1);
                  qt = [];

                  qs.Each = function(lt,li)
                  {
                     lt = lt.trim();

                     if ((lt.length < 1) && ((li < 1) || (li == tv)))
                     { return NEXT; }

                     qt.Insert(lt);
                  };

                  qt = qt.join('↵');
               }

               rt+= (qp[0] + qt + qp[1]);

               continue;
            }
         // -----------------------------------------------------------------------------------------------



         // resl :: apnd : non-quoted
         // -----------------------------------------------------------------------------------------------
            pc = ((ci < 1) ? '' : vt[ci -1]);
            nc = ((ci < zi) ? vt[ci +1] : '');

            if
            (
               ((pc+c1) == '  ') || (c2 == '  ') ||
               ([' ','\n'].Has(c1) && ((ci < 1) || (ci == zi) || co.Has(pc) || co.Has(nc)))
            )
            { continue; }

            if (co.Has(c1))
            { bt = ((c1 != '.') ? '' : bt); }
            else
            { bt+= c1; }

            // if (mo[c2] || (mo[c1] && ((c1 != '.') || isNaN(bt) || isNaN(nc))))
            if (mo[c2] || (mo[c1] && ((c1 != '.') || isNaN(bt) || isNaN(nc)) && ((c1 != '-') || isNaN(nc))))
            {
               c1 = (mo[c2] ? mo[c2] : mo[c1]);
            }

            rt+= c1;
         // -----------------------------------------------------------------------------------------------
         }
      // --------------------------------------------------------------------------------------------------




      // done
      // --------------------------------------------------------------------------------------------------
         return rt.trim();
      // --------------------------------------------------------------------------------------------------
      },
   // -----------------------------------------------------------------------------------------------------





   // func :: reckon : calculate expressions
   // -----------------------------------------------------------------------------------------------------
      reckon:function(xl)
      {
         var vr,ol,rd,fn,op,lt,rt;

         vr = this;
         ol = Vals(Vamp.decode.swap).Select(range(9,23));
         rd = xl.shift();

         if (xl.length < 2)
         { return rd; }

         xl.Each = function(iv)
         {
            if (ol.Has(iv))
            { op = iv; return; }

            if (!op){ return; }

            if ((rd == VOID) && (iv == VOID))
            { rd = VOID; return; }

            if ((rd == null) && (iv == null))
            { rd = null; return; }

            lt = typeOf(rd).substr(1,2);
            lt = (['MA','PL'].Has(lt) ? 'VO' : lt);

            rt = typeOf(iv).substr(1,2);
            rt = (['MA','PL'].Has(rt) ? 'VO' : rt);

            tp = (lt+'|'+rt);
            tp = (vr[tp] ? tp : (vr[(lt+'|*')] ? (lt+'|*') : ('*|'+rt)));
            fn = vr[tp][op];

            if (isText(fn))
            { fn = Function("lv","rv","lt","rt", ('return '+fn+';')); }

            rd = fn(rd,iv,lt,rt);
         };

         return rd;
      }
      .Join
      ({
         'VO|*':
         {
            '﹢':'rv',
            '﹣':'',
            '﹡':'',
            '﹨':'',
            '﹪':'',
            'ˆ':'',
            '﹦':'((rt == "VO") ? true : false)',
            '∼':'(!rv ? true : false)',
            '﹤':'((rt == "VO") ? false : true)',
            '﹥':'false',
            '﹠':'false',
            '‖':'rv',
            '﹖':'false',
            '﹗':'(!rv ? true : false)',
         },

         '*|VO':
         {
            '﹢':'lv',
            '﹣':'lv',
            '﹡':'',
            '﹨':'lv',
            '﹪':'lv',
            'ˆ':'',
            '﹦':'((lt == "VO") ? true : false)',
            '∼':'(!lv ? true : false)',
            '﹤':'false',
            '﹥':'((lt == "VO") ? false : true)',
            '﹠':'false',
            '‖':'lv',
            '﹖':'(!lv ? false : true)',
            '﹗':'true',
         },


         'QB|*':
         {
            '﹒':'',
            '﹢':'',
            '﹣':'',
            '﹡':'',
            '﹨':'',
            '﹪':'',
            'ˆ':'',
            '﹦':'',
            '∼':'',
            '﹤':'',
            '﹥':'',
            '﹠':'',
            '‖':'',
            '﹖':'',
            '﹗':'',
         },

         '*|QB':
         {
            '﹒':'',
            '﹢':'',
            '﹣':'',
            '﹡':'',
            '﹨':'',
            '﹪':'',
            'ˆ':'',
            '﹦':'',
            '∼':'',
            '﹤':'',
            '﹥':'',
            '﹠':'',
            '‖':'',
            '﹖':'',
            '﹗':'',
         },
      }),
   // -----------------------------------------------------------------------------------------------------





   // func :: desect : split up minified vamp-text into a list of same-level sections
   // -----------------------------------------------------------------------------------------------------
      desect:function(text)
      {
         var span,last,dlim,rbop,reop,rlvl,resl,bufr,indx,char;

         span = text.length;
         last = (span -1);
         dlim = ['﹐','﹔'];
         rlst = {'﹕':dlim, '‷':'‴', '﹙':'﹚', '﹝':'﹞', '﹛':'﹜'};
         rbop = null;
         reop = null;
         rlvl = 0;
         resl = [];
         bufr = '';


         for (indx=0; indx<span; indx++)
         {
            char = text[indx];
            bufr+= char;

            if (rlvl < 1)
            {
               if (rlst[char])
               {
                  rbop = char;
                  reop = rlst[rbop];
                  rlvl+= 1;
                  continue;
               }

               if (dlim.hasAny(char))
               {
                  resl[resl.length] = bufr;
                  bufr = '';
                  continue;
               }
            }

            if ((rlvl > 0) && reop.hasAny(char))
            {
               rlvl-= 1;
               if (indx == last){ resl[resl.length] = bufr; }
               continue;
            }
         }


         return resl;
      },
   // -----------------------------------------------------------------------------------------------------





   // func :: decode : parse into runtime
   // -----------------------------------------------------------------------------------------------------
      decode:function(text,vars,done,mini)
      {
         var list;

         text = (mini ? text : Vamp.minify(text));
         vars = (isNode(vars) ? vars : {});
         list = Vamp.desect(text);

         list.Each = function(sect)
         {
            Dump(sect);
         };
      }
      .Join
      ({
         extn:{v:'Vamp',vmp:'Vamp'},

         expr: // expression operators
         {
            '.':/a-zA-Z0-9_\(/,  // select - as in "chica's boobs"   .: chica.boobs
            '+':null,            // add / insert
            '-':null,            // subtract / remove
            '*':null,            // multiply / combine
            '/':null,            // divide / chop
            '%':null,            // modulus / modify
            '^':null,            // powerOf / parentOf
            '=':null,            // strict compare
            '~':null,            // loose compare
            '<':null,            // less-than
            '>':null,            // more-than
            '&':null,            // and
            '|':null,            // else    / boolean-test(alternative)
            '?':null,            // really? / boolean-cast(either-or)
            '!':null,            // !toggle / boolean-cast(negative-of)
         },

         mopr: // multi-level operators
         {
            ':':'\n;,)]}'.Chop(1),// define
            '(':')',             // call/express
            '{':'}',             // attribute
            '[':']',             // content
         },

         dlim: // delimiter operators
         {
            "\n":null,           // next
            ';' :null,           // next
            ',' :null,           // next
         },

         quot: // quoted-text operators
         {
            '`' :'`',            // multi-line
            '"' :'"',            // single-line
            "'" :"'",            // single-line
            '[|':'|]',           // multi-line  (alternative content)
            // '‷' :'‴',            // multi-line  (minified)
         },

         omit: // comment operators
         {
            '# '   : "\n",
            '##'   : "\n",
            '#! '  : "\n",
            '!# '  : "\n",
            '.: '  : "\n",
            ':: '  : "\n",
            ':::'  : "\n",
            '---'  : "\n",
            '==='  : "\n",
            '// '  : "\n",
            '\\\\ ': "\n",
            '/*'   : '*/',            // muli-line
            "\n--" : ["\n--","\n::"], // muli-line
         },

         escp: // escape characters in quoted-string
         {
            'n':"\n",
            'r':"\r",
            't':"\t",
            "'":"'",
            '"':'"',
            '`':'`',
            '[|':'[|',
         },

         swap: // swap operators with (special) single operators
         {
            '+=':'⨥',
            '-=':'⨪',
            '*=':'⨰',
            '/=':'⨫',
            '>=':'≤',
            '<=':'≥',
            '==':'﹦',
            '&&':'﹠',
            '||':'‖',
            '.' :'﹒',
            '+' :'﹢',
            '-' :'﹣',
            '*' :'﹡',
            '/' :'﹨',
            '%' :'﹪',
            '^' :'ˆ',
            '=' :'﹦',
            '~' :'∼',
            '<' :'﹤',
            '>' :'﹥',
            '&' :'﹠',
            '|' :'‖',
            '?' :'﹖',
            '!' :'﹗',
            ':' :'﹕',
            ',' :'﹐',
            ';' :'﹔',
            '\n':'﹔',

            '(' :'﹙',
            ')' :'﹚',
            '[' :'﹝',
            ']' :'﹞',
            '{' :'﹛',
            '}' :'﹜',
         },
      }),
   // -----------------------------------------------------------------------------------------------------
   });
// --------------------------------------------------------------------------------------------------------
