
/* Protex: PROLOG->LATEX Preprocessor */

#include <stdio.h>

isvalid(c) int c;
{ return (c>='A' && c<='Z')||(c>='a' && c<='z')||(c>='0'&&c<='9'); }

int ungetflag=0; 
int ungetchar;

get()
{if (ungetflag) {ungetflag=0; return ungetchar; }
 return getchar();
}

unget(c) int c;
{ ungetflag=1; ungetchar=c; }
 
process(c) int c;
{ int cc;
/*  if ('A'<=c && c<='Z')
    { printf("$%c",c);
      if ((cc=get())==c) { printf("'"); cc=get(); }
      if (!isvalid(cc)) { unget(cc); printf("$"); return; }
      printf("_{"); 
      do printf("%c",cc); while (isvalid(cc=get()));
      printf("}$"); unget(cc); return;
    } */
  switch(c)
  { case '<': printf("$<$"); break;
    case '>': printf("$>$"); break;
    case '_': printf("\\_\\hspace{0.1em}"); break;
    case '|': printf("$\\mid$"); break;
    case ' ': printf(" "); break;
    case '#': printf("\\#"); break;
    case '&': printf("\\&"); break;
    case '%': printf("\\%%"); break;
    case '{': printf("\\{"); break;
    case '}': printf("\\}"); break;
    case '\\': printf("$\\backslash$"); break;
    case '$': printf("\\$"); break;
    case '^': printf("\\^{}"); break;
    case '~': printf("{\\verb`~`}"); break;
    default:  printf("%c",c); break;
  }
}

main()
{ int c,i,
      eoln=1,
      tabbing=0;

  printf("\n%% begin ProTex\n");
  while ((c=get())!=EOF)
  { if (eoln)
      if (c=='%')
      { c=get();
        /* copy LaTeX input string */
        if (tabbing) 
            { printf("\n\\end{tabbing}\\end{sf}\n"); tabbing=0; }
        printf("\n");
        do printf("%c",c);
        while ((c=get())!='\n'); 
        eoln=1;
        continue;
      }  
      else
      { if (c=='\n') 
          { if (tabbing) printf("\\\\[-0.7ex]\n"); 
            eoln=1; continue; }
        if (tabbing) printf("\\\\[-0.15ex]\n");
        else { printf("\n\\begin{sf}\\begin{tabbing}\n"); tabbing=1; }
        i=0; 
        while (c==' ') { i++; c=get(); }
        if (i) printf("\\hspace{%dem}",i/2);
        if (c=='\n') eoln=1; 
        else { process(c);eoln=0; }
      }
    else 
      { if (c=='\n') eoln=1; else process(c); }
  }

  if (tabbing) printf("\n\\end{tabbing}\n");
  printf("\n%% end ProTex\n");


}

