import Laydown.UI
import Laydown.JSGen


def runtime : String :=
  "
    const button = label => click => r => {
      const b = document.createElement('button');
      b.setAttribute('type', 'button');
      label(l => b.appendChild(l));
      b.addEventListener('click', () => click(x=>x));
      b.classList.add('btn');
      b.classList.add('btn-primary');
      r(b);
    }

    const text = txt => r => r(document.createTextNode(txt));

    const signalUI = sig => r => {
      const span = document.createElement('span');
      const i = sig.subscribe(newVal => {
        newVal(n => {
        span.innerHTML = '';
        span.appendChild(n);
        });
      });
      r(span);
    }

    const signalListUI = sig => render => r => {
      const span = document.createElement('span');
      const i = sig.subscribe(newVal => {
        span.innerHTML = '';
        newVal.forEach(x => {
          render(x).then(z => {
            span.appendChild(z());
          });
        });
      });
      r(span);
    }

    const concat = a => b => r => {
      a(a_ => {
        b(b_ => {
          const c = document.createElement('span');
          c.appendChild(a_);
          c.appendChild(b_);
          r(c);
        });
      })
    }

    const displayList = xs => r => {
      joinEffects(xs)(xs_ => {
        const c = document.createElement('span');
        xs_.forEach(x => {
          c.appendChild(x());
        });
        r(c);
      });
    }

    const createSignal = init => r => {
      let currentValue = init;
      let callbacks = {};
      r(Immutable.Map({
        set : (newVal) => r => {
          currentValue = newVal;
          Object.values(callbacks).forEach(cb => cb(currentValue));
          r();
        },
        update : f => r => {
          currentValue = f(currentValue);
          Object.values(callbacks).forEach(cb => cb(currentValue));
          r();
        },
        signal : {
          subscribe : (cb) => {
            const i = crypto.randomUUID();
            callbacks[i] = cb;
            cb(currentValue);
            return i;
          },
          unsubsribe : (i) => {
            delete callbacks[i];
          },
          get : r => r(currentValue)
        },
        get : r => r(currentValue)
      }));
    }

    const mapSignal = f => sig => {
      return {
        subscribe : (cb) => {
          return sig.subscribe(val => cb(f(val)));
        },
        get : r => sig.get(x => r(f(x))),
        unsubscribe : sig.unsubscribe
      }
    }

    const br = r => r(document.createElement('br'));

    const textInput = init => cb => r => {
      const input = document.createElement('input');
      input.value = init;
      input.setAttribute('type', 'text');
      input.classList.add('form-control');
      input.addEventListener('input', () => cb(input.value)(x => x) );
      r(input);
    }

    const streamChangesUI = stream => render => orderBy => r => {
      const span = document.createElement('span');
      const contentRefs = [];
      stream(x => {
        if(x.has('added')) {
          const v = x.get('added');
          const k = v.toJSON();
          const o = orderBy(v);
          render(v)(z => {
            if(contentRefs.length === 0) {
              contentRefs.push({key: k, orderKey: orderBy(v)});
              span.appendChild(z);
            }else if(o<= contentRefs[0].orderKey) {
              contentRefs.unshift({key: k, orderKey: o});
              span.prepend(z);
            }else if(o >= contentRefs[contentRefs.length - 1].orderKey) {
              contentRefs.push({key: k, orderKey: o});
              span.appendChild(z);
            }else{
              for(let i = contentRefs.length - 2; i >= 0; i--) {
                if(o >= contentRefs[i].orderKey) {
                  contentRefs.splice(i + 1, 0, {key: k, orderKey: o});
                  span.insertBefore(z, span.childNodes[i + 1]);
                  break;
                }
              }
            }
          });
        } else if(x.has('removed')) {
          console.log(x);
        }else{
          console.log(x);
        }
      });
      r(span);
    }

    const form = f => render => r => {
      const frm = document.createElement('form');
      frm.addEventListener('submit', e => {
        e.preventDefault();
        f(Immutable.Map({reset: r => r(frm.reset()) }))(x => x);
      });
      render(render_ =>{
        frm.appendChild(render_);
        r(frm);
      })
    }
  "

def browserTemplate (extra : String) (client : String) : String :=
  "
  <!DOCTYPE html>
  <html>
  <head>
    <link href=\"https://cdn.jsdelivr.net/npm/bootstrap@5.3.3/dist/css/bootstrap.min.css\" rel=\"stylesheet\" integrity=\"sha384-QWTKZyjpPEjISv5WaRU9OFeRpok6YctnYmDr5pNlyT2bRjXh0JMhjY6hW+ALEwIH\" crossorigin=\"anonymous\">
    <script src=\"https://cdn.jsdelivr.net/npm/bootstrap@5.3.3/dist/js/bootstrap.bundle.min.js\" integrity=\"sha384-YvpcrYf0tY3lHB60NNkmXc5s9fDVZLESaAA55NDzOxhy9GkcIdslK1eN7N6jIeHz\" crossorigin=\"anonymous\"></script>
  </head>
  <body>
    <div id=\"root\"></div>
    <script src=\"https://cdn.jsdelivr.net/npm/immutable@5.1.1/dist/immutable.min.js\"></script>
    <script>" ++ jsRuntime ++ runtime ++ "\n\n" ++ extra ++ "\n" ++ "
      const mainNode =" ++ client ++ ";

      mainNode(n => {document.body.appendChild(n)});
    </script>
  </body>
  </html>
  "

def genBrowser [SubEnv ui e]  (x : Lexp e (.effect .ui)) : String :=
  browserTemplate "" (jsGen x)

def writeBrowser [SubEnv ui e] (client : Lexp e (.effect .ui)) (path : String) : IO Unit :=
  IO.FS.writeFile path (genBrowser client)
