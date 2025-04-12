import Laydown.UI
import Laydown.JSGen


def runtime : String :=
  "
    ctxt = ctxt.set('button', label => click => r => {
      const b = document.createElement('button');
      b.setAttribute('type', 'button');
      label(l => b.appendChild(l));
      b.addEventListener('click', () => click(x=>x));
      b.classList.add('btn');
      b.classList.add('btn-primary');
      r(b);
    });

    ctxt = ctxt.set('text', txt => r => r(document.createTextNode(txt)));

    ctxt = ctxt.set('signalUI', sig => r => {
      const span = document.createElement('span');
      const i = sig.subscribe(newVal => {
        newVal(n => {
          span.innerHTML = '';
          span.appendChild(n);
        });
      });
      r(span);
    });

    ctxt = ctxt.set('signalListUI', sig => render => r => {
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
    });

    ctxt = ctxt.set('concat', a => b => r => {
      a(a_ => {
        b(b_ => {
          const c = document.createElement('span');
          c.appendChild(a_);
          c.appendChild(b_);
          r(c);
        });
      });
    });

    ctxt = ctxt.set('displayList', xs => r => {
      joinEffects(xs)(xs_ => {
        const c = document.createElement('span');
        xs_.forEach(x => {
          c.appendChild(x());
        });
        r(c);
      });
    });

    ctxt = ctxt.set('createSignal', init => r => {
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
    });

    ctxt = ctxt.set('mapSignal', f => sig => {
      return {
        subscribe : (cb) => {
          return sig.subscribe(val => cb(f(val)));
        },
        get : r => sig.get(x => r(f(x))),
        unsubscribe : sig.unsubscribe
      }
    });

    ctxt = ctxt.set('pureSignal', x => {
      return {
        subscribe : cb => {
          cb(x);
          return crypto.randomUUID();
        },
        get : r => r(x),
        unsubscribe : () => {}
      }
    });

    ctxt = ctxt.set('seqSignal', f => x => {
      const x_ = x();
      let callbacks = {};
      f.subscribe(f_ => {
        Object.values(callbacks).forEach(cb => x_.get(x__ => cb(f_(x__))));
      });

      x_.subscribe(x__ => {
        Object.values(callbacks).forEach(cb => f.get(f_ => cb(f_(x__))));
      });

      return {
        subscribe : cb => {
          const i = crypto.randomUUID();
          callbacks[i] = cb;
          f.get(f_ => {
            x_.get(x__ => cb(f_(x__)));
          });
          return i;
        },
        get : r => f.get(f_ => x_.get(x__ => r(f_(x__)))),
        unsubscribe : i => {
          delete callbacks[i];
        }
      }
    });

    ctxt = ctxt.set('br', r => r(document.createElement('br')));

    ctxt = ctxt.set('textInput', init => cb => r => {
      const input = document.createElement('input');
      input.value = init;
      input.setAttribute('type', 'text');
      input.classList.add('form-control');
      input.addEventListener('input', () => {cb(input.value)(x => x)});
      r(input);
    });

    ctxt = ctxt.set('passwordInput', init => cb => r => {
      const input = document.createElement('input');
      input.value = init;
      input.setAttribute('type', 'password');
      input.classList.add('form-control');
      input.addEventListener('input', () => {cb(input.value)(x => x)});
      r(input);
    });

    ctxt = ctxt.set('streamChangesUI', stream => render => orderBy => r => {
      const span = document.createElement('span');
      const contentRefs = {};
      stream(x => {
        if(x.has('added')) {
          const v = x.get('added');
          const k = v.toJSON();
          render(v)(z => {
            contentRefs[k] = (contentRefs[k] ?? []).concat([z]);
            span.appendChild(z);
          });
        } else if(x.has('removed')) {
          console.log(x);
        } else {
          console.log(x);
        }
      });
      r(span);
    });

    ctxt = ctxt.set('form', f => render => r => {
      const frm = document.createElement('form');
      frm.addEventListener('submit', e => {
        e.preventDefault();
        f(Immutable.Map({reset: r => r(frm.reset())}))(x => x);
      });
      render(render_ => {
        frm.appendChild(render_);
        r(frm);
      });
    });

    ctxt = ctxt.set('withLabel', label => value => r => {
      const div = document.createElement('div');
      div.classList.add('mb-3');
      const l = document.createElement('label');
      l.classList.add('form-label');

      div.appendChild(l);
      value(value_ => {
        label(label_ => {
          l.appendChild(label_);
          div.appendChild(l);
          div.appendChild(value_);
          r(div);
        });
      });
    });

    ctxt = ctxt.set('consoleLog', x => r => {
      console.log(x);
      r();
    });

    ctxt = ctxt.set('submitButton', label => r => {
      const b = document.createElement('button');
      b.setAttribute('type', 'submit');
      label(l => b.appendChild(l));
      b.classList.add('btn');
      b.classList.add('btn-primary');
      r(b);
    });

    ctxt = ctxt.set('subscribeSignal', sig => cb => r => {
      const i = sig.subscribe(v => cb(v)(x => x));
      r(x => x);
    });
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
