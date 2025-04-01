import Laydown.UI
import Laydown.JSGen


def runtime : String :=
  "
    const button = label => click => () => {
      const b = document.createElement('button');
      b.appendChild(label());
      b.addEventListener('click', click);
      b.classList.add('btn');
      b.classList.add('btn-primary');
      return b;
    }

    const text = txt => () => document.createTextNode(txt);

    const signalUI = sig => () => {
      const span = document.createElement('span');
      span.appendChild(sig.get()());
      const i = sig.subscribe(newVal => {
        span.innerHTML = '';
        span.appendChild(newVal());
      });
      return span;
    }

    const signalListUI = sig => render => () => {
      const span = document.createElement('span');
      const list = sig.get();
      list.forEach(x => {
        span.appendChild(render(x)());
      });
      const i = sig.subscribe(newVal => {
        span.innerHTML = '';
        newVal.forEach(x => {
          span.appendChild(render(x)());
        });
      });
      return span;
    }

    const concat = a => b => () => {
      const c = document.createElement('span');
      c.appendChild(a());
      c.appendChild(b());
      return c;
    }

    const displayList = xs => () => {
      const c = document.createElement('span');
      xs.forEach(x => {
        c.appendChild(x());
      });
      return c;
    }

    const createSignal = init => () => {
      let currentValue = init;
      let callbacks = {};
      return Immutable.Map({
        set : (newVal) => () => {
          currentValue = newVal;
          Object.values(callbacks).forEach(cb => cb(currentValue));
        },
        update : f => () =>{
          currentValue = f(currentValue);
          Object.values(callbacks).forEach(cb => cb(currentValue));
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
          get : () => currentValue
        },
        get : () => currentValue
      });
    }

    const mapSignal = f => sig => {
      return {
        subscribe : (cb) => {
          return sig.subscribe(val => cb(f(val)));
        },
        get : () => f(sig.get()),
        unsubscribe : sig.unsubscribe
      }
    }

    const currentValue = sig => () => sig.get();
    const br = () => document.createElement('br');
    const textInput = cb => () => {
      const input = document.createElement('input');
      input.addEventListener('input', () => cb(input.value)());
      return input;
    }

    const streamChangesUI = stream => render => () => {
      //console.log('streamChangesUI', stream);
      return text('streamChangesUI')()
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
    <script>" ++ jsRuntime ++ runtime ++ "\n\n" ++ extra ++ "\n" ++
      "const mainNode =" ++ client ++ ";
      document.body.appendChild(mainNode());
    </script>
  </body>
  </html>
  "

def genBrowser [SubEnv ui e]  (x : Lexp e (.effect .ui)) : String :=
  browserTemplate "" (jsGen x)

def writeBrowser [SubEnv ui e] (client : Lexp e (.effect .ui)) (path : String) : IO Unit :=
  IO.FS.writeFile path (genBrowser client)
