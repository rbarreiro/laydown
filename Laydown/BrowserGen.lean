import Laydown.UI
import Laydown.JSGen


def runtime : String :=
  "
    const text = txt => () => document.createTextNode(txt);

    const signalText = sig => () => {
      const span = document.createElement('span');
      span.appendChild(text(sig.get()));
      const i = sig.subscribe(newVal => {
        span.innerHTML = '';
        span.appendChild(text(newVal));
      });
      return span;
    }

    const button = label => click => () => {
      const b = document.createElement('button');
      b.appendChild(text(label));
      b.addEventListener('click', click);
      return b;
    }

    const concat = a => b => () => {
      const c = document.createElement('span');
      c.appendChild(a());
      c.appendChild(b());
      return c;
    }

  "

def browserTemplate (client : String) : String :=
  "
  <!DOCTYPE html>
  <html>
  <body>
    <div id=\"root\"></div>
    <script src=\"https://cdnjs.cloudflare.com/ajax/libs/immutable/5.0.3/immutable.min.js\"
            integrity=\"sha512-7gKzXmjcoHpm+sl09bSCRqlj8XlxpyNhjny1jur6yyqQ6Tiw6q/loRThw10PcTYnjiWeNJZOpshsbCSJT9TLYA==\"
            crossorigin=\"anonymous\"
            referrerpolicy=\"no-referrer\">
    </script>
    <script>" ++ jsRuntime ++ runtime ++ "\n\n" ++
      "const mainNode =" ++ client ++ ";
      document.body.appendChild(mainNode());
    </script>
  </body>
  </html>
  "

def genBrowser [SubEnv ui e] : Lexp e (.effect .ui) → String :=
  browserTemplate ∘ jsGen

def writeBrowser [SubEnv ui e] (client : Lexp e (.effect .ui)) (path : String) : IO Unit :=
  IO.FS.writeFile path (genBrowser client)

def test : Lexp ui (.int ⟶ .effect (.record [("set", .int ⟶ .effect .unit), ("value", .signal .int)])) :=
  [laydown| !createSignal]


def test2 : Lexp ui (.effect .ui) :=
  [laydown|
    do{
      let counter ← !createSignal 0,
      [ui| hello world]
    }
  ]

#eval genBrowser test2
#eval writeBrowser test2 "../test.html"
