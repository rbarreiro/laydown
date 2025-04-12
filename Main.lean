import Laydown

def schema :=
  mkSchema ["caaty"]
  [
    (
      "chatMessage",
      .tuple [.string, .string],
      .record [
        ("timestamp", .datetime),
        (
          "content",
          .sum [
            (
              "userMessage",
              .record [("text", .string)]
            ),
            (
              "form",
              .record [
              ]
            )
          ]
        )
      ]
    )
  ]

def server := #server ["user", "admin"] [schema]{
  dbService :
    {
      name := "userMessage",
      args := [("message", .string), ("chatId", .string)],
      res := option .string,
      access := .roles ["user", "admin"],
      kind := .rpc
    } :=
    [laydown|
      do {
        let n ← now,
        let u ← uuid,
        let r_ ← chatMessage~insertI
                    (chatId, u,)
                    {timestamp := n, content := Mk(userMessage, {text := message})},
        !pure Mk(none)
      }
    ],
  dbService :
    {
      name := "getMessages",
      args := [("chatId", .string)],
      res := changes idValueType(schema, "chatMessage"),
      access := .roles ["user", "admin"],
      kind := .stream
    } :=
    [laydown|
      !pure ( !streamChanges (
        chatMessage~between (!setDim1_2 chatId)
      ))
    ]
}

def showMsg [SubEnv ui e] : Lexp e (idValueType(schema, "chatMessage") ⟶ .effect .ui) :=
  [laydown|
    λ msg =>
      match msg~value~content with {
        Mk (userMessage, userMsg) =>
          [ui| {userMsg~text} ],
        Mk (form, formMsg) =>
          [ui| form]
      }
  ]

def chat [SubEnv ui e]: Lexp e ((serviceGroup ["userMessage", "getMessages"] server) ⟶ .effect .ui) :=
  [laydown|
    λ api =>
      do{
        let send : option .string ⟶ .effect unit := match{
          Mk(some, m) => do {
            let _ ← api~userMessage {message := m, chatId := "chat0"},
            !pure ()
          },
          Mk(none) => !pure ()
        },
        let messages ← api~getMessages {chatId := "chat0"},
        [ui|
          {{forChanges msg in messages order by msg~value~timestamp}
            {!showMsg msg} <br>
          }
          <br>
          [formR|send| ___ ]
        ]
      }
  ]

def loginPage [SubEnv ui e] : Lexp e (flux (.record [("user", .string), ("password", .string)])) :=
  [laydown|
    [formF|
      "user" :: ___
      "password" :: *___
      s["login"]
    ]
  ]

def app := #rapp [server] {
    [laydown| do{
      let disp ← !createSignal [ui| {""}],
      let flx  := do{
        let l ← !loginPage,
        let api ← !lift (connect (Mk(user, l))),
        match api with{
          Mk (fail, error) => !terminal [ui| login fail ],
          Mk (guest, api) => !terminal [ui| guest ],
          Mk (user, api) => !terminal (!chat api),
          Mk (admin, api) => !terminal (!chat api)
        }
      },
      !startFlux disp~set flx,
      [ui| {disp~signal}]
    }
    ]
}


#eval genApp app
#eval deployApp "caaty_def.json" "localhost" 6401 app

--def main : IO Unit :=
--  IO.println s!"Hello, !"
