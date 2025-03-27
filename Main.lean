import Laydown

def schema :=
  SchemaDef.new "caaty"
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
  .dbService
    {
      name := "userMessage",
      args := [("message", .string), ("chatId", .string)],
      res := option .string,
      access := .roles ["user", "admin"]
    }
    (
      [laydown|
        do {
          let n ← now,
          let u ← uuid,
          let r_ ← chatMessage#insertI
                      (chatId, u,)
                      {timestamp := n, content := Mk(userMessage, {text := message})},
          return Mk(none)
        }
      ]
    )
}
def chat [SubEnv ui e]: Lexp e ((serviceGroup ["userMessage"] server) ⟶ .effect .ui) :=
  [laydown|
    λ api =>
      do{
        let msg ← !createSignal "",
        let send := do{
          let m ← msg#get,
          let _ ← api#userMessage {message := m, chatId := "chat0"},
          return ()
        },
        [ui|
          Chat<br>
          ___(msg#set) b[Send](send)
        ]
      }
  ]

def app := #rapp [server] {
    [laydown|
      do {
        let mainPage ← !createSignal [ui| connecting to ws],
        connect
          Mk(user, {user := "admin", password := "1234"})
          (match{
            Mk (guest, api) => mainPage#set [ui| guest ],
            Mk (user, api) => mainPage#set (!chat api#(userMessage)),
            Mk (admin, api) => mainPage#set (!chat api#(userMessage))
          }),
        [ui| {mainPage#signal}]
      }
    ]
}


#eval genApp app
#eval deployApp "localhost" 6401 app

--def main : IO Unit :=
--  IO.println s!"Hello, !"
