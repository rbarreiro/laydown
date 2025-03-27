const express = require('express');
const Joi = require('joi');
const app = express();
var expressWs = require('express-ws')(app);
const port = 3000;
const swaggerUi = require('swagger-ui-express');
const swaggerDocument = require('./swagger.json');
const r = require('rethinkdb');
const im = require('immutable');
const bcrypt = require('bcrypt');

const saltRounds = 10;


const pages = {};
const services = {};

const runtime = im.Map({
    seqEffect : x => y => () => [x(), y()],
    bindEffect : x => y => () => x().do((z => y(z)())) ,
    pureEffect : x => () => x,
    tubleCons : x => xs => xs.prepend(x)
})

function exp2query(exp, ctxt){
    switch(exp[0]){
        case "app":
            return exp2query(exp[1], ctxt)(exp2query(exp[2],ctxt));
        case "var":
            if(ctxt.has(exp[1]))
                return ctxt.get(exp[1]);
            else
                console.log(ctxt.toJS());
                throw "Variable not found: " + exp[1];
        case "seqEffect":
            return runtime.get("seqEffect");
        case "bindEffect":
            return runtime.get("bindEffect");
        case "litStr":  
            return r.expr(exp[1])
        case "pureEffect":
            return runtime.get("pureEffect");
        case "tupleBase":
            return r.expr([]);
        case "tupleCons":
            return runtime.get("tubleCons");
        case "lambda":
            return x => exp2query(exp[2], ctxt.set(exp[1], x));
        case "recordGet":
            return exp2query(exp[2], ctxt).get(exp[1]);
        case "recordcons":
            return exp2query(exp[3],ctxt).merge(r.object(exp[1], exp2query(exp[2], ctxt)));
        case "recordnil":
            return r.expr({});
        case "mk":
            return r.object(exp[1], exp2query(exp[2], ctxt));
        
    }
    throw "Unknown expression: " + exp;
}


const migrationCtxt = im.Map({
    tableCreate : db => table => () => r.db(db).tableCreate(table),
});

const dbServiceCtxt = im.Map({
    now : () => r.now(),
    uuid : () => r.uuid()
});

function runMigrations(conn, appId, migrations, then){
    r.db("appserver").table("migration_status").get(appId).run(conn, (err, res)=>{
        if (err) throw err;
        if (res == null){
            doneMigrations = [];
        }else{
            doneMigrations = res.migrations;
        }
        if (doneMigrations.length > migrations.length){
            console.log("Migration error: ", appId, " has less migrations than expected")
            return;
        }

        const queries = [];
        for(let i = 0; i < migrations.length; i++){
            if(doneMigrations.length <= i){
                queries.push(exp2query(JSON.parse(migrations[i]), migrationCtxt)());                
            }else{
                if (doneMigrations[i] != migrations[i]){
                    console.log("Migration error: ", appId, ", ", i, " has different migration than expected")
                    console.log(doneMigrations[i])
                    console.log(migrations[i])
                    return;
                }
            }
        }
        if(queries.length > 0){
            queries.push(r.db("appserver").table("migration_status").get(appId).replace({id: appId, migrations: migrations}));
            queries.forEach(q => console.log("q:", q.toString()));
            r.expr(r.expr(queries)).run(conn, (err, res)=>{
                if(err) throw err;
                then();
            });
        }else{
            then();
        }
        
    });
}

function addTablesToContext(appId, tables, ctxt){
    tables.forEach(t => {
        ctxt = ctxt.set(
            t[0], 
            im.Map({
                insertI: i => v => () => r.db("app_" + appId).table(t[0]).insert({id: i, value: v}),     
    }       )
        );
    });
    return ctxt;
}

function addArgToCtxt(x, ctxt){
    for (const key of Object.keys(x)) {
        ctxt = ctxt.set(key, r.expr(x[key]));
    }
    return ctxt
}

function onAppChanges(conn){
    r.expr([r.db("appserver").table("apps").wait(), r.db("appserver").table("migration_status").wait()]).run(conn, (err, res)=>{
        if (err) throw err;
        r.db("appserver").table("apps")
        .changes({includeInitial : true}).run(conn, (err, cursor)=>{
            if (err) throw err;
            cursor.each((err, row)=>{
                if (err) throw err;
                r.expr([
                    r.branch(
                        r.dbList().contains("app_" + row.new_val.id).not(), 
                        r.dbCreate("app_" + row.new_val.id),
                        null
                    ),r.branch(
                        r.db("appserver").tableList().contains("users_" + row.new_val.id).not(), 
                        r.db("appserver").tableCreate("users_" + row.new_val.id),
                        null
                    )
                ]).run(conn, (err, res)=>{
                    if (err) throw err;
                    pages[row.new_val.id] = row.new_val.page;
                    const appId = row.new_val.id; 
                    runMigrations(conn, appId, row.new_val.migrations, ()=>{
                        const server = JSON.parse(row.new_val.server);
                        const tables  = JSON.parse(row.new_val.tables);
                        const ctxt = addTablesToContext(appId, tables, dbServiceCtxt);
                        services[row.new_val.id] = {}
                        server.forEach(srv => {
                            if(srv[0] === "dbService"){
                                services[row.new_val.id][srv[1].name] ={
                                    access : srv[1].access,
                                    query : x => exp2query(srv[2], addArgToCtxt(x, ctxt)),
                                }
                            }
                        })
                        console.log("launching server for ", row.new_val.id)
                    });
                });
            })
        });
    });
}


var connection = null;
r.connect( {host: 'rethinkdb', port: 28015}, function(err, conn) {
    if (err) throw err;
    r.branch(
        r.dbList().contains("appserver").not(), 
        [
            r.dbCreate("appserver"),
            r.db("appserver").tableCreate("apps"),
            r.db("appserver").tableCreate("migration_status")
        ],
        null
    ).run(conn, (err, res)=>{
        if (err) throw err;
        connection = conn;
        onAppChanges(conn);
    })
});

app.use('/docs', swaggerUi.serve, swaggerUi.setup(swaggerDocument));

app.use(express.json());

app.get('/', (req, res) => {
    r.db("appserver").table("apps").pluck("id").coerceTo('array')
    .run(connection, (err, r)=>{
        if (err) throw err;
        res.send(r)
    })
})

const newappSchema = Joi.object({
    id : Joi.string().required(), 
    page : Joi.string().required(),
    server : Joi.string().required(),
    migrations : Joi.array().items(Joi.string()).required(),
    tables : Joi.string().required(),
}).required();

app.post('/upsertapp', (req, res) => {
    const { error, value } = newappSchema.validate(req.body);
    if (error) {
        return res.status(400).send(error.details[0].message);
    }
    r.db('appserver').table("apps").get(value.id).replace(value)
    .run(connection, (err, r)=>{
        if (err) throw err;
        console.log(value.id, "updated")
        res.send(r)
    })
});

app.get('/app/:id', (req, res) => {
    res.send(pages[req.params.id]);
});

const serviceCallSchema = Joi.object({
    service : Joi.string().required(),
    reqId : Joi.string().required(),
    arg : Joi.any(),
}).required();

const loginSchema = Joi.alternatives().try(
    Joi.object({
        "user": Joi.object({
            user : Joi.string().required(),
            password : Joi.string().required(),
        }),
    }),
    Joi.object({
        "guest" : Joi.any(),
    })
);

app.ws('/appcom/:id', function(ws, req) {
  let role = null;
  ws.on('message', function(msg) {
    if(role === null){
        const { error, value } = loginSchema.validate(JSON.parse(msg));
        if (error) {
            console.log(error);
        }
        if(value.user){
            r.db("appserver").table("users_" + req.params.id).get(value.user.user).run(connection, (err, res)=>{
                if (err) throw err;
                if(res){
                    if(res.hasOwnProperty("password")){
                        if(res.password === value.user.password){
                            role = res.role;
                            ws.send(JSON.stringify({role: role}));
                        }else{
                            ws.send(JSON.stringify({error: "Invalid password"}));
                        }
                    }else{
                        bcrypt.compare(value.user.password, res.saltedPassword, function(err, result) {
                            if(result){
                                role = res.role;
                                ws.send(JSON.stringify({role: role}));
                            }else{
                                ws.send(JSON.stringify({error: "Invalid password"}));
                            }
                        });
                    }
                }else{
                    ws.send(JSON.stringify({error: "Invalid user"}));
                }
            });
        }else{
            role = "guest";
            ws.send(JSON.stringify({role: role}));
        }        
    }else{
        const { error, value } = serviceCallSchema.validate(JSON.parse(msg));
        if (error) {
            console.log(error);
            return;
        }

        const s = services[req.params.id][value.service];
        if(s.access.hasOwnProperty('all') || s.access.roles.list.includes(role)){
            const q = s.query(value.arg)();
            q.run(connection, (err, res)=>{
                if (err) throw err;
                ws.send(JSON.stringify({reqId: value.reqId, result: res}));
            });
        }else{
            ws.send(JSON.stringify({reqId: value.reqId, error: "Unauthorized"}));
        }
    }
  });
});

app.listen(port, () => {
  console.log(`appserver listening on port ${port}`)
});