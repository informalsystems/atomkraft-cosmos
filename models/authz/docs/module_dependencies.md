# Module dependency graph

```mermaid
flowchart TB
    Authz_MC --> AuthzProperties --> Authz --> AuthzService & AuthzMessages & Maps
    AuthzService --> AuthzMessages --> MsgTypes & MsgErrors & Grants
    Grants -->|instance| GenericAuthorization & SendAuthorization & StakeAuthorization --> MsgTypes
    SendAuthorization & StakeAuthorization --> MsgErrors
```
