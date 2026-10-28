import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8056 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8056 = true := by
  decide +kernel

theorem tot8056 : totK PD2M8K2 D2M8K2.t8056 = [0, 45772753867, 322979265909, 433734400562, 96771240301, 1198073392, 0, 0] := by
  decide +kernel

theorem rows8057 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8057 = true := by
  decide +kernel

theorem tot8057 : totK PD2M8K2 D2M8K2.t8057 = [0, 36449493752, 272849114008, 452306459733, 125974286866, 4257574148, 0, 0] := by
  decide +kernel

theorem rows8058 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8058 = true := by
  decide +kernel

theorem tot8058 : totK PD2M8K2 D2M8K2.t8058 = [0, 201147179050, 480563624051, 202741390887, 9846301812, 0, 0, 0] := by
  decide +kernel

theorem rows8059 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8059 = true := by
  decide +kernel

theorem tot8059 : totK PD2M8K2 D2M8K2.t8059 = [0, 85954675636, 368693439291, 348480201456, 60828039608, 1096505104, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
