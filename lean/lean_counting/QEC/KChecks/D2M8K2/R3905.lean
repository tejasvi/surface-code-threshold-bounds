import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15620 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15620 = true := by
  decide +kernel

theorem tot15620 : totK PD2M8K2 D2M8K2.t15620 = [0, 0, 232435430890, 502787932804, 161796887210, 8423393484, 0, 0] := by
  decide +kernel

theorem rows15621 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15621 = true := by
  decide +kernel

theorem tot15621 : totK PD2M8K2 D2M8K2.t15621 = [0, 106423910014, 350351182414, 335790743970, 82599832170, 3462014130, 0, 0] := by
  decide +kernel

theorem rows15622 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15622 = true := by
  decide +kernel

theorem tot15622 : totK PD2M8K2 D2M8K2.t15622 = [0, 165966959591, 441834338169, 271427151038, 29915471674, 0, 0, 0] := by
  decide +kernel

theorem rows15623 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15623 = true := by
  decide +kernel

theorem tot15623 : totK PD2M8K2 D2M8K2.t15623 = [0, 147654195107, 447615964095, 278751398024, 23634285059, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
