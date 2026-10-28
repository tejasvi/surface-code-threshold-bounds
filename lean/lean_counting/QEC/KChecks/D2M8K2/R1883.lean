import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7532 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7532 = true := by
  decide +kernel

theorem tot7532 : totK PD2M8K2 D2M8K2.t7532 = [0, 0, 186500241434, 470264239907, 248862576235, 22714972096, 0, 0] := by
  decide +kernel

theorem rows7533 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7533 = true := by
  decide +kernel

theorem tot7533 : totK PD2M8K2 D2M8K2.t7533 = [0, 0, 172679268313, 463428707169, 241195606938, 13484745446, 0, 0] := by
  decide +kernel

theorem rows7534 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7534 = true := by
  decide +kernel

theorem tot7534 : totK PD2M8K2 D2M8K2.t7534 = [0, 0, 0, 308811225837, 494695639791, 98994994061, 2909416399, 0] := by
  decide +kernel

theorem rows7535 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7535 = true := by
  decide +kernel

theorem tot7535 : totK PD2M8K2 D2M8K2.t7535 = [0, 0, 89631789061, 307934611202, 389300582372, 106167216088, 2250452236, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
