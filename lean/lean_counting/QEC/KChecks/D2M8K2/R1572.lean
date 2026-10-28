import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6288 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6288 = true := by
  decide +kernel

theorem tot6288 : totK PD2M8K2 D2M8K2.t6288 = [0, 49155779871, 350977090588, 452572237855, 44874741921, 0, 0, 0] := by
  decide +kernel

theorem rows6289 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6289 = true := by
  decide +kernel

theorem tot6289 : totK PD2M8K2 D2M8K2.t6289 = [0, 159471445025, 442083980165, 280167227512, 28529815567, 0, 0, 0] := by
  decide +kernel

theorem rows6290 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6290 = true := by
  decide +kernel

theorem tot6290 : totK PD2M8K2 D2M8K2.t6290 = [0, 201629469805, 491434737755, 214049704504, 8941007701, 0, 0, 0] := by
  decide +kernel

theorem rows6291 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6291 = true := by
  decide +kernel

theorem tot6291 : totK PD2M8K2 D2M8K2.t6291 = [0, 172520944976, 461919817317, 248269940573, 23373646989, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
