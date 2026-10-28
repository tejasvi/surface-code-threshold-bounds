import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9560 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9560 = true := by
  decide +kernel

theorem tot9560 : totK PD2M8K2 D2M8K2.t9560 = [0, 181922526395, 483114871314, 212450366409, 9713690252, 0, 0, 0] := by
  decide +kernel

theorem rows9561 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9561 = true := by
  decide +kernel

theorem tot9561 : totK PD2M8K2 D2M8K2.t9561 = [0, 131817466324, 443328503238, 283212881286, 20023055003, 0, 0, 0] := by
  decide +kernel

theorem rows9562 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9562 = true := by
  decide +kernel

theorem tot9562 : totK PD2M8K2 D2M8K2.t9562 = [0, 0, 292259233062, 479075811044, 84286303403, 1239866073, 0, 0] := by
  decide +kernel

theorem rows9563 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9563 = true := by
  decide +kernel

theorem tot9563 : totK PD2M8K2 D2M8K2.t9563 = [0, 161410853672, 432670009081, 294344349986, 32542041314, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
