import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3248 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3248 = true := by
  decide +kernel

theorem tot3248 : totK PD2M8K2 D2M8K2.t3248 = [89753051296, 397529228897, 353079459653, 55514040352, 1198073392, 0, 0, 0] := by
  decide +kernel

theorem rows3249 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3249 = true := by
  decide +kernel

theorem tot3249 : totK PD2M8K2 D2M8K2.t3249 = [0, 228590988114, 487162098371, 168477463835, 8466643012, 0, 0, 0] := by
  decide +kernel

theorem rows3250 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3250 = true := by
  decide +kernel

theorem tot3250 : totK PD2M8K2 D2M8K2.t3250 = [104542941805, 350613680406, 342358553448, 90207419583, 3579068459, 0, 0, 0] := by
  decide +kernel

theorem rows3251 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3251 = true := by
  decide +kernel

theorem tot3251 : totK PD2M8K2 D2M8K2.t3251 = [174971226779, 448461314912, 265540000942, 28306509322, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
