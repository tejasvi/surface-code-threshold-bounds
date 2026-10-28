import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10596 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10596 = true := by
  decide +kernel

theorem tot10596 : totK PD2M8K2 D2M8K2.t10596 = [0, 92968305029, 384691295168, 396625465795, 50768476307, 0, 0, 0] := by
  decide +kernel

theorem rows10597 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10597 = true := by
  decide +kernel

theorem tot10597 : totK PD2M8K2 D2M8K2.t10597 = [0, 171165353242, 448441076580, 272204157030, 21560386900, 0, 0, 0] := by
  decide +kernel

theorem rows10598 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10598 = true := by
  decide +kernel

theorem tot10598 : totK PD2M8K2 D2M8K2.t10598 = [0, 154431426411, 462474887964, 272243660181, 27195105329, 0, 0, 0] := by
  decide +kernel

theorem rows10599 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10599 = true := by
  decide +kernel

theorem tot10599 : totK PD2M8K2 D2M8K2.t10599 = [0, 0, 179303566033, 446655970847, 255393054019, 25111632603, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
