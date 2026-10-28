import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6196 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6196 = true := by
  decide +kernel

theorem tot6196 : totK PD2M8K2 D2M8K2.t6196 = [171565361099, 457212081908, 250644914560, 14790319751, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6197 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6197 = true := by
  decide +kernel

theorem tot6197 : totK PD2M8K2 D2M8K2.t6197 = [0, 274000603824, 508479119249, 111280848619, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows6198 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6198 = true := by
  decide +kernel

theorem tot6198 : totK PD2M8K2 D2M8K2.t6198 = [100743039162, 380823083988, 386673899899, 53102639884, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6199 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6199 = true := by
  decide +kernel

theorem tot6199 : totK PD2M8K2 D2M8K2.t6199 = [202417634778, 479262505007, 225210799496, 14002694637, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
