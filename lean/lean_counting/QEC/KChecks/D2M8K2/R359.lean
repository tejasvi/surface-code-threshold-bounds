import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1436 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1436 = true := by
  decide +kernel

theorem tot1436 : totK PD2M8K2 D2M8K2.t1436 = [0, 72365903168, 359518938316, 428635831733, 52155083805, 0, 0, 0] := by
  decide +kernel

theorem rows1437 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1437 = true := by
  decide +kernel

theorem tot1437 : totK PD2M8K2 D2M8K2.t1437 = [0, 162336109749, 455505967892, 279959982299, 27402819764, 0, 0, 0] := by
  decide +kernel

theorem rows1438 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1438 = true := by
  decide +kernel

theorem tot1438 : totK PD2M8K2 D2M8K2.t1438 = [0, 153370728324, 456423782622, 271798055707, 23484641922, 0, 0, 0] := by
  decide +kernel

theorem rows1439 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1439 = true := by
  decide +kernel

theorem tot1439 : totK PD2M8K2 D2M8K2.t1439 = [0, 0, 191656491786, 449059419250, 241431924142, 20729740161, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
