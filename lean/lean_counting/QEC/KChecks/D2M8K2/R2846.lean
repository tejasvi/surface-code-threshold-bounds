import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11384 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11384 = true := by
  decide +kernel

theorem tot11384 : totK PD2M8K2 D2M8K2.t11384 = [0, 0, 302770244233, 464830278803, 110117204260, 3824247485, 0, 0] := by
  decide +kernel

theorem rows11385 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11385 = true := by
  decide +kernel

theorem tot11385 : totK PD2M8K2 D2M8K2.t11385 = [0, 171428166111, 440867378221, 277012142371, 30468475795, 0, 0, 0] := by
  decide +kernel

theorem rows11386 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11386 = true := by
  decide +kernel

theorem tot11386 : totK PD2M8K2 D2M8K2.t11386 = [0, 189783009197, 469645246786, 224156842812, 12351777281, 0, 0, 0] := by
  decide +kernel

theorem rows11387 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11387 = true := by
  decide +kernel

theorem tot11387 : totK PD2M8K2 D2M8K2.t11387 = [0, 63902374403, 341464441968, 408839450701, 85931292789, 1242138600, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
