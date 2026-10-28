import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11848 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11848 = true := by
  decide +kernel

theorem tot11848 : totK PD2M8K2 D2M8K2.t11848 = [0, 125195970774, 426155146180, 303685393219, 27616542470, 0, 0, 0] := by
  decide +kernel

theorem rows11849 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11849 = true := by
  decide +kernel

theorem tot11849 : totK PD2M8K2 D2M8K2.t11849 = [0, 0, 279010879956, 504765289526, 102277875256, 1369150432, 0, 0] := by
  decide +kernel

theorem rows11850 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11850 = true := by
  decide +kernel

theorem tot11850 : totK PD2M8K2 D2M8K2.t11850 = [0, 180048717498, 429633179754, 278439635094, 34883320125, 0, 0, 0] := by
  decide +kernel

theorem rows11851 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11851 = true := by
  decide +kernel

theorem tot11851 : totK PD2M8K2 D2M8K2.t11851 = [0, 172658362178, 478069963650, 255471660196, 14670519921, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
