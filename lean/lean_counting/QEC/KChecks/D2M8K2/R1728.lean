import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6912 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6912 = true := by
  decide +kernel

theorem tot6912 : totK PD2M8K2 D2M8K2.t6912 = [0, 200802750902, 485702807720, 195476237777, 9780024374, 0, 0, 0] := by
  decide +kernel

theorem rows6913 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6913 = true := by
  decide +kernel

theorem tot6913 : totK PD2M8K2 D2M8K2.t6913 = [0, 103934187288, 412050497008, 320977591339, 34837684693, 0, 0, 0] := by
  decide +kernel

theorem rows6914 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6914 = true := by
  decide +kernel

theorem tot6914 : totK PD2M8K2 D2M8K2.t6914 = [0, 65579953647, 322164422649, 426222584297, 73064389363, 1096505104, 0, 0] := by
  decide +kernel

theorem rows6915 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6915 = true := by
  decide +kernel

theorem tot6915 : totK PD2M8K2 D2M8K2.t6915 = [0, 182310174810, 468497252195, 237872742359, 20228466982, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
