import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15008 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15008 = true := by
  decide +kernel

theorem tot15008 : totK PD2M8K2 D2M8K2.t15008 = [0, 163502321088, 439935304087, 272614869971, 32832494543, 0, 0, 0] := by
  decide +kernel

theorem rows15009 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15009 = true := by
  decide +kernel

theorem tot15009 : totK PD2M8K2 D2M8K2.t15009 = [0, 160003380572, 459488485044, 268018513976, 16756946085, 0, 0, 0] := by
  decide +kernel

theorem rows15010 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15010 = true := by
  decide +kernel

theorem tot15010 : totK PD2M8K2 D2M8K2.t15010 = [0, 0, 278977190057, 509005962568, 95562939455, 1096505104, 0, 0] := by
  decide +kernel

theorem rows15011 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15011 = true := by
  decide +kernel

theorem tot15011 : totK PD2M8K2 D2M8K2.t15011 = [0, 173511939259, 410017296055, 240063047882, 63494774537, 3821179711, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
