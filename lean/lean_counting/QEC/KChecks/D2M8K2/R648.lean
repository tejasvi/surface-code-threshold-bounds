import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2592 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2592 = true := by
  decide +kernel

theorem tot2592 : totK PD2M8K2 D2M8K2.t2592 = [53275168027, 326408497084, 432766520895, 88679902299, 1164319620, 0, 0, 0] := by
  decide +kernel

theorem rows2593 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2593 = true := by
  decide +kernel

theorem tot2593 : totK PD2M8K2 D2M8K2.t2593 = [0, 209490016333, 473696942072, 185505082826, 11740097756, 0, 0, 0] := by
  decide +kernel

theorem rows2594 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2594 = true := by
  decide +kernel

theorem tot2594 : totK PD2M8K2 D2M8K2.t2594 = [165497800747, 443965629690, 273400268285, 34000387433, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2595 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2595 = true := by
  decide +kernel

theorem tot2595 : totK PD2M8K2 D2M8K2.t2595 = [172777712065, 449313476804, 257641799645, 18129863194, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
