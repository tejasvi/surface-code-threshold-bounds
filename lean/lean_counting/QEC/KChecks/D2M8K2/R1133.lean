import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4532 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4532 = true := by
  decide +kernel

theorem tot4532 : totK PD2M8K2 D2M8K2.t4532 = [0, 0, 107565863211, 439873573433, 337284606865, 28903710965, 0, 0] := by
  decide +kernel

theorem rows4533 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4533 = true := by
  decide +kernel

theorem tot4533 : totK PD2M8K2 D2M8K2.t4533 = [0, 0, 72625937434, 320402293098, 412419129117, 89832996853, 1444560764, 0] := by
  decide +kernel

theorem rows4534 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4534 = true := by
  decide +kernel

theorem tot4534 : totK PD2M8K2 D2M8K2.t4534 = [0, 0, 189161049733, 464089713764, 245863332142, 20104258212, 0, 0] := by
  decide +kernel

theorem rows4535 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4535 = true := by
  decide +kernel

theorem tot4535 : totK PD2M8K2 D2M8K2.t4535 = [0, 0, 176907299225, 477315116494, 241828021669, 11437485927, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
