import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10012 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10012 = true := by
  decide +kernel

theorem tot10012 : totK PD2M8K2 D2M8K2.t10012 = [0, 0, 175740758571, 476792827696, 239471906292, 13657636408, 0, 0] := by
  decide +kernel

theorem rows10013 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10013 = true := by
  decide +kernel

theorem tot10013 : totK PD2M8K2 D2M8K2.t10013 = [0, 0, 0, 292948649756, 511266215771, 100499159472, 1162515529, 0] := by
  decide +kernel

theorem rows10014 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10014 = true := by
  decide +kernel

theorem tot10014 : totK PD2M8K2 D2M8K2.t10014 = [0, 0, 87240234242, 323852231320, 383957085225, 104212948255, 4030866388, 0] := by
  decide +kernel

theorem rows10015 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10015 = true := by
  decide +kernel

theorem tot10015 : totK PD2M8K2 D2M8K2.t10015 = [0, 0, 170709993493, 460635905436, 261119712999, 20153406995, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
