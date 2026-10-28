import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9396 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9396 = true := by
  decide +kernel

theorem tot9396 : totK PD2M8K2 D2M8K2.t9396 = [0, 194753494978, 483094042726, 225413783249, 12523541424, 0, 0, 0] := by
  decide +kernel

theorem rows9397 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9397 = true := by
  decide +kernel

theorem tot9397 : totK PD2M8K2 D2M8K2.t9397 = [0, 26334346697, 312468679522, 461450795664, 94531431012, 1178750802, 0, 0] := by
  decide +kernel

theorem rows9398 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9398 = true := by
  decide +kernel

theorem tot9398 : totK PD2M8K2 D2M8K2.t9398 = [0, 0, 203412120097, 473025702234, 190588483074, 11991925116, 0, 0] := by
  decide +kernel

theorem rows9399 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9399 = true := by
  decide +kernel

theorem tot9399 : totK PD2M8K2 D2M8K2.t9399 = [0, 171650470825, 444901484918, 253930714165, 33684084160, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
