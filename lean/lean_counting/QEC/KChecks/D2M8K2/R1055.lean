import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4220 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4220 = true := by
  decide +kernel

theorem tot4220 : totK PD2M8K2 D2M8K2.t4220 = [0, 0, 0, 88555651143, 400818755889, 373562187216, 58115384001, 0] := by
  decide +kernel

theorem rows4221 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4221 = true := by
  decide +kernel

theorem tot4221 : totK PD2M8K2 D2M8K2.t4221 = [0, 0, 0, 0, 172873796807, 446245462000, 245563712790, 21565429856] := by
  decide +kernel

theorem rows4222 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4222 = true := by
  decide +kernel

theorem tot4222 : totK PD2M8K2 D2M8K2.t4222 = [0, 0, 0, 0, 172871062976, 476884856519, 220983850053, 7473384741] := by
  decide +kernel

theorem rows4223 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4223 = true := by
  decide +kernel

theorem tot4223 : totK PD2M8K2 D2M8K2.t4223 = [0, 0, 0, 206253610334, 442166942280, 217258524442, 36658538947, 4256931014] := by
  decide +kernel

end QECKChecks.D2M8K2
