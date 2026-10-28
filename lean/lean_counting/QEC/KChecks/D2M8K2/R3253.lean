import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13012 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13012 = true := by
  decide +kernel

theorem tot13012 : totK PD2M8K2 D2M8K2.t13012 = [0, 0, 92859452576, 418718106768, 342677428640, 37360339045, 0, 0] := by
  decide +kernel

theorem rows13013 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13013 = true := by
  decide +kernel

theorem tot13013 : totK PD2M8K2 D2M8K2.t13013 = [0, 0, 167702888163, 450737778547, 263292016319, 21845004954, 0, 0] := by
  decide +kernel

theorem rows13014 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13014 = true := by
  decide +kernel

theorem tot13014 : totK PD2M8K2 D2M8K2.t13014 = [0, 0, 200746556025, 492159064704, 207458062718, 8031378390, 0, 0] := by
  decide +kernel

theorem rows13015 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13015 = true := by
  decide +kernel

theorem tot13015 : totK PD2M8K2 D2M8K2.t13015 = [0, 0, 202683200899, 476317431535, 215107839067, 11051716772, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
