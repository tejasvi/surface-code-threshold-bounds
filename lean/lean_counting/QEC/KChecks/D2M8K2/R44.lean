import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows176 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t176 = true := by
  decide +kernel

theorem tot176 : totK PD2M8K2 D2M8K2.t176 = [0, 174886359322, 467875319545, 246109734314, 15248594464, 0, 0, 0] := by
  decide +kernel

theorem rows177 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t177 = true := by
  decide +kernel

theorem tot177 : totK PD2M8K2 D2M8K2.t177 = [0, 0, 274687681072, 507672226462, 113453201505, 1369150432, 0, 0] := by
  decide +kernel

theorem rows178 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t178 = true := by
  decide +kernel

theorem tot178 : totK PD2M8K2 D2M8K2.t178 = [0, 87964691079, 410259685927, 372839952930, 40339691702, 0, 0, 0] := by
  decide +kernel

theorem rows179 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t179 = true := by
  decide +kernel

theorem tot179 : totK PD2M8K2 D2M8K2.t179 = [0, 192493972931, 448806261947, 242416614906, 18492996429, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
