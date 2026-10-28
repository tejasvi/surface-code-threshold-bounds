import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4188 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4188 = true := by
  decide +kernel

theorem tot4188 : totK PD2M8K2 D2M8K2.t4188 = [0, 0, 54508123318, 294614725271, 419028491471, 102866881115, 2516941024, 0] := by
  decide +kernel

theorem rows4189 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4189 = true := by
  decide +kernel

theorem tot4189 : totK PD2M8K2 D2M8K2.t4189 = [0, 0, 186551070353, 462252899552, 243264898711, 20884098803, 0, 0] := by
  decide +kernel

theorem rows4190 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4190 = true := by
  decide +kernel

theorem tot4190 : totK PD2M8K2 D2M8K2.t4190 = [0, 0, 168062828938, 478670908852, 244180905235, 11977135916, 0, 0] := by
  decide +kernel

theorem rows4191 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4191 = true := by
  decide +kernel

theorem tot4191 : totK PD2M8K2 D2M8K2.t4191 = [0, 0, 0, 284349115433, 504223124059, 91918976367, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
