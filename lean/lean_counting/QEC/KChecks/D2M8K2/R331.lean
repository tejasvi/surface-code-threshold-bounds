import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1324 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1324 = true := by
  decide +kernel

theorem tot1324 : totK PD2M8K2 D2M8K2.t1324 = [60585930939, 333631143582, 424788648098, 89913870978, 1164319620, 0, 0, 0] := by
  decide +kernel

theorem rows1325 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1325 = true := by
  decide +kernel

theorem tot1325 : totK PD2M8K2 D2M8K2.t1325 = [0, 207231972200, 460798438880, 181654329936, 11856106740, 0, 0, 0] := by
  decide +kernel

theorem rows1326 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1326 = true := by
  decide +kernel

theorem tot1326 : totK PD2M8K2 D2M8K2.t1326 = [171384004273, 446029385281, 264595683143, 34975704365, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1327 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1327 = true := by
  decide +kernel

theorem tot1327 : totK PD2M8K2 D2M8K2.t1327 = [158140493153, 437553745519, 274073768972, 20345785288, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
