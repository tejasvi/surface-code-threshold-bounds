import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1404 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1404 = true := by
  decide +kernel

theorem tot1404 : totK PD2M8K2 D2M8K2.t1404 = [0, 91193102611, 377273177293, 390941689037, 51160430510, 0, 0, 0] := by
  decide +kernel

theorem rows1405 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1405 = true := by
  decide +kernel

theorem tot1405 : totK PD2M8K2 D2M8K2.t1405 = [0, 190972335815, 455915126373, 249792162737, 18602404635, 0, 0, 0] := by
  decide +kernel

theorem rows1406 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1406 = true := by
  decide +kernel

theorem tot1406 : totK PD2M8K2 D2M8K2.t1406 = [0, 105805967407, 424118461345, 334737226752, 40846647816, 0, 0, 0] := by
  decide +kernel

theorem rows1407 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1407 = true := by
  decide +kernel

theorem tot1407 : totK PD2M8K2 D2M8K2.t1407 = [0, 0, 142985020964, 435658094348, 289766001416, 24691320395, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
