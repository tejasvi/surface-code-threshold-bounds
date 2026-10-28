import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1496 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1496 = true := by
  decide +kernel

theorem tot1496 : totK PD2M8K2 D2M8K2.t1496 = [0, 0, 193245219977, 453475237582, 227995558680, 16629160294, 0, 0] := by
  decide +kernel

theorem rows1497 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1497 = true := by
  decide +kernel

theorem tot1497 : totK PD2M8K2 D2M8K2.t1497 = [0, 0, 103128191985, 395606462868, 318038788745, 46909606953, 1086231185, 0] := by
  decide +kernel

theorem rows1498 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1498 = true := by
  decide +kernel

theorem tot1498 : totK PD2M8K2 D2M8K2.t1498 = [0, 0, 0, 275411170206, 450599467358, 112590646823, 3752012233, 0] := by
  decide +kernel

theorem rows1499 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1499 = true := by
  decide +kernel

theorem tot1499 : totK PD2M8K2 D2M8K2.t1499 = [0, 0, 174703029157, 461349028146, 250602617800, 23570995583, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
