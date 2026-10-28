import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1552 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1552 = true := by
  decide +kernel

theorem tot1552 : totK PD2M8K2 D2M8K2.t1552 = [0, 165051808623, 396766694686, 254791935176, 71965112457, 3884009855, 0, 0] := by
  decide +kernel

theorem rows1553 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1553 = true := by
  decide +kernel

theorem tot1553 : totK PD2M8K2 D2M8K2.t1553 = [0, 183207317060, 456396025236, 250674323015, 20192862351, 0, 0, 0] := by
  decide +kernel

theorem rows1554 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1554 = true := by
  decide +kernel

theorem tot1554 : totK PD2M8K2 D2M8K2.t1554 = [0, 66402094079, 325252483376, 406629285329, 93104565020, 1268739303, 0, 0] := by
  decide +kernel

theorem rows1555 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1555 = true := by
  decide +kernel

theorem tot1555 : totK PD2M8K2 D2M8K2.t1555 = [0, 0, 216743149206, 478705297924, 177475585505, 7439461435, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
