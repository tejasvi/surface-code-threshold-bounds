import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1588 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1588 = true := by
  decide +kernel

theorem tot1588 : totK PD2M8K2 D2M8K2.t1588 = [0, 206238303562, 474404422489, 221600415785, 14468159576, 0, 0, 0] := by
  decide +kernel

theorem rows1589 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1589 = true := by
  decide +kernel

theorem tot1589 : totK PD2M8K2 D2M8K2.t1589 = [0, 8130385210, 298122115569, 471337920388, 107445420075, 1268739303, 0, 0] := by
  decide +kernel

theorem rows1590 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1590 = true := by
  decide +kernel

theorem tot1590 : totK PD2M8K2 D2M8K2.t1590 = [0, 0, 211812459828, 483482108834, 181627272756, 7439274334, 0, 0] := by
  decide +kernel

theorem rows1591 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1591 = true := by
  decide +kernel

theorem tot1591 : totK PD2M8K2 D2M8K2.t1591 = [0, 0, 180833661302, 473233705140, 216598906110, 14703944056, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
