import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9060 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9060 = true := by
  decide +kernel

theorem tot9060 : totK PD2M8K2 D2M8K2.t9060 = [0, 139046189236, 366359477401, 303553215855, 90078992787, 3880716147, 0, 0] := by
  decide +kernel

theorem rows9061 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9061 = true := by
  decide +kernel

theorem tot9061 : totK PD2M8K2 D2M8K2.t9061 = [0, 178195040534, 441024893975, 266796407179, 28343493663, 0, 0, 0] := by
  decide +kernel

theorem rows9062 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9062 = true := by
  decide +kernel

theorem tot9062 : totK PD2M8K2 D2M8K2.t9062 = [0, 92353366773, 411903997613, 356312258592, 40946782878, 0, 0, 0] := by
  decide +kernel

theorem rows9063 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9063 = true := by
  decide +kernel

theorem tot9063 : totK PD2M8K2 D2M8K2.t9063 = [0, 0, 240190066696, 497042583397, 153199117097, 2516391818, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
