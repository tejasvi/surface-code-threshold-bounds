import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12900 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12900 = true := by
  decide +kernel

theorem tot12900 : totK PD2M8K2 D2M8K2.t12900 = [0, 0, 301807411433, 515379644115, 88473381297, 0, 0, 0] := by
  decide +kernel

theorem rows12901 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12901 = true := by
  decide +kernel

theorem tot12901 : totK PD2M8K2 D2M8K2.t12901 = [0, 141545560730, 377407403313, 286547619303, 87245481679, 3884009855, 0, 0] := by
  decide +kernel

theorem rows12902 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12902 = true := by
  decide +kernel

theorem tot12902 : totK PD2M8K2 D2M8K2.t12902 = [0, 204716269077, 449400135564, 222498340066, 17127447079, 0, 0, 0] := by
  decide +kernel

theorem rows12903 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12903 = true := by
  decide +kernel

theorem tot12903 : totK PD2M8K2 D2M8K2.t12903 = [0, 36455305428, 312824016592, 437304767866, 102735538088, 1268739303, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
