import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14196 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14196 = true := by
  decide +kernel

theorem tot14196 : totK PD2M8K2 D2M8K2.t14196 = [163805274024, 469193403614, 248319286494, 14992323340, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14197 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14197 = true := by
  decide +kernel

theorem tot14197 : totK PD2M8K2 D2M8K2.t14197 = [87940474155, 353562552011, 358498999619, 98238214941, 13135812311, 0, 0, 0] := by
  decide +kernel

theorem rows14198 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14198 = true := by
  decide +kernel

theorem tot14198 : totK PD2M8K2 D2M8K2.t14198 = [0, 160709442784, 453522925258, 263770523730, 16069061757, 0, 0, 0] := by
  decide +kernel

theorem rows14199 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14199 = true := by
  decide +kernel

theorem tot14199 : totK PD2M8K2 D2M8K2.t14199 = [37176659836, 214711599315, 435436672656, 196251857014, 8186970494, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
