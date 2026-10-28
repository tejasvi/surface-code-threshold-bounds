import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12524 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12524 = true := by
  decide +kernel

theorem tot12524 : totK PD2M8K2 D2M8K2.t12524 = [0, 0, 170290302882, 479835502923, 238176590542, 13753654941, 0, 0] := by
  decide +kernel

theorem rows12525 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12525 = true := by
  decide +kernel

theorem tot12525 : totK PD2M8K2 D2M8K2.t12525 = [0, 0, 196521717745, 472334732595, 214673297309, 12183533023, 0, 0] := by
  decide +kernel

theorem rows12526 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12526 = true := by
  decide +kernel

theorem tot12526 : totK PD2M8K2 D2M8K2.t12526 = [0, 0, 68542036366, 342521151657, 373510425341, 77625327672, 1162935789, 0] := by
  decide +kernel

theorem rows12527 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12527 = true := by
  decide +kernel

theorem tot12527 : totK PD2M8K2 D2M8K2.t12527 = [0, 0, 0, 209374196293, 447551584906, 173896024523, 11853261585, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
