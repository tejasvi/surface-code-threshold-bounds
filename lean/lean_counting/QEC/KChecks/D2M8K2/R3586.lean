import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14344 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14344 = true := by
  decide +kernel

theorem tot14344 : totK PD2M8K2 D2M8K2.t14344 = [0, 195524045221, 467606198589, 194055767067, 7572879337, 0, 0, 0] := by
  decide +kernel

theorem rows14345 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14345 = true := by
  decide +kernel

theorem tot14345 : totK PD2M8K2 D2M8K2.t14345 = [0, 0, 282193866440, 503495768152, 98000152806, 1334361349, 0, 0] := by
  decide +kernel

theorem rows14346 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14346 = true := by
  decide +kernel

theorem tot14346 : totK PD2M8K2 D2M8K2.t14346 = [0, 93254969463, 382448501944, 388974380458, 44146955488, 0, 0, 0] := by
  decide +kernel

theorem rows14347 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14347 = true := by
  decide +kernel

theorem tot14347 : totK PD2M8K2 D2M8K2.t14347 = [0, 157664404846, 445788709500, 284699285299, 22547112966, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
