import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5364 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5364 = true := by
  decide +kernel

theorem tot5364 : totK PD2M8K2 D2M8K2.t5364 = [0, 0, 193034192441, 471654938662, 216496682313, 14707859566, 0, 0] := by
  decide +kernel

theorem rows5365 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5365 = true := by
  decide +kernel

theorem tot5365 : totK PD2M8K2 D2M8K2.t5365 = [0, 0, 194536129568, 477055119324, 201126226250, 7984731767, 0, 0] := by
  decide +kernel

theorem rows5366 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5366 = true := by
  decide +kernel

theorem tot5366 : totK PD2M8K2 D2M8K2.t5366 = [0, 0, 102077584784, 388150110545, 334588925377, 53110103140, 1310285577, 0] := by
  decide +kernel

theorem rows5367 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5367 = true := by
  decide +kernel

theorem tot5367 : totK PD2M8K2 D2M8K2.t5367 = [0, 0, 0, 301299179808, 507100877210, 63097217967, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
