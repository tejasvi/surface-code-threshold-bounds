import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11028 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11028 = true := by
  decide +kernel

theorem tot11028 : totK PD2M8K2 D2M8K2.t11028 = [0, 184550696815, 472475093202, 215234435750, 14703944056, 0, 0, 0] := by
  decide +kernel

theorem rows11029 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11029 = true := by
  decide +kernel

theorem tot11029 : totK PD2M8K2 D2M8K2.t11029 = [0, 205773654425, 471504910342, 196302197878, 9713690252, 0, 0, 0] := by
  decide +kernel

theorem rows11030 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11030 = true := by
  decide +kernel

theorem tot11030 : totK PD2M8K2 D2M8K2.t11030 = [0, 102813076522, 417375330686, 320463037133, 27636676706, 0, 0, 0] := by
  decide +kernel

theorem rows11031 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11031 = true := by
  decide +kernel

theorem tot11031 : totK PD2M8K2 D2M8K2.t11031 = [0, 0, 301968424997, 478425301589, 77996728389, 1239866073, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
