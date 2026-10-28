import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1212 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1212 = true := by
  decide +kernel

theorem tot1212 : totK PD2M8K2 D2M8K2.t1212 = [162641740095, 474352723873, 262954590699, 18345456823, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1213 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1213 = true := by
  decide +kernel

theorem tot1213 : totK PD2M8K2 D2M8K2.t1213 = [0, 167070007785, 445850799755, 261858340895, 25373788367, 0, 0, 0] := by
  decide +kernel

theorem rows1214 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1214 = true := by
  decide +kernel

theorem tot1214 : totK PD2M8K2 D2M8K2.t1214 = [0, 218747937909, 491783647984, 191447089393, 5430665091, 0, 0, 0] := by
  decide +kernel

theorem rows1215 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1215 = true := by
  decide +kernel

theorem tot1215 : totK PD2M8K2 D2M8K2.t1215 = [156454984840, 367972201492, 270362740641, 110695100493, 6804944647, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
