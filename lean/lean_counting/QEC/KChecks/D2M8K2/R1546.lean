import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6184 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6184 = true := by
  decide +kernel

theorem tot6184 : totK PD2M8K2 D2M8K2.t6184 = [0, 179909389958, 445428177550, 264709698934, 29110791914, 0, 0, 0] := by
  decide +kernel

theorem rows6185 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6185 = true := by
  decide +kernel

theorem tot6185 : totK PD2M8K2 D2M8K2.t6185 = [0, 102101974263, 427185101042, 341834575665, 36562359091, 0, 0, 0] := by
  decide +kernel

theorem rows6186 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6186 = true := by
  decide +kernel

theorem tot6186 : totK PD2M8K2 D2M8K2.t6186 = [0, 0, 222742020194, 486132877488, 163832364502, 5218872685, 0, 0] := by
  decide +kernel

theorem rows6187 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6187 = true := by
  decide +kernel

theorem tot6187 : totK PD2M8K2 D2M8K2.t6187 = [0, 186432467177, 437260385256, 252639255832, 29785417251, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
