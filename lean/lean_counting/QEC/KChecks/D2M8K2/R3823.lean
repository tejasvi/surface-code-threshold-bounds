import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15292 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15292 = true := by
  decide +kernel

theorem tot15292 : totK PD2M8K2 D2M8K2.t15292 = [0, 0, 175332985657, 452998514046, 269762266063, 17810241492, 0, 0] := by
  decide +kernel

theorem rows15293 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15293 = true := by
  decide +kernel

theorem tot15293 : totK PD2M8K2 D2M8K2.t15293 = [0, 0, 74287995194, 336890787834, 401408098144, 84680108909, 1232609433, 0] := by
  decide +kernel

theorem rows15294 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15294 = true := by
  decide +kernel

theorem tot15294 : totK PD2M8K2 D2M8K2.t15294 = [0, 0, 0, 275931237243, 503385887272, 120514665773, 3724448267, 0] := by
  decide +kernel

theorem rows15295 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15295 = true := by
  decide +kernel

theorem tot15295 : totK PD2M8K2 D2M8K2.t15295 = [0, 0, 175465715302, 386276229500, 229425140475, 94526564165, 8757608180, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
