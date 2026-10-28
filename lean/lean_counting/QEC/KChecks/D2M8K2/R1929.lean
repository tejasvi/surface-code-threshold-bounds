import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7716 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7716 = true := by
  decide +kernel

theorem tot7716 : totK PD2M8K2 D2M8K2.t7716 = [0, 0, 0, 211001872409, 469021859416, 194427760194, 12488965933, 0] := by
  decide +kernel

theorem rows7717 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7717 = true := by
  decide +kernel

theorem tot7717 : totK PD2M8K2 D2M8K2.t7717 = [0, 0, 0, 195974455537, 479742795971, 194871670022, 9840992866, 0] := by
  decide +kernel

theorem rows7718 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7718 = true := by
  decide +kernel

theorem tot7718 : totK PD2M8K2 D2M8K2.t7718 = [0, 0, 0, 194873458169, 473582647344, 169957773438, 6050748506, 0] := by
  decide +kernel

theorem rows7719 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7719 = true := by
  decide +kernel

theorem tot7719 : totK PD2M8K2 D2M8K2.t7719 = [0, 0, 0, 0, 300844709913, 446632749131, 84886035434, 1206465782] := by
  decide +kernel

end QECKChecks.D2M8K2
