import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10328 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10328 = true := by
  decide +kernel

theorem tot10328 : totK PD2M8K2 D2M8K2.t10328 = [0, 0, 160278744452, 469799876318, 250973111337, 13597322258, 0, 0] := by
  decide +kernel

theorem rows10329 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10329 = true := by
  decide +kernel

theorem tot10329 : totK PD2M8K2 D2M8K2.t10329 = [0, 0, 173491865919, 463773979916, 242387177699, 15069002009, 0, 0] := by
  decide +kernel

theorem rows10330 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10330 = true := by
  decide +kernel

theorem tot10330 : totK PD2M8K2 D2M8K2.t10330 = [0, 0, 187249775258, 470030703406, 209807723942, 11980462845, 0, 0] := by
  decide +kernel

theorem rows10331 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10331 = true := by
  decide +kernel

theorem tot10331 : totK PD2M8K2 D2M8K2.t10331 = [0, 0, 70684353322, 354639903331, 370897566657, 66385332008, 1095107716, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
