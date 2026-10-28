import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7288 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7288 = true := by
  decide +kernel

theorem tot7288 : totK PD2M8K2 D2M8K2.t7288 = [0, 0, 194071945847, 472788460501, 201334465029, 24064328939, 2814597007, 0] := by
  decide +kernel

theorem rows7289 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7289 = true := by
  decide +kernel

theorem tot7289 : totK PD2M8K2 D2M8K2.t7289 = [0, 0, 202358225511, 457215509259, 198023462947, 9177721283, 0, 0] := by
  decide +kernel

theorem rows7290 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7290 = true := by
  decide +kernel

theorem tot7290 : totK PD2M8K2 D2M8K2.t7290 = [0, 0, 19497166104, 300862014085, 471342098683, 101808954948, 1369150432, 0] := by
  decide +kernel

theorem rows7291 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7291 = true := by
  decide +kernel

theorem tot7291 : totK PD2M8K2 D2M8K2.t7291 = [0, 0, 89257852685, 395170118931, 387625543575, 38143482161, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
