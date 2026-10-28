import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9744 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9744 = true := by
  decide +kernel

theorem tot9744 : totK PD2M8K2 D2M8K2.t9744 = [0, 0, 245176748786, 489152167085, 153274054358, 4764360615, 0, 0] := by
  decide +kernel

theorem rows9745 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9745 = true := by
  decide +kernel

theorem tot9745 : totK PD2M8K2 D2M8K2.t9745 = [0, 0, 183418471542, 466963165011, 224735736195, 17385499678, 0, 0] := by
  decide +kernel

theorem rows9746 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9746 = true := by
  decide +kernel

theorem tot9746 : totK PD2M8K2 D2M8K2.t9746 = [0, 0, 167076456177, 471865037359, 210059389815, 7871360470, 0, 0] := by
  decide +kernel

theorem rows9747 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9747 = true := by
  decide +kernel

theorem tot9747 : totK PD2M8K2 D2M8K2.t9747 = [0, 0, 148080945397, 437564049538, 263252441601, 21563280948, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
