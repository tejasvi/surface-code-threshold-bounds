import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7396 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7396 = true := by
  decide +kernel

theorem tot7396 : totK PD2M8K2 D2M8K2.t7396 = [0, 0, 184051156748, 455285850744, 262460721911, 26012142351, 0, 0] := by
  decide +kernel

theorem rows7397 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7397 = true := by
  decide +kernel

theorem tot7397 : totK PD2M8K2 D2M8K2.t7397 = [0, 0, 202167928717, 488684978520, 207103042105, 9474029161, 0, 0] := by
  decide +kernel

theorem rows7398 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7398 = true := by
  decide +kernel

theorem tot7398 : totK PD2M8K2 D2M8K2.t7398 = [0, 0, 160824170644, 461683440609, 262920313487, 21756182385, 0, 0] := by
  decide +kernel

theorem rows7399 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7399 = true := by
  decide +kernel

theorem tot7399 : totK PD2M8K2 D2M8K2.t7399 = [0, 0, 177755252870, 451421314043, 251264461301, 17767297607, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
