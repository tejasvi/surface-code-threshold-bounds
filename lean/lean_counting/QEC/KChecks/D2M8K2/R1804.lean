import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7216 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7216 = true := by
  decide +kernel

theorem tot7216 : totK PD2M8K2 D2M8K2.t7216 = [0, 0, 168882656096, 450804488798, 246088419255, 17061934822, 0, 0] := by
  decide +kernel

theorem rows7217 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7217 = true := by
  decide +kernel

theorem tot7217 : totK PD2M8K2 D2M8K2.t7217 = [0, 0, 0, 239223017450, 503960114864, 136403801251, 3499003824, 0] := by
  decide +kernel

theorem rows7218 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7218 = true := by
  decide +kernel

theorem tot7218 : totK PD2M8K2 D2M8K2.t7218 = [0, 0, 80007408125, 277413158305, 377564529192, 116667271398, 7228027050, 0] := by
  decide +kernel

theorem rows7219 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7219 = true := by
  decide +kernel

theorem tot7219 : totK PD2M8K2 D2M8K2.t7219 = [0, 0, 179773261166, 471188634975, 231030143408, 9997409401, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
