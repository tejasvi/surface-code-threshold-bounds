import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5052 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5052 = true := by
  decide +kernel

theorem tot5052 : totK PA10K2 A10K2.t5052 = [0, 0, 564410626380, 1991561868912, 1753171585945, 401702943544, 25371180993, 0, 0, 0] := by
  decide +kernel

theorem rows5053 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5053 = true := by
  decide +kernel

theorem tot5053 : totK PA10K2 A10K2.t5053 = [0, 410905957332, 1475971387462, 1839487018935, 906781355715, 164549926075, 5460492893, 0, 0, 0] := by
  decide +kernel

theorem rows5054 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5054 = true := by
  decide +kernel

theorem tot5054 : totK PA10K2 A10K2.t5054 = [0, 131218372369, 1086259797253, 1949256980938, 1231645704940, 293546958448, 25299471099, 0, 0, 0] := by
  decide +kernel

theorem rows5055 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5055 = true := by
  decide +kernel

theorem tot5055 : totK PA10K2 A10K2.t5055 = [0, 277626483571, 1152468005010, 1882663088727, 1218999994447, 196008199664, 6034215561, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
