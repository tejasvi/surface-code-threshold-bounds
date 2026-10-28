import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows216 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t216 = true := by
  decide +kernel

theorem tot216 : totK PD2M8K2 D2M8K2.t216 = [0, 0, 278676792421, 516331242733, 106383488258, 1164319620, 0, 0] := by
  decide +kernel

theorem rows217 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t217 = true := by
  decide +kernel

theorem tot217 : totK PD2M8K2 D2M8K2.t217 = [0, 18419415786, 197821382220, 459974098438, 184963979403, 11885407614, 0, 0] := by
  decide +kernel

theorem rows218 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t218 = true := by
  decide +kernel

theorem tot218 : totK PD2M8K2 D2M8K2.t218 = [0, 179811956495, 455375570328, 238438354695, 20913607421, 0, 0, 0] := by
  decide +kernel

theorem rows219 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t219 = true := by
  decide +kernel

theorem tot219 : totK PD2M8K2 D2M8K2.t219 = [0, 202366464203, 456341374061, 217898398479, 17028109311, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
