import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16356 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16356 = true := by
  decide +kernel

theorem tot16356 : totK PD2M8K2 D2M8K2.t16356 = [0, 0, 7930757961, 304837703375, 488426666163, 92347907324, 1164319620, 0] := by
  decide +kernel

theorem rows16357 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16357 = true := by
  decide +kernel

theorem tot16357 : totK PD2M8K2 D2M8K2.t16357 = [0, 0, 0, 224276136124, 480506770526, 158828024256, 7393276268, 0] := by
  decide +kernel

theorem rows16358 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16358 = true := by
  decide +kernel

theorem tot16358 : totK PD2M8K2 D2M8K2.t16358 = [0, 0, 178504761243, 442372872801, 248298907372, 28400856438, 0, 0] := by
  decide +kernel

theorem rows16359 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16359 = true := by
  decide +kernel

theorem tot16359 : totK PD2M8K2 D2M8K2.t16359 = [0, 0, 215672694549, 485653801045, 194244185399, 9317730953, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
