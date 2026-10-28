import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16240 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16240 = true := by
  decide +kernel

theorem tot16240 : totK PD2M8K2 D2M8K2.t16240 = [0, 0, 0, 309672889478, 525262174088, 70309816698, 0, 0] := by
  decide +kernel

theorem rows16241 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16241 = true := by
  decide +kernel

theorem tot16241 : totK PD2M8K2 D2M8K2.t16241 = [0, 0, 177987622975, 454613620818, 256203930064, 24659588562, 0, 0] := by
  decide +kernel

theorem rows16242 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16242 = true := by
  decide +kernel

theorem tot16242 : totK PD2M8K2 D2M8K2.t16242 = [0, 0, 201617193777, 475188284465, 194968713755, 7777975280, 0, 0] := by
  decide +kernel

theorem rows16243 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16243 = true := by
  decide +kernel

theorem tot16243 : totK PD2M8K2 D2M8K2.t16243 = [0, 0, 27202216626, 316726817671, 468283955419, 86860286086, 1164319620, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
