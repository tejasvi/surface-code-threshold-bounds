import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16084 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16084 = true := by
  decide +kernel

theorem tot16084 : totK PD2M8K2 D2M8K2.t16084 = [0, 0, 171520112656, 473180019276, 225383536925, 9029799587, 0, 0] := by
  decide +kernel

theorem rows16085 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16085 = true := by
  decide +kernel

theorem tot16085 : totK PD2M8K2 D2M8K2.t16085 = [0, 0, 167179097555, 467421634477, 229118366244, 13097927948, 0, 0] := by
  decide +kernel

theorem rows16086 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16086 = true := by
  decide +kernel

theorem tot16086 : totK PD2M8K2 D2M8K2.t16086 = [0, 0, 221083745034, 481936659447, 170478529699, 5262322419, 0, 0] := by
  decide +kernel

theorem rows16087 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16087 = true := by
  decide +kernel

theorem tot16087 : totK PD2M8K2 D2M8K2.t16087 = [0, 0, 179158891719, 479962063745, 233384336606, 9495229574, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
