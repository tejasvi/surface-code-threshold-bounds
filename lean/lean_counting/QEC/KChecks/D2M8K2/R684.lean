import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2736 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2736 = true := by
  decide +kernel

theorem tot2736 : totK PD2M8K2 D2M8K2.t2736 = [0, 160688136308, 442129677007, 280839862132, 30368503698, 0, 0, 0] := by
  decide +kernel

theorem rows2737 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2737 = true := by
  decide +kernel

theorem tot2737 : totK PD2M8K2 D2M8K2.t2737 = [0, 87660816535, 370439176407, 348374697148, 59464894222, 1164319620, 0, 0] := by
  decide +kernel

theorem rows2738 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2738 = true := by
  decide +kernel

theorem tot2738 : totK PD2M8K2 D2M8K2.t2738 = [0, 0, 246640890984, 488842292291, 155145098873, 8423393484, 0, 0] := by
  decide +kernel

theorem rows2739 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2739 = true := by
  decide +kernel

theorem tot2739 : totK PD2M8K2 D2M8K2.t2739 = [0, 128998824005, 356567396336, 305851366404, 82590333276, 3462014130, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
