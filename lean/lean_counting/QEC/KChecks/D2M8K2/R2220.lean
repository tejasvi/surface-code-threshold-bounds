import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8880 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8880 = true := by
  decide +kernel

theorem tot8880 : totK PD2M8K2 D2M8K2.t8880 = [191860371588, 460404037613, 230722190417, 16860239812, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8881 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8881 = true := by
  decide +kernel

theorem tot8881 : totK PD2M8K2 D2M8K2.t8881 = [22237551438, 335941562172, 445295719873, 87471322899, 1096156699, 0, 0, 0] := by
  decide +kernel

theorem rows8882 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8882 = true := by
  decide +kernel

theorem tot8882 : totK PD2M8K2 D2M8K2.t8882 = [56271710756, 286910851846, 434001766112, 115704939966, 3880716147, 0, 0, 0] := by
  decide +kernel

theorem rows8883 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8883 = true := by
  decide +kernel

theorem tot8883 : totK PD2M8K2 D2M8K2.t8883 = [181096052132, 465728939296, 256644709107, 23350937170, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
