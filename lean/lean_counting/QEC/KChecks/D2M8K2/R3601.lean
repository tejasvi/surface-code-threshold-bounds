import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14404 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14404 = true := by
  decide +kernel

theorem tot14404 : totK PD2M8K2 D2M8K2.t14404 = [0, 0, 0, 317097307698, 450337362141, 79337313761, 1035247001, 0] := by
  decide +kernel

theorem rows14405 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14405 = true := by
  decide +kernel

theorem tot14405 : totK PD2M8K2 D2M8K2.t14405 = [0, 175895516967, 436948247500, 194729070367, 47285120864, 27529764623, 2682886096, 0] := by
  decide +kernel

theorem rows14406 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14406 = true := by
  decide +kernel

theorem tot14406 : totK PD2M8K2 D2M8K2.t14406 = [0, 211992949354, 472608042363, 191754848397, 7941653742, 0, 0, 0] := by
  decide +kernel

theorem rows14407 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14407 = true := by
  decide +kernel

theorem tot14407 : totK PD2M8K2 D2M8K2.t14407 = [0, 19497166104, 298960236573, 470443408213, 99593115672, 1369150432, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
