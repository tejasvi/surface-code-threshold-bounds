import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14164 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14164 = true := by
  decide +kernel

theorem tot14164 : totK PD2M8K2 D2M8K2.t14164 = [141309891445, 417855756120, 301423808648, 53732491797, 2498878989, 0, 0, 0] := by
  decide +kernel

theorem rows14165 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14165 = true := by
  decide +kernel

theorem tot14165 : totK PD2M8K2 D2M8K2.t14165 = [175745543068, 449611925041, 262514938774, 21516997609, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14166 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14166 = true := by
  decide +kernel

theorem tot14166 : totK PD2M8K2 D2M8K2.t14166 = [61622140921, 360553466070, 394639315410, 71699795862, 1096156699, 0, 0, 0] := by
  decide +kernel

theorem rows14167 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14167 = true := by
  decide +kernel

theorem tot14167 : totK PD2M8K2 D2M8K2.t14167 = [49694763032, 290288476332, 436868841694, 119698640361, 3880716147, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
