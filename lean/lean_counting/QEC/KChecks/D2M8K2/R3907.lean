import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15628 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15628 = true := by
  decide +kernel

theorem tot15628 : totK PD2M8K2 D2M8K2.t15628 = [0, 0, 92486169098, 424650335034, 339470154484, 32023049186, 0, 0] := by
  decide +kernel

theorem rows15629 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15629 = true := by
  decide +kernel

theorem tot15629 : totK PD2M8K2 D2M8K2.t15629 = [0, 0, 156934563163, 441713453014, 282057830686, 23226348832, 0, 0] := by
  decide +kernel

theorem rows15630 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15630 = true := by
  decide +kernel

theorem tot15630 : totK PD2M8K2 D2M8K2.t15630 = [0, 0, 206242344259, 484576055415, 209269149626, 9766274741, 0, 0] := by
  decide +kernel

theorem rows15631 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15631 = true := by
  decide +kernel

theorem tot15631 : totK PD2M8K2 D2M8K2.t15631 = [0, 0, 199616123465, 482549613079, 210585538482, 11051716772, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
