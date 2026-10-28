import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4820 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4820 = true := by
  decide +kernel

theorem tot4820 : totK PD2M8K2 D2M8K2.t4820 = [0, 0, 198827834663, 479855868957, 224502018083, 11465142734, 0, 0] := by
  decide +kernel

theorem rows4821 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4821 = true := by
  decide +kernel

theorem tot4821 : totK PD2M8K2 D2M8K2.t4821 = [0, 0, 8130385210, 311748293052, 471860679046, 95438095886, 1242138600, 0] := by
  decide +kernel

theorem rows4822 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4822 = true := by
  decide +kernel

theorem tot4822 : totK PD2M8K2 D2M8K2.t4822 = [0, 0, 0, 223261815444, 484565494271, 155624456171, 4948628341, 0] := by
  decide +kernel

theorem rows4823 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4823 = true := by
  decide +kernel

theorem tot4823 : totK PD2M8K2 D2M8K2.t4823 = [0, 0, 161913507163, 368324804453, 233186130283, 114109541381, 11893557120, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
