import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13556 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13556 = true := by
  decide +kernel

theorem tot13556 : totK PD2M8K2 D2M8K2.t13556 = [0, 175953661429, 484930912389, 214695178472, 9653832318, 0, 0, 0] := by
  decide +kernel

theorem rows13557 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13557 = true := by
  decide +kernel

theorem tot13557 : totK PD2M8K2 D2M8K2.t13557 = [0, 150939178717, 452113828543, 253578762763, 17364808128, 0, 0, 0] := by
  decide +kernel

theorem rows13558 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13558 = true := by
  decide +kernel

theorem tot13558 : totK PD2M8K2 D2M8K2.t13558 = [0, 0, 289367772379, 467353654473, 82599390615, 1206465782, 0, 0] := by
  decide +kernel

theorem rows13559 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13559 = true := by
  decide +kernel

theorem tot13559 : totK PD2M8K2 D2M8K2.t13559 = [0, 177501810653, 439063816100, 281703751981, 31004239096, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
