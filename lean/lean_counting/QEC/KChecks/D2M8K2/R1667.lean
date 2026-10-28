import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6668 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6668 = true := by
  decide +kernel

theorem tot6668 : totK PD2M8K2 D2M8K2.t6668 = [0, 0, 294780466108, 507135080186, 103524192039, 1164319620, 0, 0] := by
  decide +kernel

theorem rows6669 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6669 = true := by
  decide +kernel

theorem tot6669 : totK PD2M8K2 D2M8K2.t6669 = [0, 0, 206310775086, 474526385429, 185519997969, 11885407614, 0, 0] := by
  decide +kernel

theorem rows6670 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6670 = true := by
  decide +kernel

theorem tot6670 : totK PD2M8K2 D2M8K2.t6670 = [0, 175328763981, 440232227909, 259505730772, 28036957438, 0, 0, 0] := by
  decide +kernel

theorem rows6671 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6671 = true := by
  decide +kernel

theorem tot6671 : totK PD2M8K2 D2M8K2.t6671 = [0, 192255006586, 460647993247, 227884264555, 16988685346, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
