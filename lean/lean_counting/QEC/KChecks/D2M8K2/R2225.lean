import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8900 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8900 = true := by
  decide +kernel

theorem tot8900 : totK PD2M8K2 D2M8K2.t8900 = [0, 186526291816, 460331688392, 230755207401, 16772303799, 0, 0, 0] := by
  decide +kernel

theorem rows8901 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8901 = true := by
  decide +kernel

theorem tot8901 : totK PD2M8K2 D2M8K2.t8901 = [0, 37505423682, 379544172825, 435951871989, 47742051713, 0, 0, 0] := by
  decide +kernel

theorem rows8902 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8902 = true := by
  decide +kernel

theorem tot8902 : totK PD2M8K2 D2M8K2.t8902 = [0, 67647452671, 324339096647, 405210717037, 93732534369, 1415142070, 0, 0] := by
  decide +kernel

theorem rows8903 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8903 = true := by
  decide +kernel

theorem tot8903 : totK PD2M8K2 D2M8K2.t8903 = [0, 169116272856, 448409872711, 274549059050, 28064795884, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
