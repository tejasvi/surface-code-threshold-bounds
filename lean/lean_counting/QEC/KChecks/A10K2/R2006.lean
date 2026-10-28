import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8024 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8024 = true := by
  decide +kernel

theorem tot8024 : totK PA10K2 A10K2.t8024 = [0, 0, 0, 319295482399, 1099545115493, 1547372980635, 1388185539957, 532119649544, 48886019071, 0] := by
  decide +kernel

theorem rows8025 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8025 = true := by
  decide +kernel

theorem tot8025 : totK PA10K2 A10K2.t8025 = [0, 0, 0, 527679610015, 1921005808014, 1888954101117, 405561640540, 11386979328, 0, 0] := by
  decide +kernel

theorem rows8026 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8026 = true := by
  decide +kernel

theorem tot8026 : totK PA10K2 A10K2.t8026 = [0, 0, 0, 0, 637330501894, 2084808160321, 1720461061740, 351200049995, 13364899180, 0] := by
  decide +kernel

theorem rows8027 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8027 = true := by
  decide +kernel

theorem tot8027 : totK PA10K2 A10K2.t8027 = [0, 0, 0, 287800902345, 1281439740717, 2037312417772, 1084909880919, 125185495722, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
