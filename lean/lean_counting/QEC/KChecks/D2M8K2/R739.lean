import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2956 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2956 = true := by
  decide +kernel

theorem tot2956 : totK PD2M8K2 D2M8K2.t2956 = [0, 170687054936, 444194679151, 255603449524, 26064789182, 0, 0, 0] := by
  decide +kernel

theorem rows2957 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2957 = true := by
  decide +kernel

theorem tot2957 : totK PD2M8K2 D2M8K2.t2957 = [0, 191512076904, 457857805052, 224670204336, 16450933629, 0, 0, 0] := by
  decide +kernel

theorem rows2958 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2958 = true := by
  decide +kernel

theorem tot2958 : totK PD2M8K2 D2M8K2.t2958 = [0, 57223643531, 349952958869, 409278420138, 69627459483, 1075657031, 0, 0] := by
  decide +kernel

theorem rows2959 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2959 = true := by
  decide +kernel

theorem tot2959 : totK PD2M8K2 D2M8K2.t2959 = [0, 27086647011, 279203254353, 450746015881, 110574438589, 3804183361, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
