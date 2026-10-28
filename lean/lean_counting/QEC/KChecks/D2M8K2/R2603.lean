import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10412 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10412 = true := by
  decide +kernel

theorem tot10412 : totK PD2M8K2 D2M8K2.t10412 = [0, 0, 139046189236, 372897389932, 319207876459, 73343584828, 2813333534, 0] := by
  decide +kernel

theorem rows10413 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10413 = true := by
  decide +kernel

theorem tot10413 : totK PD2M8K2 D2M8K2.t10413 = [0, 0, 181510327402, 469367699677, 251700342834, 22847913822, 0, 0] := by
  decide +kernel

theorem rows10414 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10414 = true := by
  decide +kernel

theorem tot10414 : totK PD2M8K2 D2M8K2.t10414 = [0, 0, 91991626324, 416239097566, 363992371949, 38917175862, 0, 0] := by
  decide +kernel

theorem rows10415 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10415 = true := by
  decide +kernel

theorem tot10415 : totK PD2M8K2 D2M8K2.t10415 = [0, 0, 0, 299701426638, 484988430483, 120214137133, 3718846349, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
