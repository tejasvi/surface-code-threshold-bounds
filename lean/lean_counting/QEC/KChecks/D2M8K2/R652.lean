import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2608 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2608 = true := by
  decide +kernel

theorem tot2608 : totK PD2M8K2 D2M8K2.t2608 = [0, 178176161797, 437847099230, 257672743380, 27917676903, 0, 0, 0] := by
  decide +kernel

theorem rows2609 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2609 = true := by
  decide +kernel

theorem tot2609 : totK PD2M8K2 D2M8K2.t2609 = [0, 196330604190, 478865898852, 207919888344, 11879147749, 0, 0, 0] := by
  decide +kernel

theorem rows2610 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2610 = true := by
  decide +kernel

theorem tot2610 : totK PD2M8K2 D2M8K2.t2610 = [0, 34501533551, 341785359023, 438431561569, 73297514087, 1075657031, 0, 0] := by
  decide +kernel

theorem rows2611 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2611 = true := by
  decide +kernel

theorem tot2611 : totK PD2M8K2 D2M8K2.t2611 = [0, 65172340486, 294246864626, 396682632862, 105201856536, 3804183361, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
