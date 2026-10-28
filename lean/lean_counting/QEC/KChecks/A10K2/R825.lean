import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3300 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3300 = true := by
  decide +kernel

theorem tot3300 : totK PA10K2 A10K2.t3300 = [0, 0, 293526267267, 1491933473899, 2110782530979, 765213224299, 44689285346, 0, 0, 0] := by
  decide +kernel

theorem rows3301 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3301 = true := by
  decide +kernel

theorem tot3301 : totK PA10K2 A10K2.t3301 = [0, 0, 188973729878, 976114526543, 1963358206496, 1346109463785, 220070221064, 6354482628, 0, 0] := by
  decide +kernel

theorem rows3302 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3302 = true := by
  decide +kernel

theorem tot3302 : totK PA10K2 A10K2.t3302 = [0, 0, 403309960161, 1722570066731, 2180417446187, 744835169455, 36732467334, 0, 0, 0] := by
  decide +kernel

theorem rows3303 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3303 = true := by
  decide +kernel

theorem tot3303 : totK PA10K2 A10K2.t3303 = [0, 0, 104588151703, 854743829818, 2100154248874, 1653732336265, 295901665239, 6962742351, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
