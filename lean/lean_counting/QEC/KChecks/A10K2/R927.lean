import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3708 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3708 = true := by
  decide +kernel

theorem tot3708 : totK PA10K2 A10K2.t3708 = [0, 579887477939, 1904929462092, 1782766601022, 494096138961, 33273707513, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3709 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3709 = true := by
  decide +kernel

theorem tot3709 : totK PA10K2 A10K2.t3709 = [0, 170110163244, 1129906425666, 2097231844373, 1214802675299, 247153843256, 20340910120, 0, 0, 0] := by
  decide +kernel

theorem rows3710 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3710 = true := by
  decide +kernel

theorem tot3710 : totK PA10K2 A10K2.t3710 = [0, 145729267903, 778005880618, 1831464325591, 1649789194588, 362197728490, 11427838733, 0, 0, 0] := by
  decide +kernel

theorem rows3711 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3711 = true := by
  decide +kernel

theorem tot3711 : totK PA10K2 A10K2.t3711 = [0, 393135362883, 1636157334356, 1962817387800, 673372188013, 52232171148, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
