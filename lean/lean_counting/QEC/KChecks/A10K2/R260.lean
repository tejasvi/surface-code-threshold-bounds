import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1040 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1040 = true := by
  decide +kernel

theorem tot1040 : totK PA10K2 A10K2.t1040 = [0, 0, 562204777993, 1964577627825, 1813608436606, 479682177795, 46588517567, 0, 0, 0] := by
  decide +kernel

theorem rows1041 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1041 = true := by
  decide +kernel

theorem tot1041 : totK PA10K2 A10K2.t1041 = [0, 0, 129731217399, 901872364339, 2086217111963, 1338517869072, 196072853352, 5982052406, 0, 0] := by
  decide +kernel

theorem rows1042 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1042 = true := by
  decide +kernel

theorem tot1042 : totK PA10K2 A10K2.t1042 = [0, 0, 550837065656, 1943701475348, 1984938341360, 558643722105, 32848078363, 0, 0, 0] := by
  decide +kernel

theorem rows1043 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1043 = true := by
  decide +kernel

theorem tot1043 : totK PA10K2 A10K2.t1043 = [0, 0, 119627100822, 1073514128776, 2343713133919, 1378645951646, 162105019192, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
