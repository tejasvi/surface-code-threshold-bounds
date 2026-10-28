import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows708 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t708 = true := by
  decide +kernel

theorem tot708 : totK PA10K2 A10K2.t708 = [0, 0, 479165155472, 1709197596521, 1871493606841, 595268807420, 45569422880, 0, 0, 0] := by
  decide +kernel

theorem rows709 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t709 = true := by
  decide +kernel

theorem tot709 : totK PA10K2 A10K2.t709 = [0, 0, 295075171265, 1548155066326, 2112028171947, 733464498754, 59339750188, 0, 0, 0] := by
  decide +kernel

theorem rows710 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t710 = true := by
  decide +kernel

theorem tot710 : totK PA10K2 A10K2.t710 = [0, 0, 268061909688, 1148466621946, 1873232922700, 1180392030118, 220689258505, 6354482628, 0, 0] := by
  decide +kernel

theorem rows711 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t711 = true := by
  decide +kernel

theorem tot711 : totK PA10K2 A10K2.t711 = [0, 0, 464920362815, 1667676100052, 1885401666024, 645843365387, 51699011822, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
