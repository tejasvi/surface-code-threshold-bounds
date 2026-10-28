import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows696 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t696 = true := by
  decide +kernel

theorem tot696 : totK PA10K2 A10K2.t696 = [0, 0, 534549117383, 1810514467113, 1803465650577, 464167647189, 31169761322, 0, 0, 0] := by
  decide +kernel

theorem rows697 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t697 = true := by
  decide +kernel

theorem tot697 : totK PA10K2 A10K2.t697 = [0, 0, 307739496603, 1535656000407, 2064968201126, 711989999612, 48995886185, 0, 0, 0] := by
  decide +kernel

theorem rows698 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t698 = true := by
  decide +kernel

theorem tot698 : totK PA10K2 A10K2.t698 = [0, 0, 213371739588, 1031021095311, 1929376244110, 1210534602587, 233528391130, 6354482628, 0, 0] := by
  decide +kernel

theorem rows699 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t699 = true := by
  decide +kernel

theorem tot699 : totK PA10K2 A10K2.t699 = [0, 0, 447929357241, 1732945069699, 1976912347930, 552344694103, 32040661968, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
