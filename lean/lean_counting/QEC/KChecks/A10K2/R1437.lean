import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5748 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5748 = true := by
  decide +kernel

theorem tot5748 : totK PA10K2 A10K2.t5748 = [0, 0, 0, 765774496554, 2295584740742, 1449757340701, 170342041109, 0, 0, 0] := by
  decide +kernel

theorem rows5749 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5749 = true := by
  decide +kernel

theorem tot5749 : totK PA10K2 A10K2.t5749 = [0, 0, 458520426296, 1672227219151, 1844624935154, 732159803559, 136041279435, 6354482628, 0, 0] := by
  decide +kernel

theorem rows5750 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5750 = true := by
  decide +kernel

theorem tot5750 : totK PA10K2 A10K2.t5750 = [0, 0, 311769148082, 1247583091161, 1909388962946, 1183307965238, 167470952302, 6853348008, 0, 0] := by
  decide +kernel

theorem rows5751 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5751 = true := by
  decide +kernel

theorem tot5751 : totK PA10K2 A10K2.t5751 = [0, 0, 452945970440, 1712518902353, 1990469658670, 594758653395, 32846095359, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
