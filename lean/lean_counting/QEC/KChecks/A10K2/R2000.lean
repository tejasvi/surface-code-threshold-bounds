import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8000 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8000 = true := by
  decide +kernel

theorem tot8000 : totK PA10K2 A10K2.t8000 = [0, 0, 0, 486924098881, 1862974788590, 2050010303315, 562425699602, 31582106180, 0, 0] := by
  decide +kernel

theorem rows8001 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8001 = true := by
  decide +kernel

theorem tot8001 : totK PA10K2 A10K2.t8001 = [0, 0, 303501126640, 1027231327011, 1528144945276, 1501603007574, 588990168233, 50491866487, 0, 0] := by
  decide +kernel

theorem rows8002 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8002 = true := by
  decide +kernel

theorem tot8002 : totK PA10K2 A10K2.t8002 = [0, 0, 456053228344, 1813759617247, 2030183183799, 534342292236, 32040661968, 0, 0, 0] := by
  decide +kernel

theorem rows8003 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8003 = true := by
  decide +kernel

theorem tot8003 : totK PA10K2 A10K2.t8003 = [0, 0, 0, 723239032095, 2110811126412, 1670505297480, 390261413614, 25371180993, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
