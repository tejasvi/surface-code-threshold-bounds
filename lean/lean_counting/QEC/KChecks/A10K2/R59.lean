import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows236 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t236 = true := by
  decide +kernel

theorem tot236 : totK PA10K2 A10K2.t236 = [0, 0, 556245062404, 2069120417006, 2036799530736, 448379308670, 20094979411, 0, 0, 0] := by
  decide +kernel

theorem rows237 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t237 = true := by
  decide +kernel

theorem tot237 : totK PA10K2 A10K2.t237 = [0, 412976510926, 1341068214483, 1569318880132, 1108900620758, 483606663537, 41737205306, 0, 0, 0] := by
  decide +kernel

theorem rows238 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t238 = true := by
  decide +kernel

theorem tot238 : totK PA10K2 A10K2.t238 = [0, 387399747517, 1694782504978, 2090960607374, 689683839503, 46953201059, 0, 0, 0, 0] := by
  decide +kernel

theorem rows239 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t239 = true := by
  decide +kernel

theorem tot239 : totK PA10K2 A10K2.t239 = [0, 0, 464914593420, 1859289827054, 1897060137801, 443798135444, 25371180993, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
