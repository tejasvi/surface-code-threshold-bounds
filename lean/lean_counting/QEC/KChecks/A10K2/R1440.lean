import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5760 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5760 = true := by
  decide +kernel

theorem tot5760 : totK PA10K2 A10K2.t5760 = [0, 0, 294356378534, 1196004113628, 1874844274660, 1143914291616, 177287303861, 5460492893, 0, 0] := by
  decide +kernel

theorem rows5761 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5761 = true := by
  decide +kernel

theorem tot5761 : totK PA10K2 A10K2.t5761 = [0, 0, 450717101824, 1750993182251, 1962627816468, 587208016432, 32846095359, 0, 0, 0] := by
  decide +kernel

theorem rows5762 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5762 = true := by
  decide +kernel

theorem tot5762 : totK PA10K2 A10K2.t5762 = [0, 0, 0, 749553032832, 2065213543549, 1478561034656, 317738394950, 24969229125, 0, 0] := by
  decide +kernel

theorem rows5763 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5763 = true := by
  decide +kernel

theorem tot5763 : totK PA10K2 A10K2.t5763 = [0, 0, 270189285852, 1145310258679, 1874101539220, 1165075254700, 195821153372, 6034215561, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
